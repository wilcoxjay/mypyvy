
from typing import BinaryIO, ByteString, Callable, Collection, Iterable, List, Optional, Tuple, Union, Any, Awaitable, TypeVar
import signal
import struct
import asyncio
import os
import pickle
import socket
import sys
import io
import gc
import array


async def _read_exactly(read_fd: int, size: int) -> bytes:
    if size == 0: return bytes()
    try:
        initial_read = os.read(read_fd, size)
        if len(initial_read) == 0:
            raise EOFError()
    except BlockingIOError:
        initial_read = bytes()
    if len(initial_read) == size:
        return initial_read
    buf = bytearray(initial_read)
    loop = asyncio.get_event_loop()
    event = asyncio.Event(loop=loop)
    try:
        loop.add_reader(read_fd, event.set)
        while len(buf) < size:
            await event.wait()
            event.clear()
            try:
                more = os.read(read_fd, size - len(buf))
                if len(more) == 0:
                    raise EOFError()
                buf += more
            except BlockingIOError:
                pass
        return bytes(buf)
    finally:
        loop.remove_reader(read_fd)

async def _write_exactly(write_fd: int, buf: ByteString) -> None:
    if len(buf) == 0: return
    try:
        # Note: type: ignore needed due to incorrect signature of os.write; it actually accepts any bytes-like
        written = os.write(write_fd, buf) # type: ignore
    except BlockingIOError:
        written = 0
    except BrokenPipeError:
        raise EOFError()
    # print(f"Wrote {written} bytes")
    if written == len(buf):
        return
    loop = asyncio.get_event_loop()
    event = asyncio.Event(loop=loop)
    try:
        loop.add_writer(write_fd, event.set)
        while written < len(buf):
            # print("Awaiting to write")
            await event.wait()
            event.clear()
            try:
                w = os.write(write_fd, buf[written:]) # type: ignore
                written += w
            except BlockingIOError:
                pass
            except BrokenPipeError:
                raise EOFError()
        return
    finally:
        loop.remove_writer(write_fd)

# Class to wrap file descriptors for pickling between processes
class FileDescriptor:
    def __init__(self, id: int):
        self.id = id

class AsyncConnection:
    '''A bidirectional pipe like `multiprocessing.Connection`, but `send` and `recv` are coroutines.'''
    HEADER_FMT = '<Q'
    HEADER_SIZE = struct.calcsize(HEADER_FMT)
    BLANK_HEADER = struct.pack(HEADER_FMT, 0)
    def __init__(self, read: int, write: int) -> None:
        self._read_fd = read
        os.set_blocking(read, False)
        self._write_fd = write
        os.set_blocking(write, False)

    async def recv(self) -> Any:
        header = await _read_exactly(self._read_fd, AsyncConnection.HEADER_SIZE)
        data = await _read_exactly(self._read_fd, struct.unpack(AsyncConnection.HEADER_FMT, header)[0])
        return pickle.loads(data)

    async def send(self, v: Any) -> None:
        # pickled = pickle.dumps(v, protocol=pickle.HIGHEST_PROTOCOL)
        # pickled = struct.pack(AsyncConnection.HEADER_FMT, len(pickled)) + pickled
        # await _write_exactly(self._write_fd, pickled)

        stream = io.BytesIO()
        stream.write(AsyncConnection.BLANK_HEADER)
        pickle.dump(v, stream, protocol=pickle.HIGHEST_PROTOCOL)
        size = stream.tell() - AsyncConnection.HEADER_SIZE
        mem_view = stream.getbuffer()
        struct.pack_into(AsyncConnection.HEADER_FMT, mem_view, 0, size)
        await _write_exactly(self._write_fd, mem_view)

    # Support pickling
    def __getstate__(self) -> Tuple[FileDescriptor, FileDescriptor]:
        return (FileDescriptor(self._read_fd), FileDescriptor(self._write_fd))
    def __setstate__(self, t: Tuple[FileDescriptor, FileDescriptor]) -> None:
        self._read_fd = t[0].id
        self._write_fd = t[1].id
        os.set_blocking(self._read_fd, False)
        os.set_blocking(self._write_fd, False)

    def close(self) -> None:
        os.close(self._read_fd)
        os.close(self._write_fd)

    @staticmethod
    def pipe_pair() -> Tuple['AsyncConnection', 'AsyncConnection']:
        (dn_r, dn_w) = os.pipe() # Down pipe (written on top, read on bottom)
        (up_r, up_w) = os.pipe() # Up pipe (written on bottom, read on top)
        return (AsyncConnection(up_r, dn_w), AsyncConnection(dn_r, up_w))


class _ForkPickler(pickle.Pickler):
    def __init__(self, file: BinaryIO):
        super().__init__(file)
        self.fds: List[int] = []
    def persistent_id(self, obj: Any) -> Optional[int]:
        if isinstance(obj, FileDescriptor):
            self.fds.append(obj.id)
            return len(self.fds) - 1
        return None

class _ForkUnpickler(pickle.Unpickler):
    def __init__(self, file: BinaryIO, fds: List[int]):
        super().__init__(file)
        self.fds = fds
    def persistent_load(self, pid: int) -> FileDescriptor:
        return FileDescriptor(self.fds[pid])


def _reap(_a: Any, _b: Any) -> None:
    while True:
        try:
            (id, status) = os.waitpid(-1, os.WNOHANG)
            if id == 0: break            
        except ChildProcessError:
            break

class ForkServer:
    def __init__(self) -> None:
        s1, s2 = socket.socketpair(socket.AF_UNIX)
        self.pid = os.fork()
        if self.pid == 0:
            self.sock = s2
            s1.close()
            try:
                self._main_forkserver()
            except KeyboardInterrupt:
                pass
            # print("Fork done")
            sys.exit(0)
        else:
            self.sock = s1
            s2.close()
    
    
    def _main_forkserver(self) -> None:
        # setup
        gc.collect()
        gc.freeze()
        signal.signal(signal.SIGCHLD, _reap)
        
        while True:
            data = self.sock.recv(struct.calcsize('nn'))
            if len(data) < struct.calcsize('nn'): return
            (length, n_fds) = struct.unpack('nn', data)
            # print(f"Length, n_fds {length}, {n_fds}")
            if length == 0: return
            msg = self.sock.recv(length)
            if len(msg) < length: return
            fds = []
            if n_fds > 0:
                a = array.array('i')
                bytes_size = a.itemsize * n_fds
                msg_rights, ancdata, flags, addr = self.sock.recvmsg(1, socket.CMSG_SPACE(bytes_size))
                if not msg_rights and not ancdata:
                    raise EOFError
                if len(ancdata) != 1 or ancdata[0][0] != socket.SOL_SOCKET or ancdata[0][1] != socket.SCM_RIGHTS:
                    raise RuntimeError("Expected SCM_RIGHTS ancdata")
                cmsg_data = ancdata[0][2]
                if len(cmsg_data) != bytes_size:
                    raise ValueError
                a.frombytes(cmsg_data)
                fds = list(a)

            pid = os.fork()
            if pid == 0:
                self.sock.close()
                buf = io.BytesIO(msg)
                unpickler = _ForkUnpickler(buf, fds)
                (func, args) = unpickler.load()
                func(*args)
                sys.exit(0)
            else:
                self.sock.send(struct.pack('n', pid))
                for fd in fds:
                    os.close(fd)

    def fork(self, func: Callable, *args: Any) -> int:
        buf = io.BytesIO()
        pickler = _ForkPickler(buf)
        pickler.dump((func, args))
        msg = buf.getvalue()
        self.sock.send(struct.pack('nn', len(msg), len(pickler.fds)) + msg)
        if len(pickler.fds) > 0:
            fds_bytes = array.array('i', pickler.fds).tobytes()
            self.sock.sendmsg([b'A'], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, fds_bytes)])
        (pid,) = struct.unpack('n', self.sock.recv(struct.calcsize('n')))
        return pid

def _main_scoped_proc(_target: Callable, conn_worker: AsyncConnection, *_args: Any) -> None:
    os.setpgid(0, 0) # Start a new process group
    async def run() -> None:
        r = _target(conn_worker, *_args)
        if r is not None:
            await r
    asyncio.run(run())

class ScopedProcess:
    '''Allows a target function to be run in a `with` statement:

           async def child(c: AsyncConnection, *args): await c.send(os.getpid())
           with ScopedProcess(child, *args) as conn:
               print("Child pid:", await conn.recv())

       Interacts properly with asyncio and cancellation.'''
    def __init__(self, forkserver: ForkServer, target: Callable[..., Union[None, Awaitable[None]]], *args: Any, well_behaved: bool = False):
        self._target = target
        self._args = args
        self._conn_main: AsyncConnection
        self._pid = 0
        self._forkserver = forkserver
        self._well_behaved = well_behaved
    def __enter__(self) -> AsyncConnection:
        (self._conn_main, conn_worker) = AsyncConnection.pipe_pair()
        self._pid = self._forkserver.fork(_main_scoped_proc, self._target, conn_worker, *self._args)
        conn_worker.close() # We don't need the child end open in the parent
        del self._forkserver
        return self._conn_main

    def __exit__(self, a: Any, b: Any, c: Any) -> None:
        if self._pid != 0 and not self._well_behaved:
            try: os.killpg(self._pid, signal.SIGKILL)
            except ProcessLookupError: pass
            try: os.kill(self._pid, signal.SIGKILL)
            except ProcessLookupError: pass
        self._conn_main.close()
        

async def _cancel_and_wait_for_cleanup(tasks: Collection[asyncio.Future]) -> None:
    for task in tasks:
        if not task.done():
            task.cancel()
    # do one turn of the event loop to allow CancelledError to be raised
    await asyncio.sleep(0)
    # Clean up any remaining tasks and ensure they have finished their cleanup handlers
    for task in tasks:
        try:
            if not task.done():
                await asyncio.wait_for(task, 0)
        except asyncio.TimeoutError: pass
        except asyncio.CancelledError: pass

class ScopedTasks:
    '''Runs some coroutines in the background and cancels them on exit or cancellation.

           async with ScopedTasks() as tasks:
               tasks.add(coro())
               asyncio.sleep(1)
           # here coro is cancelled and has finished try/finally blocks

       Waits for the background tasks to finish their cancellation cleanup before continuing normal
       control flow.'''
    def __init__(self) -> None:
        self.futs: List[asyncio.Future] = []
    async def __aenter__(self) -> 'ScopedTasks':
        return self
    def add(self, *aws: Awaitable) -> None:
        self.futs.extend(asyncio.ensure_future(a) for a in aws)
    async def __aexit__(self, a: Any, b: Any, c: Any) -> None:
        await _cancel_and_wait_for_cleanup(self.futs)


_forkserver: Optional['ForkServer'] = None # This needs to be initialized in 'main', before launching threads/asyncio but after globals (syntax.the_program, etc.) are filled in.

def get_forkserver() -> ForkServer:
    global _forkserver
    if _forkserver is None:
        _forkserver = ForkServer()
    return _forkserver