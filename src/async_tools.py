
from typing import Callable, List, Optional, Sequence, Tuple, Union, NoReturn, Any, Awaitable, TypeVar
import multiprocessing
import signal
import struct
import asyncio
import os
import pickle

async def _readexactly(read_fd: int, size: int) -> bytes:
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

async def _writeexactly(write_fd: int, buf: bytes) -> None:
    if len(buf) == 0: return
    try:
        written = os.write(write_fd, buf)
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
                w = os.write(write_fd, buf[written:])
                written += w
            except BlockingIOError:
                pass
            except BrokenPipeError:
                raise EOFError()
        return
    finally:
        loop.remove_writer(write_fd)

# async def test():
#     (a, b) = os.pipe()
#     os.set_blocking(a, False)
#     os.set_blocking(b, False)
#     async def reader() -> None:
#         while True:
#             v = await _readexactly(a, 10000)
#             print("Got 10000 bytes")
#     t = asyncio.create_task(reader())
#     await _writeexactly(b, bytes(1000000))
#     t.cancel()
#     os.close(a)
#     try:
#         await _writeexactly(b, bytes(1000000))
#     except EOFError:
#         print("got eof when writing")
#     while True: pass
# asyncio.run(test())

class AsyncConnection:
    HEADER_FMT = '<Q'
    HEADER_SIZE = struct.calcsize(HEADER_FMT)
    def __init__(self, read: int, write: int) -> None:
        self._read_fd = read
        os.set_blocking(read, False)
        self._write_fd = write
        os.set_blocking(write, False)

    async def recv(self) -> Any:
        header = await _readexactly(self._read_fd, AsyncConnection.HEADER_SIZE)
        data = await _readexactly(self._read_fd, struct.unpack(AsyncConnection.HEADER_FMT, header)[0])
        return pickle.loads(data)

    async def send(self, v: Any) -> None:
        pickled = pickle.dumps(v, protocol=pickle.HIGHEST_PROTOCOL)
        await _writeexactly(self._write_fd, struct.pack(AsyncConnection.HEADER_FMT, len(pickled)))
        await _writeexactly(self._write_fd, pickled)

    def close(self) -> None:
        os.close(self._read_fd)
        os.close(self._write_fd)

    @staticmethod
    def pipe_pair() -> Tuple['AsyncConnection', 'AsyncConnection']:
        (dn_r, dn_w) = os.pipe() # Down pipe (written on top, read on bottom)
        (up_r, up_w) = os.pipe() # Up pipe (written on bottom, read on top)
        return (AsyncConnection(up_r, dn_w), AsyncConnection(dn_r, up_w))

T = TypeVar('T')
async def async_race(aws: Sequence[Awaitable[T]]) -> T:
    '''Returns the first value from `aws` and cancels the other tasks.
    
    Ignores exceptions from the awaitables, unless all awaitables produce an exception,
    which causes `async_race` to raise the exception from an arbitrary awaitable.
    `aws` must be non-empty. '''
    tasks: List[asyncio.Future[T]] = [a if isinstance(a, asyncio.Task) else asyncio.create_task(a) for a in aws]
    while True:
        try:
            done, pending = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
        except asyncio.CancelledError:
            for task in tasks:
                task.cancel()
            raise
        exc: Optional[BaseException] = None
        for f in done:
            if f.cancelled():
                exc = asyncio.CancelledError()
            elif f.exception() is None:
                for unfinished in pending:
                    unfinished.cancel()
                return f.result()
            else:
                exc = f.exception()
        if len(pending) == 0:
            if exc is not None:
                raise exc
            else:
                raise ValueError("Empty sequence passed to async_race()")
        tasks = list(pending)

class ScopedProcess:
    '''Allows a target function to be run in a `with` statement:
       
       async def child(): await c.send(os.getpid())
       with ScopedProcess() as conn:
           print("Child pid:", await conn.recv())

       Interacts properly with asyncio and cancellation.'''
    def __init__(self, target: Callable[[AsyncConnection], Union[None, Awaitable[None]]], well_behaved: bool = False):
        self._target = target
        self._conn_main: AsyncConnection
        self._proc: multiprocessing.Process
        self._well_behaved = well_behaved
    @staticmethod
    def _kill_own_pgroup(signal_num: int, frame: Any) -> NoReturn:
        signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM})
        os.killpg(os.getpgid(os.getpid()), signal.SIGTERM)
        os._exit(0)
    def __enter__(self) -> AsyncConnection:
        #(self._conn_main, conn_worker) = multiprocessing.Pipe(duplex = True)

        (self._conn_main, conn_worker) = AsyncConnection.pipe_pair()

        def proc() -> None:
            os.setpgid(0, 0)
            signal.signal(signal.SIGTERM, ScopedProcess._kill_own_pgroup)
            signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGTERM})
            async def run() -> None:                    
                # c = AsyncConnection2(dn_r, up_w)
                # await c.connect(dn_r, up_w)
                r = self._target(conn_worker)
                if r is not None:
                    await r
            asyncio.run(run())

        self._proc = multiprocessing.Process(target=proc, args = ())
        signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM})
        self._proc.start()
        signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGTERM})
        conn_worker.close()
        # self._conn_main = AsyncConnection2(up_r, dn_w)
        # await self._conn_main.connect(up_r, dn_w)

        return self._conn_main
    def __exit__(self, a: Any, b: Any, c: Any) -> None:
        self._conn_main.close()
        p = self._proc.pid
        if p is not None and not self._well_behaved:
            try: os.killpg(p, signal.SIGKILL)
            except ProcessLookupError: pass
            try: os.kill(p, signal.SIGKILL)
            except ProcessLookupError: pass
        self._proc.join()
        self._proc.close()

class ScopedTask:
    def __init__(self, aws: Awaitable) -> None:
        self.fut = asyncio.ensure_future(aws)
    async def __aenter__(self) -> None:
        return None
    async def __aexit__(self, a: Any, b: Any, c: Any) -> None:
        self.fut.cancel()
        try: await self.fut
        except asyncio.CancelledError: pass
