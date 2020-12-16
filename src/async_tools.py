
from typing import Callable, Collection, Iterable, List, Optional, Tuple, Union, Any, Awaitable, TypeVar
import multiprocessing
import signal
import struct
import asyncio
import os
import pickle

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

async def _write_exactly(write_fd: int, buf: bytes) -> None:
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

class AsyncConnection:
    '''A bidirectional pipe like `multiprocessing.Connection`, but `send` and `recv` are coroutines.'''
    HEADER_FMT = '<Q'
    HEADER_SIZE = struct.calcsize(HEADER_FMT)
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
        pickled = pickle.dumps(v, protocol=pickle.HIGHEST_PROTOCOL)
        pickled = struct.pack(AsyncConnection.HEADER_FMT, len(pickled)) + pickled
        # await _write_exactly(self._write_fd, struct.pack(AsyncConnection.HEADER_FMT, len(pickled)))
        await _write_exactly(self._write_fd, pickled)

    def close(self) -> None:
        os.close(self._read_fd)
        os.close(self._write_fd)

    @staticmethod
    def pipe_pair() -> Tuple['AsyncConnection', 'AsyncConnection']:
        (dn_r, dn_w) = os.pipe() # Down pipe (written on top, read on bottom)
        (up_r, up_w) = os.pipe() # Up pipe (written on bottom, read on top)
        return (AsyncConnection(up_r, dn_w), AsyncConnection(dn_r, up_w))

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
    def __enter__(self) -> AsyncConnection:

        def proc(conn_main: AsyncConnection, conn_worker: AsyncConnection) -> None:
            os.setpgid(0, 0) # Start a new process group
            conn_main.close() # We don't need the parent end open in the child
            async def run() -> None:
                r = self._target(conn_worker)
                if r is not None:
                    await r
            asyncio.run(run())

        (self._conn_main, conn_worker) = AsyncConnection.pipe_pair()
        self._proc = multiprocessing.Process(target=proc, args = (self._conn_main, conn_worker))
        self._proc.start() # This is where the fork actually happens
        conn_worker.close() # We don't need the child end open in the parent
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

T = TypeVar('T')
async def async_race(aws: Iterable[Awaitable[T]]) -> T:
    '''Returns the first value from `aws` and cancels the other tasks.

    Ignores exceptions from the awaitables, unless all awaitables produce an exception,
    which causes `async_race` to raise the exception from an arbitrary awaitable.
    `aws` must be non-empty. '''
    tasks: List[asyncio.Future[T]] = [a if isinstance(a, asyncio.Task) else asyncio.create_task(a) for a in aws]
    while True:
        try:
            done, pending = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
        except asyncio.CancelledError:
            await _cancel_and_wait_for_cleanup(tasks)
            raise
        exc: Optional[BaseException] = None
        for f in done:
            if f.cancelled():
                exc = asyncio.CancelledError()
            elif f.exception() is None:
                await _cancel_and_wait_for_cleanup(pending)
                return f.result()
            else:
                exc = f.exception()
        if len(pending) == 0:
            if exc is not None:
                raise exc
            else:
                raise ValueError("Empty sequence passed to async_race()")
        tasks = list(pending)

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
