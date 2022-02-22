

from contextlib import contextmanager
import heapq
from io import StringIO
import io
import math
import random
import time
import pickle
from typing import IO, Callable, Dict, Generator, Generic, Iterable, Iterator, Optional, Any, List, Tuple, Type, TypeVar, cast, Set
from dataclasses import dataclass, field

class Tracer:
    @dataclass
    class EndSpan:
        span: 'Tracer.Span'
        t: float
    @dataclass
    class StartSpan:
        span: 'Tracer.Span'
        t: float
    @dataclass
    class LogEvent:
        span: 'Tracer.Span'
        t: float
        d: Any
    @dataclass
    class DataEvent:
        span: 'Tracer.Span'
        d: Dict

    def __init__(self, file: IO[bytes]):
        self._file = file
        self._pickler = pickle.Pickler(self._file, protocol=pickle.HIGHEST_PROTOCOL)
        self._messages: List[Any] = []
        self._root = Tracer.Span(self, None, '', None)
        self._pickler.dump(self._root)

    @staticmethod
    def dummy_span() -> 'Tracer.Span':
        return Tracer.Span(None, None, '', None)
        
    def flush(self) -> None:
        self._pickler.dump((time.perf_counter(), self._messages))
        self._file.flush()
        self._messages = []
    
    def _start(self, e: 'Span') -> None:
        self._messages.append(Tracer.StartSpan(e, time.perf_counter()))
    def _end(self, e: 'Span') -> None:
        self._messages.append(Tracer.EndSpan(e, time.perf_counter()))
    def _log(self, e: 'Span', d: Any) -> None:
        self._messages.append(Tracer.LogEvent(e, time.perf_counter(), d))
    def _data(self, e: 'Span', **kwargs: Any) -> None:
        self._messages.append(Tracer.DataEvent(e, kwargs))
    
    class Span:
        def __init__(self, base: Optional['Tracer'], upstream: Optional['Tracer.Span'], category: str, instance: Any):
            self._base = base
            self._upstream = upstream
            self._category = category
            self._instance = instance

        def __getstate__(self) -> Tuple:
            return (self._upstream, self._category, self._instance)
        def __setstate__(self, d: Tuple) -> None:
            self._base = cast(Tracer, None)
            self._upstream, self._category, self._instance = d

        @contextmanager
        def span(self, category: str, instance: Any = None) -> Iterator['Tracer.Span']:
            span = Tracer.Span(self._base, self, category, instance)
            if self._base:
                self._base._start(span)
            try:
                yield span
            finally:
                if self._base:
                    self._base._end(span)
        
        def log(self, data: Any) -> None:
            if self._base:
                self._base._log(self, data)
        
        def data(self, **kwargs: Any) -> None:
            if self._base:
                self._base._data(self, **kwargs)

        def flush(self) -> None:
            if self._base:
                self._base.flush()

        def __str__(self) -> str:
            return f'[{self._category}]({self._instance})'

@contextmanager
def trace(file: IO[bytes]) -> Iterator['Tracer.Span']:
    self = Tracer(file)
    self._start(self._root)
    try:
        yield self._root
    finally:
        self._end(self._root)
        self.flush()

@dataclass
class Span:
    category: str
    instance: Any
    duration: float = float('NaN')
    start_time: float = float('NaN')
    closed: bool = False
    log: List[Tuple[float, Any]] = field(default_factory=list)
    data: Dict = field(default_factory=dict)
    spans: List['Span'] = field(default_factory=list)
    def pp(self, indent: int, parent_start: Optional[float], out: IO[str]) -> None:
        offset_str = f' +{self.start_time - parent_start:0.3f}' if parent_start is not None else ''
        instance_str = f'({self.instance})' if self.instance is not None else ''
        out.write(f'{" "* indent}[{self.category}]{instance_str} {"" if self.closed else ">="}{self.duration:0.3f}sec{offset_str}\n')
        if len(self.data) > 0:
            contents = ", ".join(f'{k}: {v}' for k,v in self.data.items())
            out.write(f'{" "* indent}{contents}\n')
        for (t, l) in self.log:
            out.write(f'{" "* indent}{l} +{t-self.start_time:0.3f}sec\n')
        for s in self.spans:
            s.pp(indent + 2, self.start_time, out)

    def descendants(self, category: str) -> Generator['Span', None, None]:
        for c in self.spans:
            if c.category == category:
                yield c
            yield from c.descendants(category)

    def __str__(self) -> str:
        io = StringIO()
        self.pp(0, None, io)
        return io.getvalue()

def load_trace(file: IO[bytes]) -> Span:
    unpickler = pickle.Unpickler(file)
    root_tracer = unpickler.load()
    messages = []
    latest_time = 0
    while True:
        try:
            latest_time, loaded = unpickler.load()
            messages.extend(loaded)
        except EOFError:
            break
        except pickle.UnpicklingError:
            print("Warning: truncated data...")
            break
    
    spans: Dict[Tracer.Span, Span] = {}
    unclosed: Dict[int, Span] = {}
    def get_span(s: Tracer.Span) -> Span:
        if s not in spans:
            spans[s] = Span(s._category, s._instance)
        return spans[s]
    
    for m in messages:
        if isinstance(m, Tracer.StartSpan):
            s = get_span(m.span)
            s.start_time = m.t
            if m.span._upstream is not None:
                parent = get_span(m.span._upstream)
                parent.spans.append(s)
            unclosed[id(s)] = s
        elif isinstance(m, Tracer.EndSpan):
            s = get_span(m.span)
            s.duration = m.t - s.start_time
            s.closed = True
            del unclosed[id(s)]
        elif isinstance(m, Tracer.LogEvent):
            s = get_span(m.span)
            s.log.append((m.t, m.d))
        elif isinstance(m, Tracer.DataEvent):
            s = get_span(m.span)
            s.data.update(m.d)
        else:
            assert False

    for s in unclosed.values():
        s.duration = latest_time - s.start_time
    return get_span(root_tracer)

_T = TypeVar("_T")
class Sampler(Generic[_T]):
    @dataclass(order=True)
    class Item:
        priority: float
        weight: float
        data: Any = field(compare=False, default=None)

    def __init__(self, k: int, output: Optional[IO[bytes]] = None):
        self._samples: List[Sampler.Item] = []
        self._k = k
        self._output = output

    def sample(self, weight: float, data: Callable[[], _T]) -> bool:
        """Provide an item. If included in the sample, data() will be called to produce the data, and returns True. Otherwise, returns False."""
        assert weight > 0
        r = -math.log(random.random()) / weight
        new_item = Sampler.Item(r, weight)
        if len(self._samples) < self._k:
            heapq.heappush(self._samples, new_item)
        else:
            old_item = heapq.heappushpop(self._samples, new_item)
            if old_item is new_item:
                return False
        new_item.data = data()
        if self._output:
            pickle.dump(new_item, self._output)
            self._output.flush()
        return True

    @staticmethod
    def load(k: int, file: IO[bytes]) -> 'Sampler[_T]':
        self: Sampler[_T] = Sampler(k)
        while True:
            try: item = pickle.load(file)
            except EOFError: break

            if len(self._samples) < self._k:
                heapq.heappush(self._samples, item)
            else:
                heapq.heappushpop(self._samples, item)
        return self
            
    def merge(self, s: 'Sampler[_T]') -> None:
        """Merge this sampler with the given one. Modifies `self` in place. For accurate results, k parameters must match."""
        for item in s._samples:
            if len(self._samples) < self._k:
                heapq.heappush(self._samples, item)
            else:
                old_item = heapq.heappushpop(self._samples, item)
                if old_item is item:
                    continue
            if self._output:
                pickle.dump(item, self._output)
        if self._output:
            self._output.flush()
        
    def values(self) -> Iterable[_T]:
        for i in self._samples:
            yield i.data

    def clear(self) -> None:
        self._samples.clear()
