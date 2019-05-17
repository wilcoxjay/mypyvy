from __future__ import annotations

import argparse
from datetime import datetime
import functools
import logging
from pathlib import Path
import ply
import ply.lex
import sys
import xml
import xml.sax
import xml.sax.saxutils

from typing import List, Optional, Set, Iterable, Generic, Iterator, TypeVar, NoReturn, \
                   Any, Callable, cast, Sequence


T = TypeVar('T')

class OrderedSet(Generic[T], Iterable[T]):
    def __init__(self, contents: Optional[Iterable[T]]=None) -> None:
        self.l: List[T] = []
        self.s: Set[T] = set()

        if contents is None:
            contents = []

        for x in contents:
            self.add(x)

    def __len__(self) -> int:
        return len(self.l)

    def __str__(self) -> str:
        return '{%s}' % ','.join(str(x) for x in self.l)

    def __contains__(self, item: T) -> bool:
        return item in self.s

    def add(self, x: T) -> None:
        if x not in self.s:
            self.l.append(x)
            self.s.add(x)

    def remove(self, x: T) -> None:
        if x not in self.s:
            raise

    def __isub__(self, other: Set[T]) -> OrderedSet[T]:
        self.s -= other
        self.l = [x for x in self.l if x in self.s]
        return self

    def __iter__(self) -> Iterator[T]:
        return iter(self.l)

MySet = OrderedSet

# Dummy class that is not used at run time. Allows us to statically declare and check
# which options are available.
class MypyvyArgs(object):
    forbid_parser_rebuild: bool
    log: str
    log_time: bool
    log_xml: bool
    seed: int
    print_program_repr: bool
    print_program: bool
    key_prefix: str
    minimize_models: bool
    timeout: int
    exit_on_error: bool
    ipython: bool
    error_filename_basename: bool
    query_time: bool
    print_counterexample: bool
    print_cmdline: bool
    simplify_diagram: bool
    use_z3_unsat_cores: bool
    smoke_test: bool
    assert_inductive_trace: bool
    sketch: bool
    block_may_cexs: bool
    push_frame_zero: str
    automaton: Any  # str or bool depending on updr vs. verify
    check_transition: Sequence[str]
    check_invariant: Sequence[str]
    safety: str
    depth: int
    filename: str
    sharp: bool
    def main(self, solver: Any, prog: Any) -> None: ...

args: MypyvyArgs = cast(MypyvyArgs, None)  # ensure that args is always defined

Token = ply.lex.LexToken
def clean_filename(filename: str) -> str:
    if args.error_filename_basename:
        return Path(filename).name
    else:
        return filename

def tok_to_string(tok: Optional[Token]) -> str:
    return '%s:%s:%s' % (clean_filename(tok.filename), tok.lineno, tok.col) if tok is not None else 'None'

error_count = 0

def print_error(tok: Optional[Token], msg: str) -> None:
    global error_count
    error_count += 1
    print('error%s: %s' % (' ' + tok_to_string(tok) if tok is not None else '', msg))
    if args.exit_on_error:
        sys.exit(1)

def print_error_and_exit(tok: Optional[Token], msg: str) -> NoReturn:
    print_error(tok, msg)
    sys.exit(1)

def print_warning(tok: Optional[Token], msg: str) -> None:
    print('warning%s: %s' % (' ' + tok_to_string(tok) if tok is not None else '', msg))


class MyLogger(object):
    ALWAYS_PRINT = 35

    def __init__(self, logger: logging.Logger, start: datetime) -> None:
        self.logger = logger
        self.start = start

    def setLevel(self, lvl: int) -> None:
        self.logger.setLevel(lvl)

    def isEnabledFor(self, lvl: int) -> bool:
        return self.logger.isEnabledFor(lvl)

    def warning(self, msg: str, end: str='\n') -> None:
        self.log(logging.WARNING, msg, end=end)

    def info(self, msg: str, end: str='\n') -> None:
        self.log(logging.INFO, msg, end=end)

    def debug(self, msg: str, end: str='\n') -> None:
        self.log(logging.DEBUG, msg, end=end)

    def always_print(self, msg: str, end: str='\n') -> None:
        self.log(MyLogger.ALWAYS_PRINT, msg, end=end)

    def log_list(self, lvl: int, msgs: List[str], sep: str='\n', end: str='\n') -> None:
        if args.log_xml:
            n = len(msgs)
            for i, msg in enumerate(msgs):
                self.log(lvl, msg, end=sep if i < n - 1 else end)
        else:
            self.log(lvl, sep.join(msgs), end=end)

    def log(self, lvl: int, msg: str, end: str='\n') -> None:
        if self.isEnabledFor(lvl):
            if args.log_xml:
                msg = xml.sax.saxutils.escape(msg)
                with LogTag(self, 'msg', lvl=lvl, time=str((datetime.now() - self.start).total_seconds())):
                    self.rawlog(MyLogger.ALWAYS_PRINT, msg, end=end)
            else:
                self.rawlog(lvl, msg, end=end)

    def rawlog(self, lvl: int, msg: str, end: str='\n') -> None:
        self.logger.log(lvl, msg + end)

class LogTag(object):
    def __init__(self, logger: MyLogger, name: str, lvl: int=MyLogger.ALWAYS_PRINT, **kwargs: str) -> None:
        self.logger = logger
        self.name = name
        self.lvl = lvl
        self.kwargs = kwargs

    def __enter__(self) -> None:
        if args.log_xml and self.logger.isEnabledFor(self.lvl):
            msg = ''
            for k, v in self.kwargs.items():
                msg += ' %s="%s"' % (k, xml.sax.saxutils.escape(v))

            self.logger.rawlog(MyLogger.ALWAYS_PRINT, '<%s%s>' % (self.name, msg))

    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None:
        if args.log_xml and self.logger.isEnabledFor(self.lvl):
            self.logger.rawlog(MyLogger.ALWAYS_PRINT, '</%s>' % self.name)

logger = MyLogger(logging.getLogger('mypyvy'), datetime.now())

FuncType = Callable[..., Any]
F = TypeVar('F', bound=FuncType)
def log_start_end_time(logger: MyLogger, lvl: int=logging.DEBUG) -> Callable[[F], F]:
    def dec(func: F) -> F:
        @functools.wraps(func)
        def wrapped(*args: Any, **kwargs: Any) -> Any:
            start = datetime.now()
            logger.log(lvl, '%s started at %s' % (func.__name__, start))
            ans = func(*args, **kwargs)
            end = datetime.now()
            logger.log(lvl, '%s ended at %s (took %s seconds)' % (func.__name__, end, (end - start).total_seconds()))
            return ans
        return cast(F, wrapped)
    return dec

def log_start_end_xml(logger: MyLogger, lvl: int=logging.DEBUG, tag: Optional[str]=None) -> Callable[[F], F]:
    def dec(func: F) -> F:
        @functools.wraps(func)
        def wrapped(*args: Any, **kwargs: Any) -> Any:
            with LogTag(logger, tag if tag is not None else func.__name__, lvl=lvl):
                ans = func(*args, **kwargs)
            return ans
        return cast(F, wrapped)
    return dec


class YesNoAction(argparse.Action):
    '''Parser argument with --[no-]option.
    Based on:
    https://thisdataguy.com/2017/07/03/no-options-with-argparse-and-python/
    https://stackoverflow.com/questions/9234258/in-python-argparse-is-it-possible-to-have-paired-no-something-something-arg
    '''
    def __init__(self,
                 option_strings: List[str],
                 dest: str,
                 nargs: Any = None,
                 const: Any = None,
                 default: bool = False,
                 help: Optional[str] = None,
                 **kwargs: Any
    ) -> None:
        if nargs is not None:
            raise ValueError('nargs not allowed')
        if const is not None:
            raise ValueError('const not allowed')
        if not (isinstance(option_strings, (list, tuple)) and
                len(option_strings) == 1 and
                option_strings[0].startswith('--')):
            raise ValueError(f'bad option_strings: {option_strings}')
        if help is not None:
            help = f'{help} (or not, default {"yes" if default else "no"})'
        yes = option_strings[0]
        no = '--no-' + yes[2:]
        super().__init__([yes, no], dest, nargs=0, const=None, default=default, help=help, **kwargs)
        self._yes = yes
        self._no = no

    def __call__(self, parser: Any, namespace: Any, values: Any, option_string : Optional[str] = None) -> None:
        assert option_string is not None, 'Cannot use Flag as a positional argument'
        assert option_string in [self._yes, self._no]
        setattr(namespace, self.dest, option_string == self._yes)
