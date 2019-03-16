from __future__ import annotations

import argparse
import ply
import sys

from typing import List, Optional, Set, Iterable, Generic, Iterator, TypeVar, NoReturn, \
                   Any

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

args: argparse.Namespace

Token = ply.lex.LexToken
def tok_to_string(tok: Optional[Token]) -> str:
    if tok is not None:
        return '%s:%s:%s' % (tok.filename, tok.lineno, tok.col)
    else:
        return 'None'

error_count = 0

def print_error(tok: Optional[Token], msg: str) -> None:
    global error_count
    error_count += 1
    print('error: %s: %s' % (tok_to_string(tok), msg))
    if args.exit_on_error:
        sys.exit(1)

def print_error_and_exit(tok: Optional[Token], msg: str) -> NoReturn:
    print_error(tok, msg)
    sys.exit(1)
