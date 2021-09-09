from __future__ import annotations

import dataclasses
from dataclasses import dataclass
import re
import string

from typing import Iterable, Iterator, List, Mapping, Optional, Set, Union, overload

@dataclass
class SList:
    contents: List[Sexp]

    def __str__(self) -> str:
        return f'({" ".join(str(arg) for arg in self.contents)})'

    def __iter__(self) -> Iterator[Sexp]:
        return iter(self.contents)

    def __len__(self) -> int:
        return len(self.contents)

    @overload
    def __getitem__(self, i: int) -> Sexp: ...
    @overload
    def __getitem__(self, i: slice) -> List[Sexp]: ...
    def __getitem__(self, i: Union[int, slice]) -> Union[Sexp, List[Sexp]]:
        return self.contents[i]

@dataclass
class Atom:
    name: str

    def __str__(self) -> str:
        return self.name

@dataclass
class Comment:
    contents: str

    def __str__(self) -> str:
        return f';{self.contents}\n'

Sexp = Union[Comment, str, SList]

# note: does not understand variable binding!
# be careful when substituting into expressions with bound variables.
def subst(assignment: Mapping[str, Sexp], e: Sexp) -> Sexp:
    if isinstance(e, Comment):
        return e
    elif isinstance(e, str):
        if e in assignment:
            return assignment[e]
        else:
            return e
    else:
        return SList([subst(assignment, x) for x in e.contents])


def symbols_used(e: Sexp, into: Optional[Set[str]] = None) -> Set[str]:
    if into is None:
        into = set()
    if isinstance(e, Comment):
        return into
    elif isinstance(e, str):
        into.add(e)
        return into
    else:
        for x in e.contents:
            symbols_used(x, into=into)
        return into


@dataclass
class EOF:
    pass

@dataclass
class CharBuffer:
    contents: str
    pos: int = dataclasses.field(default=0)

    def add_input(self, new_input: str) -> None:
        self.contents += new_input

token_specification = [
    ('ID', r'[^(); \t\n]+'),
    ('COMMENT', r';.*\n'),
    ('LPAREN', r'\('),
    ('RPAREN', r'\)'),
    ('BLANK', r'[ \t\n]+')
]
tok_regex = re.compile('|'.join('(?P<%s>%s)' % pair for pair in token_specification))

@dataclass
class SexpLexer:
    buffer: CharBuffer

    def add_input(self, new_input: str) -> None:
        self.buffer.add_input(new_input)

    def skip_whitespace(self) -> None:
        contents = self.buffer.contents
        n = len(contents)
        i = self.buffer.pos
        while i < n and contents[i] in string.whitespace:
            i += 1
        self.buffer.pos = i

    def tokens(self) -> Iterable[Union[Comment, Atom, str, EOF]]:
        while True:
            mo = tok_regex.match(self.buffer.contents, self.buffer.pos)
            if mo is None:
                yield EOF()
                continue
            kind = mo.lastgroup
            value = mo.group()
            # print(self.buffer.pos, mo.start(), mo.end(), value)
            self.buffer.pos = mo.end()
            if kind == 'ID':
                yield Atom(value)
            elif kind == 'COMMENT':
                yield Comment(value[1:])
            elif kind == 'LPAREN':
                yield '('
            elif kind == 'RPAREN':
                yield ')'
            elif kind == 'BLANK':
                continue
            else:
                assert False

        # assert False
        #
        # parens = '()'
        # separators = '();' + string.whitespace
        #
        # while True:
        #     self.skip_whitespace()
        #
        #     contents = self.buffer.contents
        #     n = len(contents)
        #
        #     if self.buffer.pos >= n:
        #         yield EOF()
        #         continue
        #
        #     c = contents[self.buffer.pos]
        #     if c in parens:
        #         self.buffer.pos += 1
        #         yield c
        #     elif c == ';':
        #         self.buffer.pos += 1
        #         start = self.buffer.pos
        #         i = start
        #         while i < n and contents[i] != '\n':
        #             i += 1
        #         self.buffer.pos = i
        #         yield Comment(contents[start:i])
        #     else:
        #         start = self.buffer.pos
        #         i = start
        #         while i < n and contents[i] not in separators:
        #             i += 1
        #         self.buffer.pos = i
        #         # assert self.buffer.pos > start
        #         yield Atom(contents[start:i])

@dataclass
class SexpParser:
    lexer: SexpLexer
    stack: List[List[Sexp]] = dataclasses.field(default_factory=list)

    def add_input(self, new_input: str) -> None:
        self.lexer.add_input(new_input)

    def parse(self) -> Iterable[Union[Sexp, EOF]]:
        for tok in self.lexer.tokens():
            # print(repr(tok))
            t = type(tok)
            if t is EOF:
                new_input = yield tok  # type: ignore
                if new_input is not None:
                    assert isinstance(new_input, str)
                    self.add_input(new_input)
            elif t is Comment or t is Atom:
                if t is Atom:
                    ans: Union[str, Comment] = tok.name  # type: ignore
                else:
                    ans = tok  # type: ignore

                if not self.stack:
                    yield ans
                else:
                    self.stack[-1].append(ans)
            else:
                # assert isinstance(tok, str)
                # assert tok in '()'
                if tok == '(':
                    self.stack.append([])
                else:
                    assert tok == ')'
                    assert len(self.stack) > 0, 'unexpected close paren'
                    prev = SList(self.stack.pop())
                    if not self.stack:
                        yield prev
                    else:
                        self.stack[-1].append(prev)

def get_parser(input: str) -> SexpParser:
    return SexpParser(SexpLexer(CharBuffer(input)))

def parse(input: str) -> Iterable[Sexp]:
    for sexp in get_parser(input).parse():
        if isinstance(sexp, EOF):
            return
        else:
            yield sexp

def parse_one(input: str) -> Sexp:
    l = list(parse(input))
    assert len(l) == 1
    return l[0]
