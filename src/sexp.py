from __future__ import annotations

import dataclasses
from dataclasses import dataclass
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

    def at_eof(self) -> bool:
        return self.pos >= len(self.contents)

    def peek(self) -> str:
        assert not self.at_eof()
        return self.contents[self.pos]

    def advance(self) -> str:
        assert not self.at_eof()
        c = self.peek()
        self.pos += 1
        return c

@dataclass
class SexpLexer:
    buffer: CharBuffer

    def add_input(self, new_input: str) -> None:
        self.buffer.add_input(new_input)

    def skip_whitespace(self) -> None:
        while not self.buffer.at_eof() and self.buffer.peek() in string.whitespace:
            self.buffer.advance()

    def tokens(self) -> Iterable[Union[Comment, Atom, str, EOF]]:
        parens = '()'
        separators = '();' + string.whitespace

        while True:
            self.skip_whitespace()

            if self.buffer.at_eof():
                yield EOF()
                continue

            c = self.buffer.peek()
            if c in parens:
                self.buffer.advance()
                yield c
            elif c == ';':
                self.buffer.advance()
                comment = []
                while not self.buffer.at_eof() and self.buffer.peek() != '\n':
                    comment.append(self.buffer.advance())
                yield Comment(''.join(comment))
            else:
                tok = []
                while not self.buffer.at_eof() and self.buffer.peek() not in separators:
                    tok.append(self.buffer.advance())
                assert len(tok) > 0
                yield Atom(''.join(tok))

@dataclass
class SexpParser:
    lexer: SexpLexer
    stack: List[List[Sexp]] = dataclasses.field(default_factory=list)

    def add_input(self, new_input: str) -> None:
        self.lexer.add_input(new_input)

    def parse(self) -> Iterable[Union[Sexp, EOF]]:
        for tok in self.lexer.tokens():
            # print(repr(tok))
            if isinstance(tok, EOF):
                new_input = yield tok
                if new_input is not None:
                    assert isinstance(new_input, str)
                    self.add_input(new_input)
            elif isinstance(tok, (Comment, Atom)):
                if isinstance(tok, Atom):
                    ans: Union[str, Comment] = tok.name
                else:
                    ans = tok

                if not self.stack:
                    yield ans
                else:
                    self.stack[-1].append(ans)
            else:
                assert isinstance(tok, str)
                assert tok in '()'
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
