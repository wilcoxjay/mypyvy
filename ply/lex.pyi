from typing import Any

class LexToken:
    lineno: int
    value: str
    type: str
    filename: str
    col: int
    lexpos: int
    lexer: Lexer

class Lexer:
    def input(self, s: str) -> None: ...
    def token(self) -> LexToken: ...

    lineno: int
    bol: int



def lex(debug: bool=False, optimize: bool=False, forbid_rebuild: bool=False) -> Lexer: ...
