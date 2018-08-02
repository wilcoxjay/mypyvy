from typing import Any

class LexToken:
    lineno: int
    value: str
    type: str
    filename: str
    col: int

class Lexer: ...

def lex() -> Lexer: ...