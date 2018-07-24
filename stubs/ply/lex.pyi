from typing import Any

class LexToken:
    lineno: int
    value: str
    type: str

class Lexer: ...

def lex() -> Lexer: ...