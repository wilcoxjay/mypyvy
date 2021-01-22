from typing import List, Optional, Any, Union, Iterable, Sequence, Iterator, Protocol, Tuple, overload

class CheckSatResult: ...

sat: CheckSatResult
unsat: CheckSatResult
unknown: CheckSatResult

z3printer: Any

class Z3PPObject: ...
class Context: ...
class ModelRef(Z3PPObject, Iterable):
    def decls(self) -> List[FuncDeclRef]: ...
    def sorts(self) -> List[SortRef]: ...
    def get_universe(self, s: SortRef) -> Sequence[ExprRef]: ...
    def eval(self, e: ExprRef, model_completion: bool=False) -> ExprRef: ...
    def __iter__(self) -> Iterator[FuncDeclRef]: ... # this doesn't actually exist, but __len__ and __getitem__ are not enough (yet), see: https://github.com/python/mypy/issues/2220
    def __len__(self) -> int: ...
    def __getitem__(self, idx: Any) -> Any: ... # can't really type this...

class Statistics: ...

class Solver(Z3PPObject):
    def __init__(self, ctx: Optional[Context] = None) -> None: ...
#    def __setattr__(self, name: str, value: Any) -> None: ...
    def __enter__(self) -> None: ...
    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None: ...
    def add(self, *args: ExprRef) -> None: ...
    def check(self, *args: ExprRef) -> CheckSatResult: ...
    def model(self) -> ModelRef: ...
    def to_smt2(self) -> str: ...
    def unsat_core(self) -> Sequence[ExprRef]: ...
    def assertions(self) -> Sequence[ExprRef]: ...
    def push(self) -> None: ...
    def pop(self, num: int=1) -> None: ...
    def reason_unknown(self) -> str: ...
    def num_scopes(self) -> int: ...
    def set(self, *args: Any) -> None: ...
    def statistics(self) -> Statistics: ...

def SolverFor(logic: str, ctx: Optional[Context]=None) -> Solver: ...


class AstRef(Z3PPObject): ...

class SortRef(AstRef):
    def name(self) -> str: ...
class ExprRef(AstRef):
      def __eq__(self, other: ExprRef) -> ExprRef: ... # type: ignore
      def __ne__(self, other: ExprRef) -> ExprRef: ... # type: ignore
      def __ge__(self, other: ExprRef) -> ExprRef: ...
      def __le__(self, other: ExprRef) -> ExprRef: ...
      def __gt__(self, other: ExprRef) -> ExprRef: ...
      def __lt__(self, other: ExprRef) -> ExprRef: ...
      def __add__(self, other: ExprRef) -> ExprRef: ...
      def __sub__(self, other: ExprRef) -> ExprRef: ...
      def __mul__(self, other: ExprRef) -> ExprRef: ...
      def __truediv__(self, other: ExprRef) -> ExprRef: ...
      def __div__(self, other: ExprRef) -> ExprRef: ...
      def __mod__(self, other: ExprRef) -> ExprRef: ...
      def __getitem__(self, idx: ExprRef) -> ExprRef: ...
      def sort(self) -> SortRef: ...
      def decl(self) -> FuncDeclRef: ...
      def translate(self, ctx: Context) -> ExprRef: ...
      def children(self) -> List[ExprRef]: ...
      def as_long(self) -> int: ...

class QuantifierRef(ExprRef):
      def is_forall(self) -> bool: ...
      def num_vars(self) -> int: ...
      def body(self) -> ExprRef: ...
      def var_sort(self, idx: int) -> SortRef: ...

class Z3DeclKind: ...  # bogus abstract type which is actually int

class FuncDeclRef(AstRef):
      def __call__(self, *args: ExprRef) -> ExprRef: ...
      def arity(self) -> int: ...
      def domain(self, i: int) -> SortRef: ...
      def range(self) -> SortRef: ...
      def name(self) -> str: ...
      def kind(self) -> Z3DeclKind: ...

class Goal(Z3PPObject):
      def add(self, *args: ExprRef) -> None: ...

class ApplyResult(Z3PPObject):
    def as_expr(self) -> ExprRef: ...

class Tactic:
      def __init__(self, tactic: str): ...
      def __call__(self, goal: Goal) -> ApplyResult: ...


def Function(name: str, *args: SortRef) -> FuncDeclRef: ...
def Bool(name: str) -> ExprRef: ...
def Const(name: str, sort: SortRef) -> ExprRef: ...
def Consts(names: str, sort: SortRef) -> List[ExprRef]: ...
def DeclareSort(name: str, ctx: Optional[Context] = ...) -> SortRef: ...
def BoolSort(ctx: Optional[Context] = ...) -> SortRef: ...
def IntSort(ctx: Optional[Context] = ...) -> SortRef: ...
def ArraySort(dom: SortRef, rng: SortRef) -> SortRef: ...

def Not(arg: ExprRef) -> ExprRef: ...
@overload
def And(*args: ExprRef) -> ExprRef: ...
@overload
def And(args: List[ExprRef]) -> ExprRef: ...
@overload
def Or(*args: ExprRef) -> ExprRef: ...
@overload
def Or(args: List[ExprRef]) -> ExprRef: ...
def Implies(a: ExprRef, b: ExprRef) -> ExprRef: ...
def Distinct(*args: ExprRef) -> ExprRef: ...
def AtMost(*args: Union[ExprRef, int]) -> ExprRef: ...

def If(e1: ExprRef, e2: ExprRef, e3: ExprRef) -> ExprRef: ...

def PbEq(args: Iterable[Tuple[ExprRef, int]], k: int) -> ExprRef: ...
def PbLe(args: Iterable[Tuple[ExprRef, int]], k: int) -> ExprRef: ...
def PbGe(args: Iterable[Tuple[ExprRef, int]], k: int) -> ExprRef: ...

def BoolVal(x: bool) -> ExprRef: ...
def IntVal(x: int) -> ExprRef: ...

def Int(name: str) -> ExprRef: ...
def Ints(names: str) -> Sequence[ExprRef]: ...

def ForAll(vs: Union[ExprRef, List[ExprRef]], body: ExprRef) -> ExprRef: ...
def Exists(vs: Union[ExprRef, List[ExprRef]], body: ExprRef) -> ExprRef: ...

def Update(a: ExprRef, i: ExprRef, v: ExprRef) -> ExprRef: ...

def main_ctx() -> Context: ...

def set_param(*args: Any) -> None: ...

def substitute(t: ExprRef, *m: Tuple[ExprRef, ExprRef]) -> ExprRef: ...
def substitute_vars(t: ExprRef, *m: ExprRef) -> ExprRef: ...

def is_app(a: ExprRef) -> bool: ...
def is_quantifier(e: ExprRef) -> bool: ...
def is_bool(e: ExprRef) -> bool: ...
def is_false(e: ExprRef) -> bool: ...
def is_true(e: ExprRef) -> bool: ...
def is_const(a: ExprRef) -> bool: ...
def is_arith(e: ExprRef) -> bool: ...
def is_int(e: ExprRef) -> bool: ...
def is_int_value(e: ExprRef) -> bool: ...
def is_and(a: ExprRef) -> bool: ...
def is_or(a: ExprRef) -> bool: ...
def is_not(a: ExprRef) -> bool: ...
def is_implies(a: ExprRef) -> bool: ...
def is_app_of(a: ExprRef, tp: Any) -> bool: ...
Z3_OP_ITE: Any = ...

def open_log(filename: str) -> None: ...
def append_log(msg: str) -> None: ...

def Datatype(name: str) -> Any: ...  # TODO: type this better

