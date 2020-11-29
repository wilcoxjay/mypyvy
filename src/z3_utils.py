import z3
from typing import Set, Tuple, Iterator

def is_function_symbol(s: z3.ExprRef) -> bool:
    if not z3.is_app(s):
        return False
    if z3.is_const(s):
        return False

    func = s.decl()
    if func.range() == z3.BoolSort():
        # predicate symbol
        return False

    if func.name().lower() == 'if':
        return False

    return True


def function_symbols(s: z3.ExprRef) -> Set[z3.FuncDeclRef]:
    fsymbols = set()
    if is_function_symbol(s):
        fsymbols.add(s.decl())

    for child in s.children():
        fsymbols.update(function_symbols(child))

    return fsymbols


def z3_skolemize(e: z3.ExprRef) -> z3.ExprRef:
    g = z3.Goal()
    g.add(e)
    t = z3.Tactic('snf')
    res = t(g)
    return res.as_expr()

def z3_quantifier_alternations(e: z3.ExprRef) -> Iterator[Tuple[z3.SortRef, z3.SortRef]]:
    skolemized = z3_skolemize(e)
    for fsym in function_symbols(skolemized):
        for i in range(0, fsym.arity()):
            yield (fsym.domain(i), fsym.range())
