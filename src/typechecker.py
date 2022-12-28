import syntax
from syntax import Span, InferenceSort, SortInferencePlaceholder, Sort, BoolSort, IntSort
from syntax import SortDecl, RelationDecl, ConstantDecl, FunctionDecl, DefinitionDecl

import utils

from typing import Optional, Union

def check_constraint(span: Optional[Span], expected: InferenceSort, actual: InferenceSort) -> InferenceSort:
    def normalize(s: Union[Sort, SortInferencePlaceholder]) -> Union[Sort, SortInferencePlaceholder]:
        if isinstance(s, SortInferencePlaceholder):
            s = s.root()
            if s.sort is not None:
                s = s.sort
        return s

    if expected is None or actual is None:
        return expected or actual

    expected = normalize(expected)
    actual = normalize(actual)

    if isinstance(expected, Sort):
        if isinstance(actual, Sort):
            if expected != actual:
                utils.print_error(span, 'expected sort %s but got %s' % (expected, actual))
            return actual  # either would be fine
        else:
            actual.solve(expected)
            return expected
    else:
        if isinstance(actual, Sort):
            expected.solve(actual)
            return actual
        else:
            expected.merge(actual)
            return expected

def pre_typecheck_binder(scope: syntax.Scope, binder: syntax.Binder) -> None:
    for sv in binder.vs:
        existing = scope.get(sv.name)
        if existing is not None and not isinstance(existing, tuple):
            if isinstance(existing, ConstantDecl):
                thing = 'constant'
            elif isinstance(existing, RelationDecl):
                thing = 'relation'
            elif isinstance(existing, FunctionDecl):
                thing = 'function'
            else:
                assert False
            utils.print_error(sv.span, f'{sv.name} is already globally declared as a {thing}. '
                              'shadowing global declarations is not allowed.')
        if sv.sort is None:
            sv.sort = SortInferencePlaceholder(sv)
        else:
            assert not isinstance(sv.sort, SortInferencePlaceholder)
            typecheck_sort(scope, sv.sort)

def post_typecheck_binder(binder: syntax.Binder) -> None:
    for sv in binder.vs:
        if isinstance(sv.sort, SortInferencePlaceholder):
            utils.print_error(sv.span, 'Could not infer sort for variable %s' % (sv.name,))


# typecheck expression and destructively infer types for bound variables.
#
# NOTE(typechecking-malformed-programs)
# mypyvy tries to report as many useful errors as possible about the input program during
# resolution, by continuing after the point where the first error is detected. This
# introduces subtleties in the typechecker where some invariants are established only assuming
# no errors have been detected so far. As a rule, if the typechecker does not exit/return
# after detecting an invariant violation, then that invariant should not be relied upon
# elsewhere in the typechecker without first asserting that the program is error free.
# After the typechecker is run, mypyvy exits if any errors are detected, so any other parts
# of mypyvy can assume all invariants established by the typechecker.
def typecheck_expr(scope: syntax.Scope, e: syntax.Expr, sort: InferenceSort) -> InferenceSort:
    if isinstance(e, syntax.Bool):
        check_constraint(e.span, sort, BoolSort)
        return BoolSort
    elif isinstance(e, syntax.Int):
        check_constraint(e.span, sort, IntSort)
        return IntSort
    elif isinstance(e, syntax.UnaryExpr):
        if e.op == 'NEW':
            if not scope.new_allowed():
                utils.print_error(e.span, f'new is not allowed here because this is a {scope.num_states}-state '
                                  f'environment, and the current state index is {scope.current_state_index}')
            with scope.next_state_index():
                return typecheck_expr(scope, e.arg, sort)
        elif e.op == 'NOT':
            check_constraint(e.span, sort, BoolSort)
            typecheck_expr(scope, e.arg, BoolSort)
            return BoolSort
        else:
            assert False
    elif isinstance(e, syntax.BinaryExpr):
        ans: InferenceSort = None
        if e.op in ['AND', 'OR', 'IMPLIES', 'IFF']:
            check_constraint(e.span, sort, BoolSort)
            typecheck_expr(scope, e.arg1, BoolSort)
            typecheck_expr(scope, e.arg2, BoolSort)
            ans = BoolSort
        elif e.op in ['EQUAL', 'NOTEQ']:
            check_constraint(e.span, sort, BoolSort)
            s = typecheck_expr(scope, e.arg1, None)
            typecheck_expr(scope, e.arg2, s)
            ans = BoolSort
        elif e.op in ['GE', 'GT', 'LE', 'LT']:
            check_constraint(e.span, sort, BoolSort)
            typecheck_expr(scope, e.arg1, IntSort)
            typecheck_expr(scope, e.arg2, IntSort)
            ans = BoolSort
        elif e.op in ['PLUS', 'SUB', 'MULT']:
            check_constraint(e.span, sort, IntSort)
            typecheck_expr(scope, e.arg1, IntSort)
            typecheck_expr(scope, e.arg2, IntSort)
            ans = IntSort
        else:
            assert False, e.op
        return ans
    elif isinstance(e, syntax.NaryExpr):
        check_constraint(e.span, sort, BoolSort)

        if e.op in ['AND', 'OR']:
            for arg in e.args:
                typecheck_expr(scope, arg, BoolSort)
        else:
            assert e.op == 'DISTINCT'
            s = None
            for arg in e.args:
                s = typecheck_expr(scope, arg, s)

        return BoolSort
    elif isinstance(e, syntax.AppExpr):
        d = scope.get(e.callee)
        if d is None:
            utils.print_error(e.span, 'Unresolved relation or function name %s' % e.callee)
            return sort  # bogus

        if not (isinstance(d, RelationDecl) or isinstance(d, FunctionDecl) or isinstance(d, DefinitionDecl)):
            utils.print_error(e.span, 'Only relations, functions, or definitions can be applied, not %s' %
                              (e.callee,))
            return sort  # bogus

        if isinstance(d, RelationDecl) or isinstance(d, FunctionDecl):
            if d.mutable and not scope.mutable_allowed():
                name = 'relation' if isinstance(d, RelationDecl) else 'function'
                utils.print_error(e.span,
                                  f'Only immutable {name}s can be referenced in this context, but {d.name} is mutable')
                # note that we don't return here. typechecking can continue.
                # see NOTE(typechecking-malformed-programs)
            elif e.n_new > 0:
                if not d.mutable:
                    utils.print_error(e.span, f'{d.name} is immutable but primed')
                if not scope.new_allowed(e.n_new):
                    if e.n_new == 1:
                        utils.print_error(e.span, f'{d.name} cannot be primed here')
                    else:
                        utils.print_error(e.span, f'{d.name} is primed too many timed here')

        if isinstance(d, DefinitionDecl) and not scope.call_allowed(d, e.n_new):
            if e.n_new > 0:
                prime_msg = f' with {e.n_new} primes'
            else:
                prime_msg = ''
            utils.print_error(e.span,
                              f'a {d.num_states}-state definition cannot be called{prime_msg} from a '
                              f'{scope.num_states}-state context inside {scope.current_state_index} nested new()s!')

        if not d.arity or len(e.args) != len(d.arity):
            utils.print_error(e.span, 'Callee applied to wrong number of arguments')
        for (arg, s) in zip(e.args, d.arity):
            typecheck_expr(scope, arg, s)

        if isinstance(d, RelationDecl):
            check_constraint(e.span, sort, BoolSort)
            return BoolSort
        else:
            sort = check_constraint(e.span, sort, d.sort)
            return sort
    elif isinstance(e, syntax.QuantifierExpr):
        check_constraint(e.span, sort, BoolSort)

        pre_typecheck_binder(scope, e.binder)

        with scope.in_scope(e.binder, [v.sort for v in e.binder.vs]):
            typecheck_expr(scope, e.body, BoolSort)

        post_typecheck_binder(e.binder)

        return BoolSort
    elif isinstance(e, syntax.Id):
        d = scope.get(e.name)

        if d is None:
            utils.print_error(e.span, 'Unresolved variable %s' % (e.name,))
            return sort  # bogus

        if isinstance(d, FunctionDecl):
            utils.print_error(e.span, 'Function %s must be applied to arguments' % (e.name,))
            return sort  # bogus

        if isinstance(d, RelationDecl) or isinstance(d, ConstantDecl):
            if d.mutable and not scope.mutable_allowed():
                name = 'relation' if isinstance(d, RelationDecl) else 'constant'
                utils.print_error(e.span, f'Only immutable {name}s can be referenced in this context')
                return sort  # bogus

            elif e.n_new > 0:
                if not d.mutable:
                    utils.print_error(e.span, f'{d.name} is immutable but primed')
                if not scope.new_allowed(e.n_new):
                    if e.n_new == 1:
                        utils.print_error(e.span, f'{d.name} cannot be primed here')
                    else:
                        utils.print_error(e.span, f'{d.name} is primed too many times here')

        if isinstance(d, RelationDecl):
            if d.arity:
                utils.print_error(e.span, 'Relation %s must be applied to arguments' % (e.name,))
                return sort  # bogus
            check_constraint(e.span, sort, BoolSort)
            return BoolSort
        elif isinstance(d, ConstantDecl):
            sort = check_constraint(e.span, sort, d.sort)
            return sort
        elif isinstance(d, DefinitionDecl):
            if d.arity:
                utils.print_error(e.span, 'Definition %s must be applied to arguments' % (e.name,))
                return sort  # bogus
            if not scope.call_allowed(d, e.n_new):
                if e.n_new > 0:
                    prime_msg = f' with {e.n_new} primes'
                else:
                    prime_msg = ''
                utils.print_error(e.span,
                                  f'a {d.num_states}-state definition cannot be called{prime_msg} from a '
                                  f'{scope.num_states}-state context inside {scope.current_state_index} nested new()s!')

            check_constraint(e.span, sort, d.sort)
            return BoolSort
        else:
            if e.n_new > 0:
                utils.print_error(e.span, f'{e.name} is a variable, but is primed here')

            vsort, = d
            vsort = check_constraint(e.span, sort, vsort)
            return vsort
    elif isinstance(e, syntax.IfThenElse):
        typecheck_expr(scope, e.branch, BoolSort)
        sort = typecheck_expr(scope, e.then, sort)
        return typecheck_expr(scope, e.els, sort)
    elif isinstance(e, syntax.Let):
        pre_typecheck_binder(scope, e.binder)

        typecheck_expr(scope, e.val, e.binder.vs[0].sort)

        with scope.in_scope(e.binder, [v.sort for v in e.binder.vs]):
            sort = typecheck_expr(scope, e.body, sort)

        post_typecheck_binder(e.binder)

        return sort
    else:
        assert False

def typecheck_sortdecl(scope: syntax.Scope, s: SortDecl) -> None:
    scope.add_sort(s)

def typecheck_sort(scope: syntax.Scope, s: Sort) -> None:
    if isinstance(s, syntax.UninterpretedSort):
        s.decl = scope.get_sort(s.name)
        if s.decl is None:
            utils.print_error(s.span, 'Unresolved sort name %s' % (s.name,))
    elif isinstance(s, (syntax._BoolSort, syntax._IntSort)):
        pass
    else:
        assert False

def typecheck_statedecl(scope: syntax.Scope, d: syntax.StateDecl) -> None:
    if isinstance(d, RelationDecl):
        for sort in d.arity:
            typecheck_sort(scope, sort)

        scope.add_relation(d)

        if d.derived_axiom:
            d.derived_axiom = syntax.close_free_vars(d.derived_axiom, span=d.span)
            with scope.n_states(1):
                typecheck_expr(scope, d.derived_axiom, BoolSort)
    elif isinstance(d, ConstantDecl):
        typecheck_sort(scope, d.sort)
        scope.add_constant(d)
    else:
        assert isinstance(d, FunctionDecl)
        for sort in d.arity:
            typecheck_sort(scope, sort)

        typecheck_sort(scope, d.sort)

        scope.add_function(d)

def typecheck_modifies_clause(scope: syntax.Scope, mod: syntax.ModifiesClause) -> None:
    d = scope.get(mod.name)
    assert d is None or isinstance(d, RelationDecl) or \
        isinstance(d, ConstantDecl) or isinstance(d, FunctionDecl)
    if d is None:
        utils.print_error(mod.span, 'Unresolved constant, relation, or function %s' % (mod.name,))
        return

    if not d.mutable:
        utils.print_error(mod.span, f'Immutable symbols may not appear in a modifies clause ({mod.name} is immutable)')

def typecheck_declcontainingexpr(scope: syntax.Scope, d: syntax.DeclContainingExpr) -> None:
    if isinstance(d, syntax.InitDecl):
        d.expr = syntax.close_free_vars(d.expr, span=d.span)
        with scope.n_states(1):
            typecheck_expr(scope, d.expr, BoolSort)

        if syntax.symbols_used(scope, d.expr) == set():
            utils.print_warning(d.span, 'this initial condition mentions no mutable symbols. '
                                'it should be declared `axiom` instead.')
    elif isinstance(d, syntax.InvariantDecl):
        d.expr = syntax.close_free_vars(d.expr, span=d.span)
        with scope.n_states(1):
            typecheck_expr(scope, d.expr, BoolSort)

        if syntax.symbols_used(scope, d.expr) == set():
            utils.print_error(d.span, 'this invariant mentions no mutable symbols. it can be deleted.')
    elif isinstance(d, syntax.AxiomDecl):
        d.expr = syntax.close_free_vars(d.expr, span=d.span)
        typecheck_expr(scope, d.expr, BoolSort)
    elif isinstance(d, syntax.TheoremDecl):
        d.expr = syntax.close_free_vars(d.expr, span=d.span)
        with scope.n_states(d.num_states):
            typecheck_expr(scope, d.expr, BoolSort)
    elif isinstance(d, DefinitionDecl):
        assert len(scope.stack) == 0

        old_error_count = 0

        pre_typecheck_binder(scope, d.binder)

        for mod in d.mods:
            typecheck_modifies_clause(scope, mod)

        d.expr = syntax.close_free_vars(d.expr, in_scope=[v.name for v in d.binder.vs], span=d.span,)

        with scope.in_scope(d.binder, [v.sort for v in d.binder.vs]):
            with scope.n_states(d.num_states):
                typecheck_expr(scope, d.expr, BoolSort)

        post_typecheck_binder(d.binder)

        if utils.error_count > old_error_count:
            return

        if d.is_public_transition:  # which implies num_states == 2, as checked in __init__
            with scope.in_scope(d.binder, [v.sort for v in d.binder.vs]):
                syms = syntax.symbols_used(scope, d.expr)
                for index, spans, sym in syms:
                    if index == 1:
                        for mod in d.mods:
                            if mod.name == sym:
                                break
                        else:
                            decl = scope.get(sym)
                            assert decl is not None
                            if not (isinstance(decl, RelationDecl) and decl.is_derived()):
                                if len(spans) == 1:
                                    utils.print_error(spans[0], 'symbol %s is referred to in the new state, '
                                                      'but is not mentioned in the modifies clause' % (sym,))
                                else:
                                    utils.print_error(spans[0], 'this call indirectly refers to symbol %s in the new '
                                                      'state, but is not mentioned in the modifies clause' % (sym,))
                                    for span in spans[1:-1]:
                                        utils.print_info(span, 'symbol %s is referred to via a call-chain passing '
                                                         'through this point' % (sym,))
                                    utils.print_info(spans[-1], 'symbol %s is referred to here' % (sym,))

                for mod in d.mods:
                    decl = scope.get(mod.name)
                    assert decl is not None
                    if isinstance(decl, RelationDecl) and decl.is_derived():
                        utils.print_error(mod.span, 'derived relation %s may not be mentioned by the modifies clause, '
                                          'since derived relations are always modified' % (mod.name,))
                        continue
                    for index, _, sym in syms:
                        if mod.name == sym and index == 1:
                            break
                    else:
                        utils.print_error(mod.span, 'symbol %s is mentioned by the modifies clause, but is not '
                                          'referred to in the new state, so it will be havoced. supress this error by '
                                          'using %s in a no-op.' % (mod.name, mod.name))

    else:
        assert False

def typecheck_tracedecl(scope: syntax.Scope, d: syntax.TraceDecl) -> None:
    for c in d.components:
        if isinstance(c, syntax.AssertDecl):
            if c.expr is not None:
                c.expr = syntax.close_free_vars(c.expr, span=c.span)
                with scope.n_states(1):
                    typecheck_expr(scope, c.expr, BoolSort)
        elif isinstance(c, syntax.TraceTransitionDecl):
            te = c.transition
            if isinstance(te, syntax.AnyTransition):
                pass
            elif isinstance(te, syntax.TransitionCalls):
                for tc in te.calls:
                    ition = scope.get_definition(tc.target)
                    if ition is None:
                        utils.print_error(tc.span, 'could not find transition %s' % (tc.target,))
                        return

                    if tc.args is not None:
                        if len(tc.args) != len(ition.binder.vs):
                            utils.print_error(
                                tc.span,
                                'transition applied to wrong number of arguments (expected %s, got %s)' %
                                (len(ition.binder.vs), len(tc.args)))
                            return

                        for a, sort in zip(tc.args, (v.sort for v in ition.binder.vs)):
                            if not isinstance(a, syntax.Star):
                                with scope.n_states(1):
                                    typecheck_expr(scope, a, sort)
            else:
                assert False
        else:
            assert False


def typecheck_program_vocab(prog: syntax.Program) -> None:
    prog.scope = scope = syntax.Scope[InferenceSort]()

    for s in prog.sorts():
        typecheck_sortdecl(scope, s)

    for rcf in prog.relations_constants_and_functions():
        typecheck_statedecl(scope, rcf)

    for d in prog.definitions():
        scope.add_definition(d)

def typecheck_program(prog: syntax.Program) -> None:
    typecheck_program_vocab(prog)

    for d in prog.decls_containing_exprs():
        typecheck_declcontainingexpr(prog.scope, d)

    for tr in prog.traces():
        typecheck_tracedecl(prog.scope, tr)

    assert len(prog.scope.stack) == 0
