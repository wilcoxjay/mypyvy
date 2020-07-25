import ply
import ply.lex
import ply.yacc
import syntax
import utils
from typing import Any, List, Optional, overload, Sequence, Tuple, Union

reserved = {
    'modifies': 'MODIFIES',
    'sort': 'SORT',
    'mutable': 'MUTABLE',
    'immutable': 'IMMUTABLE',
    'derived': 'DERIVED',
    'relation': 'RELATION',
    'constant': 'CONSTANT',
    'function': 'FUNCTION',
    'init': 'INIT',
    'transition': 'TRANSITION',
    'invariant': 'INVARIANT',
    'sketch': 'SKETCH',
    'axiom': 'AXIOM',
    'new': 'NEW',
    'old': 'OLD',
    'forall': 'FORALL',
    'exists': 'EXISTS',
    'true': 'TRUE',
    'false': 'FALSE',
    'zerostate': 'ZEROSTATE',
    'onestate': 'ONESTATE',
    'twostate': 'TWOSTATE',
    'theorem': 'THEOREM',
    'definition': 'DEFINITION',
    'assert': 'ASSERT',
    'safety': 'SAFETY',
    'any': 'ANY',
    'trace': 'TRACE',
    'if': 'IF',
    'then': 'THEN',
    'else': 'ELSE',
    'let': 'LET',
    'in': 'IN',
    'sat': 'SAT',
    'unsat': 'UNSAT',
    'distinct': 'DISTINCT',
    'bool': 'BOOL',
    'int': 'INT',
}

tokens = [
    'LPAREN',
    'RPAREN',
    'LBRACKET',
    'RBRACKET',
    'LBRACE',
    'RBRACE',
    'DOT',
    'COLON',
    'BANG',
    'TILDE',
    'IFF',
    'IMPLIES',
    'PIPE',
    'EQUAL',
    'NOTEQ',
    'NOTEQ2',
    'GE',
    'GT',
    'LE',
    'LT',
    'PLUS',
    'SUB',
    'COMMA',
    'AMPERSAND',
    'STAR',
    'ANNOT',
    'ID',
    'INTLIT'
] + list(reserved.values())


def t_ID(t: Any) -> Any:
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'ID')    # Check for reserved words
    return t

def t_ANNOT(t: Any) -> Any:
    r'@[-a-zA-Z_0-9]+'
    return t

def t_INTLIT(t: Any) -> Any:
    r'[0-9]+'
    return t

t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACKET = r'\['
t_RBRACKET = r'\]'
t_LBRACE = r'{'
t_RBRACE = r'}'
t_DOT = r'\.'
t_COLON = r':'
t_BANG = r'\!'
t_TILDE = r'~'
t_IMPLIES = r'->'
t_IFF = r'<->'
t_PIPE = r'\|'
t_EQUAL = r'='
t_NOTEQ = r'\!='
t_NOTEQ2 = r'~='
t_GE = r'>='
t_GT = r'>'
t_LE = r'<='
t_LT = r'<'
t_PLUS = r'\+'
t_SUB = r'-'
t_COMMA = r','
t_AMPERSAND = r'&'
t_STAR = r'\*'
t_ignore_COMMENT = r'\#.*'

Token = ply.lex.LexToken
Span = Tuple[Token, Token]
Location = Union[Token, Span]

# Define a rule so we can track line numbers
def t_newline(t: Token) -> None:
    r'\n+'
    t.lexer.lineno += len(t.value)
    t.lexer.bol = t.lexer.lexpos - 1

t_ignore = ' \t'

def t_error(t: Any) -> None:
    utils.print_error(t, 'lexical error near %s' % t.value[0])
    t.lexer.skip(1)

lexer = None
def get_lexer(forbid_rebuild: bool = False) -> ply.lex.Lexer:
    global lexer
    if not lexer:
        lexer = ply.lex.lex(debug=False, forbid_rebuild=forbid_rebuild)
    return lexer

precedence = (
    ('right', 'DOT'),
    ('nonassoc', 'ELSE'),
    ('nonassoc', 'IN'),
    ('nonassoc', 'IFF'),
    ('right', 'IMPLIES'),
    ('left', 'PIPE'),
    ('left', 'AMPERSAND'),
    ('nonassoc', 'EQUAL', 'NOTEQ', 'NOTEQ2', 'GE', 'GT', 'LE', 'LT'),
    ('left', 'PLUS', 'SUB'),
    ('right', 'BANG', 'TILDE')
)

# NOTE: assumes list is sorted by lexpos
def loc_list(locs: Sequence[Optional[Location]]) -> Optional[Span]:
    l: Optional[Token] = None
    for loc in locs:
        if loc is not None:
            l = span_from_loc(loc)[0]
            break
    r: Optional[Token] = None
    for loc in reversed(locs):
        if loc is not None:
            r = span_from_loc(loc)[1]
            break
    if l is not None:
        if r is not None:
            return l, r
        else:
            return span_from_tok(l)
    else:
        if r is not None:
            return span_from_tok(r)
        else:
            return None

def p_program(p: Any) -> None:
    'program : decls'
    decls: List[syntax.Decl] = p[1]
    p[0] = syntax.Program(decls)

def p_decls_empty(p: Any) -> None:
    'decls : empty'
    p[0] = []

def p_decls_decl(p: Any) -> None:
    'decls : decls decl'
    p[0] = p[1] + [p[2]]

def p_id(p: Any) -> None:
    'id : ID'
    p[0] = p.slice[1]

def p_optional_annotation_args_empty(p: Any) -> None:
    'optional_annotation_args : empty'
    p[0] = (None, [])

def p_optional_annotation_args_nonempty(p: Any) -> None:
    'optional_annotation_args : LPAREN annotation_args RPAREN'
    p[0] = ((p.slice[1], p.slice[3]), p[2])

def p_annotation_args_one(p: Any) -> None:
    'annotation_args : id'
    p[0] = [p[1].value]

def p_annotation_args_more(p: Any) -> None:
    'annotation_args : annotation_args COMMA id'
    p[0] = p[1] + [p[3].value]

@overload
def span_from_loc(loc: Location) -> Span:
    ...
@overload
def span_from_loc(loc: Optional[Location]) -> Optional[Span]:
    ...
def span_from_loc(loc: Optional[Location]) -> Optional[Span]:
    if isinstance(loc, Token):
        return span_from_tok(loc)
    return loc

def span_from_tok(tok: Token) -> Span:
    return (tok, tok)

def tok_min(t1: Token, t2: Token) -> Token:
    if t1.lexpos <= t2.lexpos:
        return t1
    else:
        return t2

def tok_max(t1: Token, t2: Token) -> Token:
    if t1.lexpos >= t2.lexpos:
        return t1
    else:
        return t2

@overload
def loc_join(s1: Optional[Location], s2: Location) -> Span:
    ...
@overload
def loc_join(s1: Location, s2: Optional[Location]) -> Span:
    ...
@overload
def loc_join(s1: Optional[Location], s2: Optional[Location]) -> Optional[Span]:
    ...
def loc_join(s1: Optional[Location], s2: Optional[Location]) -> Optional[Span]:
    s1 = span_from_loc(s1)
    s2 = span_from_loc(s2)
    if s1 is None:
        return s2
    if s2 is None:
        return s1

    return tok_min(s1[0], s2[0]), tok_max(s1[1], s2[1])

def p_annotation(p: Any) -> None:
    'annotation : ANNOT optional_annotation_args'
    annot: str = p[1]
    args_span: Optional[Span]
    args: List[str]
    args_span, args = p[2]
    span: Span = loc_join(p.slice[1], args_span)
    p[0] = syntax.Annotation(span, annot[1:], args)

def p_annotations_empty(p: Any) -> None:
    'annotations : empty'
    p[0] = []

def p_annotations_one(p: Any) -> None:
    'annotations : annotations annotation'
    p[0] = p[1] + [p[2]]

def p_decl_sort(p: Any) -> None:
    'decl : SORT id annotations'
    start_tok: Token = p.slice[1]
    name_tok: Token = p[2]
    name: str = name_tok.value
    annots: List[syntax.Annotation] = p[3]
    toks: List[Optional[Location]] = [start_tok, name_tok]
    span = loc_list(toks + [a.span for a in annots])
    p[0] = syntax.SortDecl(name, annots, span=span)

def p_decl_mut(p: Any) -> None:
    '''mut : MUTABLE
           | IMMUTABLE'''
    p[0] = (p.slice[1], p[1] == 'mutable')

def p_arity_empty(p: Any) -> None:
    'arity : empty'
    p[0] = (None, [])

def p_arity_paren_empty(p: Any) -> None:
    'arity : LPAREN RPAREN'
    p[0] = ((p.slice[1], p.slice[2]), [])

def p_arity_nonempty(p: Any) -> None:
    'arity : LPAREN arity_nonempty RPAREN'
    p[0] = ((p.slice[1], p.slice[3]), p[2])

def p_arity_nonempty_one(p: Any) -> None:
    'arity_nonempty : sort'
    p[0] = [p[1]]

def p_arity_nonempty_more(p: Any) -> None:
    'arity_nonempty : arity_nonempty COMMA sort'
    p[0] = p[1] + [p[3]]

def p_sort_bool(p: Any) -> None:
    'sort : BOOL'
    tok: Token = p.slice[1]
    p[0] = syntax._BoolSort(span=span_from_tok(tok))

def p_sort_int(p: Any) -> None:
    'sort : INT'
    tok: Token = p.slice[1]
    p[0] = syntax._IntSort(span=span_from_tok(tok))

def p_sort_uninterp(p: Any) -> None:
    'sort : id'
    tok: Token = p[1]
    p[0] = syntax.UninterpretedSort(tok.value, span=span_from_tok(tok))

def p_decl_relation(p: Any) -> None:
    'decl : mut RELATION id arity annotations'
    start_tok: Token
    is_mut: bool
    arity_span: Optional[Span]
    arity: List[syntax.Sort]

    start_tok, is_mut = p[1]
    name_tok: Token = p[3]
    arity_span, arity = p[4]
    annots: List[syntax.Annotation] = p[5]

    span = loc_list([start_tok, name_tok, arity_span] + [a.span for a in annots])

    p[0] = syntax.RelationDecl(name_tok.value, arity, mutable=is_mut, derived=None,
                               annotations=annots, span=span)

def p_decl_relation_derived(p: Any) -> None:
    'decl : DERIVED RELATION id arity annotations COLON expr'
    start_tok: Token = p.slice[1]
    name_tok: Token = p[3]
    arity_span: Optional[Span]
    arity: List[syntax.Sort]
    arity_span, arity = p[4]
    annots: List[syntax.Annotation] = p[5]
    derived_defn: syntax.Expr = p[7]

    p[0] = syntax.RelationDecl(name_tok.value, arity, mutable=True, derived=derived_defn,
                               annotations=annots, span=loc_join(start_tok, derived_defn.span))

def p_constant_decl(p: Any) -> None:
    'constant_decl : mut CONSTANT id COLON sort annotations'
    start_tok: Token
    is_mut: bool
    start_tok, is_mut = p[1]
    name_tok: Token = p[3]
    sort: syntax.UninterpretedSort = p[5]
    annots: List[syntax.Annotation] = p[6]
    span = loc_join(start_tok, loc_list([sort.span] + [a.span for a in annots]))
    p[0] = syntax.ConstantDecl(name_tok.value, sort, is_mut, annots, span=span)

def p_decl_constant_decl(p: Any) -> None:
    'decl : constant_decl'
    p[0] = p[1]

def p_decl_function(p: Any) -> None:
    'decl : mut FUNCTION id LPAREN arity_nonempty RPAREN COLON sort annotations'
    start_tok: Token
    is_mut: bool
    start_tok, is_mut = p[1]
    name_tok = p[3]
    arity: List[syntax.Sort] = p[5]
    sort: syntax.UninterpretedSort = p[8]
    annots: List[syntax.Annotation] = p[9]
    span = loc_join(start_tok, loc_list([sort.span] + [a.span for a in annots]))
    p[0] = syntax.FunctionDecl(name_tok.value, arity, sort, is_mut, annots, span=span)

def p_axiom_decl(p: Any) -> None:
    'axiom_decl : AXIOM opt_name expr'
    name: Optional[str] = p[2]
    expr: syntax.Expr = p[3]
    span = loc_join(p.slice[1], expr.span)
    p[0] = syntax.AxiomDecl(name, expr, span=span)

def p_decl_axiom_decl(p: Any) -> None:
    'decl : axiom_decl'
    p[0] = p[1]

def p_decl_init(p: Any) -> None:
    'decl : INIT opt_name expr'
    name: Optional[str] = p[2]
    expr: syntax.Expr = p[3]
    span = loc_join(p.slice[1], expr.span)
    p[0] = syntax.InitDecl(name, expr, span=span)

def p_safety_or_invariant_keyword_safety(p: Any) -> None:
    'safety_or_invariant_keyword : SAFETY'
    p[0] = (p.slice[1], True, False)

def p_safety_or_invariant_keyword_invariant(p: Any) -> None:
    'safety_or_invariant_keyword : INVARIANT'
    p[0] = (p.slice[1], False, False)

def p_safety_or_invariant_keyword_sketch_invariant(p: Any) -> None:
    'safety_or_invariant_keyword : SKETCH INVARIANT'
    p[0] = (p.slice[1], False, True)

def p_invariant_decl(p: Any) -> None:
    'invariant_decl : safety_or_invariant_keyword opt_name expr'
    tok: Token
    is_safety: bool
    is_sketch: bool
    tok, is_safety, is_sketch = p[1]
    opt_name: Optional[str] = p[2]
    expr: syntax.Expr = p[3]
    span = loc_join(tok, expr.span)
    p[0] = syntax.InvariantDecl(opt_name, expr, is_safety, is_sketch, span=span)

def p_decl_invariant(p: Any) -> None:
    'decl : invariant_decl'
    p[0] = p[1]

def p_opt_name_none(p: Any) -> None:
    'opt_name : empty'
    pass

def p_opt_name_some(p: Any) -> None:
    'opt_name : LBRACKET id RBRACKET'
    p[0] = p[2].value

def p_quant(p: Any) -> None:
    '''quant : FORALL
             | EXISTS'''
    p[0] = p.slice[1]

def p_expr_quantifier(p: Any) -> None:
    'expr : quant sortedvars DOT expr'
    quant_tok: Token = p[1]
    svs: List[syntax.SortedVar] = p[2]
    expr: syntax.Expr = p[4]
    span = loc_join(quant_tok, expr.span)
    p[0] = syntax.QuantifierExpr(quant_tok.type, svs, expr, span=span)

def p_sortedvar(p: Any) -> None:
    'sortedvar : id COLON sort'
    id_tok: Token = p[1]
    sort: syntax.UninterpretedSort = p[3]
    p[0] = syntax.SortedVar(id_tok.value, sort, span=loc_join(id_tok, sort.span))

def p_sortedvar_nosort(p: Any) -> None:
    'sortedvar : id'
    id_tok: Token = p[1]
    p[0] = syntax.SortedVar(id_tok.value, None, span=span_from_tok(id_tok))

def p_sortedvars0_one(p: Any) -> None:
    'sortedvars0 : sortedvars'
    p[0] = p[1]

def p_sortedvars0_zero(p: Any) -> None:
    'sortedvars0 : empty'
    p[0] = []

def p_sortedvars_one(p: Any) -> None:
    'sortedvars : sortedvar'
    p[0] = [p[1]]

def p_sortedvars_more(p: Any) -> None:
    'sortedvars : sortedvars COMMA sortedvar'
    p[0] = p[1] + [p[3]]

def p_expr_intlit(p: Any) -> None:
    'expr : INTLIT'
    p[0] = syntax.Int(int(p[1]), span=span_from_tok(p.slice[1]))

def p_expr_true(p: Any) -> None:
    'expr : TRUE'
    p[0] = syntax.Bool(True, span=span_from_tok(p.slice[1]))

def p_expr_false(p: Any) -> None:
    'expr : FALSE'
    p[0] = syntax.Bool(False, span=span_from_tok(p.slice[1]))

def p_expr_not(p: Any) -> None:
    '''expr : BANG expr
            | TILDE expr'''
    expr: syntax.Expr = p[2]
    p[0] = syntax.UnaryExpr('NOT', expr, span=loc_join(p.slice[1], expr.span))

def p_expr_app(p: Any) -> None:
    'expr : id LPAREN args RPAREN'
    callee_tok = p[1]
    args: List[syntax.Expr] = p[3]
    p[0] = syntax.AppExpr(callee_tok.value, args, span=loc_join(callee_tok, p.slice[4]))

def p_expr_and1(p: Any) -> None:
    'expr : AMPERSAND expr'
    p[0] = p[2]

def p_expr_and(p: Any) -> None:
    'expr : expr AMPERSAND expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    if isinstance(l, syntax.NaryExpr) and l.op == 'AND':
        l.args.append(r)
        l.span = loc_join(l.span, r.span)
        p[0] = l
    else:
        span = loc_join(l.span, r.span)
        p[0] = syntax.NaryExpr('AND', [l, r], span=span)

def p_expr_or1(p: Any) -> None:
    'expr : PIPE expr'
    p[0] = p[2]

def p_expr_or(p: Any) -> None:
    'expr : expr PIPE expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    if isinstance(l, syntax.NaryExpr) and l.op == 'OR':
        l.args.append(p[3])
        l.span = loc_join(l.span, r.span)
        p[0] = l
    else:
        span = loc_join(l.span, r.span)
        p[0] = syntax.NaryExpr('OR', [l, r], span=span)

def p_expr_distinct(p: Any) -> None:
    'expr : DISTINCT LPAREN args1 RPAREN'
    p[0] = syntax.NaryExpr('DISTINCT', p[3], span=loc_join(p.slice[1], p.slice[4]))

def p_expr_iff(p: Any) -> None:
    'expr : expr IFF expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('IFF', l, r, span=span)

def p_expr_implies(p: Any) -> None:
    'expr : expr IMPLIES expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('IMPLIES', l, r, span=span)

def p_expr_eq(p: Any) -> None:
    'expr : expr EQUAL expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('EQUAL', l, r, span=span)

def p_expr_noteq(p: Any) -> None:
    '''expr : expr NOTEQ expr
            | expr NOTEQ2 expr'''
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('NOTEQ', l, r, span=span)

def p_expr_ge(p: Any) -> None:
    'expr : expr GE expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('GE', l, r, span=span)

def p_expr_gt(p: Any) -> None:
    'expr : expr GT expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('GT', l, r, span=span)

def p_expr_le(p: Any) -> None:
    'expr : expr LE expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('LE', l, r, span=span)

def p_expr_lt(p: Any) -> None:
    'expr : expr LT expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('LT', l, r, span=span)

def p_expr_plus(p: Any) -> None:
    'expr : expr PLUS expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('PLUS', l, r, span=span)

def p_expr_sub(p: Any) -> None:
    'expr : expr SUB expr'
    l: syntax.Expr = p[1]
    r: syntax.Expr = p[3]
    span = loc_join(l.span, r.span)
    p[0] = syntax.BinaryExpr('SUB', l, r, span=span)


def p_expr_old(p: Any) -> None:
    'expr : OLD LPAREN expr RPAREN'
    e: syntax.Expr = p[3]
    p[0] = syntax.UnaryExpr('OLD', e, span=loc_join(p.slice[1], p.slice[4]))

def p_expr_new(p: Any) -> None:
    'expr : NEW LPAREN expr RPAREN'
    e: syntax.Expr = p[3]
    p[0] = syntax.UnaryExpr('NEW', e, span=loc_join(p.slice[1], p.slice[4]))


def p_args_empty(p: Any) -> None:
    'args : empty'
    p[0] = []

def p_args_at_least_one(p: Any) -> None:
    'args : args1'
    p[0] = p[1]

def p_args1_one(p: Any) -> None:
    'args1 : expr'
    p[0] = [p[1]]

def p_args1_more(p: Any) -> None:
    'args1 : args1 COMMA expr'
    p[0] = p[1] + [p[3]]

def p_expr_id(p: Any) -> None:
    'expr : id'
    id_tok: Token = p[1]
    p[0] = syntax.Id(id_tok.value, span=span_from_tok(id_tok))

def p_expr_paren(p: Any) -> None:
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_expr_if(p: Any) -> None:
    'expr : IF expr THEN expr ELSE expr'
    branch: syntax.Expr = p[2]
    then: syntax.Expr = p[4]
    els: syntax.Expr = p[6]
    p[0] = syntax.IfThenElse(branch, then, els, span=loc_join(p.slice[1], els.span))

def p_expr_let(p: Any) -> None:
    'expr : LET sortedvar EQUAL expr IN expr'
    sv: syntax.SortedVar = p[2]
    val: syntax.Expr = p[4]
    body: syntax.Expr = p[6]
    p[0] = syntax.Let(sv, val, body, span=loc_join(p.slice[1], body.span))

def p_params(p: Any) -> None:
    'params : sortedvars0'
    p[0] = p[1]

def p_mod(p: Any) -> None:
    'mod : id'
    id_tok: Token = p[1]
    p[0] = syntax.ModifiesClause(id_tok.value, span=span_from_tok(id_tok))

def p_modlist_one(p: Any) -> None:
    'modlist : mod'
    p[0] = [p[1]]

def p_modlist_more(p: Any) -> None:
    'modlist : modlist COMMA mod'
    p[0] = p[1] + [p[3]]

def p_mods(p: Any) -> None:
    'mods : MODIFIES modlist'
    p[0] = p[2]

def p_decl_transition(p: Any) -> None:
    'decl : TRANSITION id LPAREN params RPAREN definition_body'
    id_tok: Token = p[2]
    mods: List[syntax.ModifiesClause]
    expr: syntax.Expr
    mods, expr = p[6]
    p[0] = syntax.DefinitionDecl(is_public_transition=True, num_states=2, name=id_tok.value,
                                 params=p[4], mods=mods, expr=expr,
                                 span=loc_join(p.slice[1], expr.span))

def p_decl_definition_body_mods_expr(p: Any) -> None:
    'definition_body : mods expr'
    p[0] = (p[1], p[2])

def p_decl_definition_body_expr(p: Any) -> None:
    'definition_body : EQUAL expr'
    p[0] = ([], p[2])

def kstate_int(kstate: str) -> int:
    if kstate == 'zerostate':
        return 0
    elif kstate == 'onestate' or kstate is None:
        return 1
    elif kstate == 'twostate':
        return 2
    else:
        assert False, kstate

def p_kstate(p: Any) -> None:
    '''kstate : ZEROSTATE
              | ONESTATE
              | TWOSTATE
              | empty'''
    tok: Optional[Token] = p.slice[1]
    if tok is not None and tok.type == 'empty':
        tok = None
    p[0] = (tok, kstate_int(p[1]))

def p_decl_theorem(p: Any) -> None:
    'decl : kstate THEOREM opt_name expr'
    k_tok, k_int = p[1]
    expr: syntax.Expr = p[4]
    p[0] = syntax.TheoremDecl(p[3], expr, num_states=k_int,
                              span=loc_join(k_tok, loc_join(p.slice[2], expr.span)))

def p_decl_definition(p: Any) -> None:
    'decl : kstate DEFINITION id LPAREN params RPAREN definition_body'
    k_tok, num_states = p[1]
    mods: List[syntax.ModifiesClause]
    expr: syntax.Expr
    mods, expr = p[7]

    if num_states != 2 and mods:
        utils.print_error(mods[0].span,
                          "syntax error: modifies clause only allowed on twostate definitions or transitions")
        return

    p[0] = syntax.DefinitionDecl(is_public_transition=False, num_states=num_states,
                                 name=p[3].value, params=p[5], mods=mods, expr=expr,
                                 span=loc_join(k_tok, loc_join(p.slice[2], expr.span)))

def p_trace_transition_any(p: Any) -> None:
    'trace_transition : ANY TRANSITION'
    p[0] = syntax.AnyTransition()

def p_optional_tcall_args_none(p: Any) -> None:
    'optional_tcall_args : empty'
    p[0] = (None, None)

def p_tcall_args_empty(p: Any) -> None:
    'tcall_args : empty'
    p[0] = []

def p_tcall_args_nonempty(p: Any) -> None:
    'tcall_args : tcall_args1'
    p[0] = p[1]

def p_tcall_arg_star(p: Any) -> None:
    'tcall_arg : STAR'
    p[0] = syntax.Star()

def p_tcall_arg_expr(p: Any) -> None:
    'tcall_arg : expr'
    p[0] = p[1]

def p_tcall_args1_arg(p: Any) -> None:
    'tcall_args1 : tcall_arg'
    p[0] = [p[1]]

def p_tcall_args1_more(p: Any) -> None:
    'tcall_args1 : tcall_args1 COMMA tcall_arg'
    p[0] = p[1] + [p[3]]

def p_optional_tcall_args_some(p: Any) -> None:
    'optional_tcall_args : LPAREN tcall_args RPAREN'
    p[0] = ((p.slice[1], p.slice[3]), p[2])

def p_trace_transition_calls(p: Any) -> None:
    'trace_transition : trace_transition_calls'
    p[0] = syntax.TransitionCalls(p[1])

def p_trace_transition_calls_one(p: Any) -> None:
    'trace_transition_calls : trace_transition_call'
    p[0] = [p[1]]

def p_trace_transition_calls_more(p: Any) -> None:
    'trace_transition_calls : trace_transition_calls PIPE trace_transition_call'
    p[0] = p[1] + [p[3]]

def p_trace_transition_call(p: Any) -> None:
    'trace_transition_call : ID optional_tcall_args'
    args_span, args = p[2]
    p[0] = syntax.TransitionCall(p[1], args, span=loc_join(p.slice[1], args_span))

def p_trace_component_assert(p: Any) -> None:
    'trace_component : ASSERT expr'
    expr: syntax.Expr = p[2]
    p[0] = syntax.AssertDecl(expr, span=loc_join(p.slice[1], expr.span))

def p_trace_component_assert_init(p: Any) -> None:
    'trace_component : ASSERT INIT'
    p[0] = syntax.AssertDecl(None, span=(p.slice[1], p.slice[2]))

def p_trace_component_transition(p: Any) -> None:
    'trace_component : trace_transition'
    p[0] = syntax.TraceTransitionDecl(p[1])

def p_trace_components_empty(p: Any) -> None:
    'trace_components : empty'
    p[0] = []

def p_trace_components_component(p: Any) -> None:
    'trace_components : trace_components trace_component'
    p[0] = p[1] + [p[2]]

def p_satunsat(p: Any) -> None:
    '''satunsat : SAT
                | UNSAT'''
    p[0] = p.slice[1]

def p_decl_trace(p: Any) -> None:
    'decl : satunsat TRACE LBRACE trace_components RBRACE'
    satunsat_tok = p[1]
    p[0] = syntax.TraceDecl(p[4], sat=satunsat_tok.value == 'sat', span=loc_join(satunsat_tok, p.slice[5]))

def p_empty(p: Any) -> None:
    'empty :'
    pass

def p_error(t: Any) -> None:
    if t is not None:
        utils.print_error(t, 'syntax error near %s' % t.value)
    else:
        l = get_lexer(forbid_rebuild=True)
        assert l is not None
        t = ply.lex.LexToken()
        t.filename = l.filename
        t.lineno = l.lineno
        t.col = l.lexpos - l.bol
        utils.print_error(t, 'syntax error near EOF')

program_parser = None
def get_parser(forbid_rebuild: bool = False) -> ply.yacc.LRParser:
    global program_parser
    if not program_parser:
        # intentionally don's pass optimize=True here, because that disables the signature check
        program_parser = ply.yacc.yacc(start='program', debug=False)

    return program_parser


expr_parser = None
def get_expr_parser() -> ply.yacc.LRParser:
    global expr_parser
    if not expr_parser:
        expr_parser = ply.yacc.yacc(start='expr', debug=False, errorlog=ply.yacc.NullLogger())

    return expr_parser

def parse_expr(input: str) -> syntax.Expr:
    l = get_lexer()
    p = get_expr_parser()
    return p.parse(input=input, lexer=l, filename='<none>')
