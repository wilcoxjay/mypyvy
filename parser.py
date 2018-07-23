import ply
import ply.lex
import ply.yacc
import ast

reserved = {
    'modifies': 'MODIFIES',
    'sort': 'SORT',
    'mutable': 'MUTABLE',
    'relation': 'RELATION',
    'init': 'INIT',
    'transition': 'TRANSITION',
    'invariant': 'INVARIANT',
    'old': 'OLD',
    'modifies': 'MODIFIES',
    'forall': 'FORALL'
#    'exists': 'EXISTS'
}

tokens = [
    'LPAREN',
    'RPAREN',
    'LBRACKET',
    'RBRACKET',
    'DOT',
    'COLON',
    'BANG',
    'IFF',
    'IMPLIES',
    'PIPE',
    'EQUAL',
    'NOTEQ',
    'COMMA',
    'AMPERSAND',
    'ID'
] + list(reserved.values())


def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value,'ID')    # Check for reserved words
    return t

t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACKET = r'\['
t_RBRACKET = r'\]'
t_DOT = r'\.'
t_COLON = r':'
t_BANG = r'\!'
t_IMPLIES = r'->'
t_IFF = r'<->'
t_PIPE = r'\|'
t_EQUAL = r'='
t_NOTEQ = r'\!='
t_COMMA = r','
t_AMPERSAND = r'&'
t_ignore_COMMENT = r'\#.*'

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
    t.lexer.bol = t.lexpos

t_ignore  = ' \t'

def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

lexer = ply.lex.lex()


precedence = (
    ('right','DOT'),
    ('nonassoc','IFF'),
    ('right','IMPLIES'),
    ('left','PIPE'),
    ('left','AMPERSAND'),
    ('nonassoc', 'EQUAL', 'NOTEQ'),
    ('right','BANG')
)

def p_program(p):
    'program : decls'
    p[0] = ast.Program(p[1])

def p_decls_empty(p):
    'decls : empty'
    p[0] = []

def p_decls_decl(p):
    'decls : decls decl'
    p[0] = p[1] + [p[2]]

def p_id(p):
    'id : ID'
    p[0] = p.slice[1]

def p_decl_sort(p):
    'decl : SORT id'
    p[0] = ast.SortDecl(p[2])

def p_decl_mut_opt(p):
    '''mut_opt : MUTABLE
               | empty'''
    p[0] = p[1] == 'mutable'

def p_arity_empty(p):
    'arity : empty'
    p[0] = []

def p_arity_nonempty(p):
    'arity : arity_nonempty'
    p[0] = p[1]

def p_arity_nonempty_one(p):
    'arity_nonempty : sort'
    p[0] = [p[1]]

def p_arity_nonempty_more(p):
    'arity_nonempty : arity_nonempty COMMA sort'
    p[0] = p[1] + [p[3]]

def p_sort(p):
    'sort : id'
    p[0] = ast.UninterpretedSort(p[1])

def p_decl_relation(p):
    'decl : mut_opt RELATION id LPAREN arity RPAREN'
    p[0] = ast.RelationDecl(p[3], p[5], p[1])

def p_decl_init(p):
    'decl : INIT opt_name expr'
    p[0] = ast.InitDecl(p[2] or p.slice[1], p[3])

def p_decl_invariant(p):
    'decl : INVARIANT opt_name expr'
    p[0] = ast.InvariantDecl(p[2] or p.slice[1], p[3])

def p_opt_name_none(p):
    'opt_name : empty'
    pass

def p_opt_name_some(p):
    'opt_name : LBRACKET id RBRACKET'
    p[0] = p[2]

def p_expr_forall(p):
    'expr : FORALL sortedvars DOT expr'
    p[0] = ast.QuantifierExpr('FORALL', p[2], p[4])

def p_sortedvar(p):
    'sortedvar : id COLON sort'
    p[0] = ast.SortedVar(p[1], p[3])

def p_sortedvars0_one(p):
    'sortedvars0 : sortedvars'
    p[0] = p[1]

def p_sortedvars0_zero(p):
    'sortedvars0 : empty'
    p[0] = []

def p_sortedvars_one(p):
    'sortedvars : sortedvar'
    p[0] = [p[1]]

def p_sortedvars_more(p):
    'sortedvars : sortedvars COMMA sortedvar'
    p[0] = p[1] + [p[3]]

def p_expr_not(p):
    'expr : BANG expr'
    p[0] = ast.UnaryExpr('NOT', p[2])

def p_expr_app(p):
    'expr : id LPAREN args RPAREN'
    p[0] = ast.AppExpr(p[1], p[3])

def p_expr_and(p):
    'expr : expr AMPERSAND expr'
    p[0] = ast.BinaryExpr('AND', p[1], p[3])

def p_expr_or(p):
    'expr : expr PIPE expr'
    p[0] = ast.BinaryExpr('OR', p[1], p[3])

def p_expr_iff(p):
    'expr : expr IFF expr'
    p[0] = ast.BinaryExpr('IFF', p[1], p[3])
    
def p_expr_implies(p):
    'expr : expr IMPLIES expr'
    p[0] = ast.BinaryExpr('IMPLIES', p[1], p[3])

def p_expr_eq(p):
    'expr : expr EQUAL expr'
    p[0] = ast.BinaryExpr('EQUAL', p[1], p[3])

def p_expr_noteq(p):
    'expr : expr NOTEQ expr'
    p[0] = ast.BinaryExpr('NOTEQ', p[1], p[3])


def p_expr_old(p):
    'expr : OLD LPAREN expr RPAREN'
    p[0] = ast.UnaryExpr('OLD', p[3])

def p_args_empty(p):
    'args : empty'
    p[0] = []

def p_args_at_least_one(p):
    'args : args1'
    p[0] = p[1]

def p_args1_one(p):
    'args1 : expr'
    p[0] = [p[1]]

def p_args1_more(p):
    'args1 : args1 COMMA expr'
    p[0] = p[1] + [p[3]]

def p_expr_id(p):
    'expr : id'
    p[0] = ast.Id(p[1])

def p_expr_paren(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_params(p):
    'params : sortedvars0'
    p[0] = p[1]

def p_mod(p):
    'mod : id'
    p[0] = ast.ModifiesClause(p[1])

def p_modlist_one(p):
    'modlist : mod'
    p[0] = [p[1]]

def p_modlist_more(p):
    'modlist : modlist COMMA mod'
    p[0] = p[1] + [p[3]]

def p_mods(p):
    'mods : MODIFIES modlist'
    p[0] = p[2]

def p_decl_transition(p):
    'decl : TRANSITION id LPAREN params RPAREN mods expr'
    p[0] = ast.TransitionDecl(p[2], p[4], p[6], p[7])

def p_empty(p):
    'empty :'
    pass

def p_error(t):
    print '%s:%s syntax error at %s' % (t.lineno, t.lexpos - t.lexer.bol, t.value)

parser = ply.yacc.yacc()

