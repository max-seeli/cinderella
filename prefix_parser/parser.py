from typing import Union

import ply.lex as lex
import ply.yacc as yacc

tokens = (
    'PLUS', 'MINUS', 'TIMES', 'DIVIDE',
    'LPAREN', 'RPAREN', 'NUMBER'
)

t_PLUS = r'\+'
t_MINUS = r'-'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_ignore = ' \t\n'



def t_NUMBER(t):
    r'\d+(\.\d+)?'
    if '.' in t.value:
        t.value = float(t.value)
    else:
        t.value = int(t.value)
    return t

def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.lexer.skip(1)


lexer = lex.lex()


def p_expression(p):
    '''expression : LPAREN operator RPAREN
                  | LPAREN negative RPAREN
                  | NUMBER'''
    p[0] = p[1] if len(p) == 2 else p[2]


def p_operator(p):
    '''operator : PLUS expression expression
                | MINUS expression expression
                | TIMES expression expression
                | DIVIDE expression expression'''
    if p[1] == '+':
        p[0] = p[2] + p[3]
    elif p[1] == '-':
        p[0] = p[2] - p[3]
    elif p[1] == '*':
        p[0] = p[2] * p[3]
    elif p[1] == '/':
        p[0] = p[2] / p[3]
        

def p_negative(p):
    '''negative : MINUS expression'''
    p[0] = -p[2]


def p_error(p):
    print("Syntax error at '%s'" % p.value if p else "Syntax error at EOF")


def parse_expression(expression: str) -> Union[float, int]:
    """
    Parse the given expression.

    Parameters
    ----------
    expression : str
        The expression to be parsed.

    Returns
    -------
    Union[float, int]
        The result of the expression.
    """
    parser = yacc.yacc()
    return parser.parse(expression)
