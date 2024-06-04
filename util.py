import regex as re
import sympy as sp
import z3

def to_z3(expr: sp.Basic) -> z3.ExprRef:
    """
    Convert a SymPy expression to a Z3 expression.

    Parameters
    ----------
    expr : sp.Basic
        The SymPy expression to convert.

    Returns
    -------
    z3.ExprRef
        The Z3 expression.
    """
    if isinstance(expr, sp.LessThan):
        return to_z3(expr.lhs) <= to_z3(expr.rhs)
    elif isinstance(expr, sp.StrictLessThan):
        return to_z3(expr.lhs) < to_z3(expr.rhs)
    elif isinstance(expr, sp.GreaterThan):
        return to_z3(expr.lhs) >= to_z3(expr.rhs)
    elif isinstance(expr, sp.StrictGreaterThan):
        return to_z3(expr.lhs) > to_z3(expr.rhs)
    elif isinstance(expr, sp.Eq):
        return to_z3(expr.lhs) == to_z3(expr.rhs)
    elif isinstance(expr, sp.And):
        return z3.And([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Or):
        return z3.Or([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Not):
        return z3.Not(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Add):
        return z3.Sum([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Mul):
        return z3.Product([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Abs):
        return z3.Abs(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Pow):
        return to_z3(expr.base) ** to_z3(expr.exp)
    elif isinstance(expr, sp.Number):
        return z3.RealVal(expr)
    elif isinstance(expr, sp.UnevaluatedExpr):
        return to_z3(expr.args[0])
    elif isinstance(expr, sp.Symbol):
        return z3.Real(expr.name)
    elif isinstance(expr, sp.logic.boolalg.BooleanTrue):
        return z3.BoolVal(True)
    elif isinstance(expr, sp.logic.boolalg.BooleanFalse):
        return z3.BoolVal(False)
    else:
        raise ValueError(f'Unsupported expression type: {type(expr)}')

def inline_let_expressions(smt_code: str) -> str:
    """
    Inline all let expressions in the SMT code.

    Parameters
    ----------
    smt_code : str
        The SMT code to process.

    Returns
    -------
    str
        The SMT code with all let expressions inlined.
    """    
    # Match all "(assert ...)" expressions, regardless of the content
    matches = re.finditer(r'\(assert\s+((?:[^()]+|\((?1)\))*)\)', smt_code)

    final_smt_code = ""
    # For each match, inline the let expression
    for m in matches:
        
        if "let" not in m.group(1):
            final_smt_code += f"{m.group(0)}\n"
            continue

        # Extract the let expression by name
        lets = re.findall(r'\(let\s+\(((?:[^()]+|\((?1)\))*)\)', m.group(1))

        named_lets = {}
        for let in lets:
            # Extract the name of the let expression
            name_clause = re.finditer(r'\(([\?\$]\w+)\s+(\(((?:[^()]+|\((?3)\))*)\))', let)
            
            for nc in name_clause:
                name, expr = nc.group(1), nc.group(2)
                named_lets[name] = expr

        total_clause = re.search(r'\n\s+(\(=>\s+((?:[^()]+|\((?2)\))*)\))', m.group(1))
        final_smt_code += f"(assert \n {fill_expression(total_clause.group(1), named_lets)})\n"

    return final_smt_code

def fill_expression(expr: str, variables: dict) -> str:
    """
    Replace every variable in the expression with the corresponding expression from variables.

    Parameters
    ----------
    expr : str
        The expression to process.
    variables : dict
        A dictionary mapping variable names to their corresponding expressions.

    Returns
    -------
    str
        The expression with all variables replaced.
    """
    # Substitute every appearance of r'[\?\$]\w+' with the corresponding expression from variables
    while curr_var := re.search(r'[\?\$]\w+', expr):
        if curr_var.group() in variables:
            # Replace the match in the expression with the corresponding expression
            sub_expr = fill_expression(variables[curr_var.group()], variables)
            variables[curr_var.group()] = sub_expr
            # Replace from the start of the match to the end of the match
            expr = expr[:curr_var.start()] + sub_expr + expr[curr_var.end():]
        else:
            raise ValueError(f'Variable {curr_var.group()} not found in variables.')
    return expr

def format_smt2(smt2: str) -> str:
    """
    Format an SMT2 string to be more readable and suit the PolyHorn format.

    Parameters
    ----------
    smt2 : str
        The SMT2 string to format.

    Returns
    -------
    str
        The formatted SMT2 string.
    """
    # Convert all "(declare-fun <name> () Real)" to "(declare-const <name> Real)"
    declarations = re.search(r'(\(declare-fun [a-zA-Z0-9_]+ \(\) Real\)\s+)+', smt2).group()
    declarations = re.sub(r'\(declare-fun (\w+) \(\) Real\)', r'(declare-const \1 Real)', declarations)
    
    # Replace variables with their corresponding expressions
    assertions = inline_let_expressions(smt2)
    return f"{declarations}{assertions}(check-sat)\n(get-model)"


