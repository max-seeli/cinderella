from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import REAL, INT

def check_linearity(filename):
    parser = SmtLibParser()
    with open(filename, 'r') as file:
        formula = parser.get_script(file).get_last_formula()
    linear = True
    
    def is_linear(formula):
        if formula.is_times() or formula.is_function_application():
            symbol_found = False
            # Check if multiplication is between a constant and a variable (still linear)
            for arg in formula.args():
                if arg.is_constant():
                    continue
                elif arg.is_symbol():
                    if symbol_found:
                        print(f"Double-symbol non-linear term: {formula}")
                        return False, symbol_found
                    symbol_found = True
                else:
                    linear, symbol_found = is_linear(arg)
                    if not linear:
                        print(f"Non-linear term: {formula}")
                        return False, symbol_found
                
            return True, symbol_found
        else:
            return all([is_linear(arg)[0] for arg in formula.args()]), any([is_linear(arg)[1] for arg in formula.args()])
    
    linear = is_linear(formula)
    return "All constraints are linear." if linear[0] else "Some constraints are non-linear."

# Example usage
filename = 'farkas-mathsat-nosat.txt'
result = check_linearity(filename)
print(result)
