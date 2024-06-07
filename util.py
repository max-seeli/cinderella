from sympy.printing.str import StrPrinter
from sympy.printing.precedence import precedence

class CustomPrinter(StrPrinter):
    def _print_Relational(self, expr):

        if expr.rel_op == '==':
            return '%s = %s' % (self.parenthesize(expr.lhs, precedence(expr)),
                                self.parenthesize(expr.rhs, precedence(expr)))
        return super()._print_Relational(expr)
