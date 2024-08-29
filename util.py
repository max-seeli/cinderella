import signal
from typing import Callable

import sympy as sp
from sympy.printing.str import StrPrinter
from sympy.printing.precedence import precedence

class CustomPrinter(StrPrinter):
    def _print_Relational(self, expr):

        if expr.rel_op == '==':
            return '%s = %s' % (self.parenthesize(expr.lhs, precedence(expr)),
                                self.parenthesize(expr.rhs, precedence(expr)))
        return super()._print_Relational(expr)


def set_timeout(callable: Callable, timeout: int, *args, **kwargs) -> sp.Basic:
    """
    Set a timeout for a callable.

    Parameters
    ----------
    callable : Callable
        The callable to be executed.
    timeout : int
        The timeout in seconds.
    args : Any
        The arguments to be passed to the callable.
    kwargs : Any
        The keyword arguments to be passed to the callable.

    Returns
    -------
    Any
        The result of the callable.

    Raises
    ------
    TimeoutError
        If the operation times out.
    """
    def timeout_handler(signum, frame):
        raise TimeoutError(
            f'The operation {callable.__name__} timed out after {timeout} seconds.')

    signal.signal(signal.SIGALRM, timeout_handler)
    signal.alarm(timeout)

    try:
        return callable(*args, **kwargs)
    finally:
        signal.alarm(0)
