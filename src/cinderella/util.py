import signal
from typing import Any, Callable


def set_timeout(callable: Callable, timeout: int, *args, **kwargs) -> Any:
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
