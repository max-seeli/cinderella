from __future__ import annotations
from typing import Tuple, Union, List
import sympy as sp
import z3

from util import to_z3, format_smt2


class ConstraintSystem:
    """
    A class representing a constraint system.
    
    Attributes
    ----------
    constraint_pairs : List[ConstraintPair]
        A list of constraint pairs in the constraint system.
    use_invariants : bool
        Whether to use invariants in the constraint system.
    """

    def __init__(self, 
                 constraint_pairs: List[ConstraintPair] = None,
                 use_invariants: bool = False
                 ) -> None:
        self.constraint_pairs = constraint_pairs if constraint_pairs else []
        self.use_invariants = use_invariants

    def add_constraint_pair(self, constraint_pair: Union[ConstraintPair, Tuple]) -> None:
        """
        Add a constraint pair to the constraint system.

        Parameters
        ----------
        constraint_pair : Union[ConstraintPair, Tuple]
            The constraint pair to be added to the constraint system.
        """
        if isinstance(constraint_pair, tuple):
            constraint_pair = ConstraintPair(*constraint_pair)
        self.constraint_pairs.append(constraint_pair)

    def write_smt2(self, file_path: str) -> None:
        """
        Write the constraint system to an SMT2 file.

        Parameters
        ----------
        file_path : str
            The path to the SMT2 file.
        """
        s = z3.Solver()
        constraints = [cp.to_z3(self.use_invariants) for cp in self.constraint_pairs]
        s.add([c for c in constraints if c is not None])
        smt2 = format_smt2(s.to_smt2())

        with open(file_path, 'w') as f:
            f.write(smt2)

class ConstraintPair:
    """
    A class representing a constraint pair.

    Attributes
    ----------
    condition : sp.Basic
        The condition of the constraint pair.
    implication : sp.Basic
        The implication of the constraint pair.
    invariants : List[sp.Basic]
        A list of invariants in the constraint pair.
    """

    def __init__(self, 
                 condition: sp.Basic,
                 implication: sp.Basic,
                 invariants: List[sp.Basic] = None
                 ) -> None:
        self.condition = condition
        self.implication = implication
        self.invariants = invariants

    def to_z3(self, use_invariants: bool = False) -> z3.BoolRef:
        """
        Convert the constraint pair to a Z3 expression.

        Parameters
        ----------
        use_invariants : bool
            Whether to use the invariants in the constraint pair.

        Returns
        -------
        z3.BoolRef
            The Z3 expression representing the constraint pair.
        """
        lhs = to_z3(self.condition)
        rhs = to_z3(self.implication)
        if use_invariants:
            for invariant in self.invariants:
                lhs = z3.And(lhs, to_z3(invariant))
        
        if str(lhs) == 'False' or str(rhs) == 'True':
            return None
        return z3.Implies(lhs, rhs)        



