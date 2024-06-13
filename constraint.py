from __future__ import annotations
from typing import Tuple, Union, List, Set
import sympy as sp


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
                 program_variables: List[sp.Symbol],
                 use_invariants: bool = False
                 ) -> None:
        self.program_variables = program_variables
        self.free_constraints = []
        self.constraint_pairs = []
        self.use_invariants = use_invariants

    def __str__(self) -> str:
        free = "\n".join([str(c) for c in self.free_constraints])
        pairs = "\n".join([str(p) for p in self.constraint_pairs])

        return f'Free Constraints:\n{free}\nConstraint Pairs:\n{pairs}'

    def add_free_constraint(self, constraint: sp.Basic) -> None:
        """
        Add a free constraint to the constraint system.

        Parameters
        ----------
        constraint : sp.Basic
            The free constraint to be added to the constraint system.
        """
        self.free_constraints.append(Constraint(constraint))

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
        symbols = set()
        smt2_constraints = []
        for constraint in self.free_constraints:
            symbols.update(constraint.get_variables())
            smt_constraint = constraint.to_smt()
            smt2 = f'(assert {smt_constraint})'
            smt2_constraints.append(smt2)

        for pair in self.constraint_pairs:
            
            symbols.update(pair.get_variables())
            
            smt_constraint = pair.to_smt(self.use_invariants)

            variable_defs = []
            for v in self.program_variables:
                variable_defs.append(f'({v.name} Real)')
            variable_defs = f"({' '.join(variable_defs)})"
            smt_quantified = f'(forall {variable_defs} {smt_constraint})'
            
            smt2 = f'(assert {smt_quantified})'
            smt2_constraints.append(smt2)

        symbols = symbols - set(self.program_variables)

        declarations = []
        for s in symbols:
            declarations.append(f'(declare-const {s.name} Real)')

        smt2 = '\n'.join(declarations + smt2_constraints + ['(check-sat)', '(get-model)'])

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
                 invariants: List[sp.Basic] = []
                 ) -> None:
        self.condition = Constraint(condition)
        self.implication = Constraint(implication)
        self.invariants = invariants

    def __str__(self) -> str:
        return f'{self.condition} => {self.implication}'
    
    def get_variables(self) -> Set[sp.Symbol]:
        """
        Get the variables in the constraint pair.

        Returns
        -------
        List[sp.Symbol]
            The variables in the constraint pair.
        """
        return self.condition.get_variables().union(self.implication.get_variables())
    
    def to_smt(self, use_invariants=False) -> str:
        """
        Convert the constraint pair to an SMT2 string.

        Returns
        -------
        str
            The SMT2 string representing the constraint pair.
        """
        condition = self.condition.formula
        if use_invariants:
            condition = sp.And(*self.invariants, condition)
        
        if condition == sp.true:
            # TODO: Maybe remove this case?
            return f'(=> (> 1 0) {self.implication.to_smt()})'
        elif condition == sp.false:
            return f'(=> (> 0 1) {self.implication.to_smt()})'
        elif self.implication.formula == sp.true:
            return f'(=> {Constraint(condition).to_smt()} (> 1 0))'
        
        condition = Constraint(condition)

        return f'(=> {condition.to_smt()} {self.implication.to_smt()})'
    
class Constraint:
    """
    A class representing a constraint.

    Attributes
    ----------
    formula : sp.Basic
        The formula of the constraint.
    """

    def __init__(self, formula: sp.Basic) -> None:
        self.formula = formula

    def __str__(self) -> str:
        return str(self.formula)

    def get_variables(self) -> Set[sp.Symbol]:
        """
        Get the variables in the constraint.

        Returns
        -------
        List[sp.Symbol]
            The variables in the constraint.
        """
        return self.formula.free_symbols

    def to_smt(self) -> str:
        """
        Convert the constraint pair to an SMT2 string.

        Returns
        -------
        str
            The SMT2 string representing the constraint pair.
        """
        return f'{self.__to_smt(self.formula)}'

    def __to_smt(self, constraint: sp.Basic) -> str:
        """
        Convert a constraint to an SMT2 string.

        Parameters
        ----------
        constraint : sp.Basic
            The constraint to be converted.

        Returns
        -------
        str
            The SMT2 string representing the constraint.
        """
        if constraint.is_Relational:
            op = constraint.rel_op if constraint.rel_op != '==' else '='
            return f'({op} {self.__to_smt(constraint.lhs)} {self.__to_smt(constraint.rhs)})'
        elif constraint.is_Add:
            return f'(+ {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
        elif constraint.is_Mul:
            return f'(* {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
        elif constraint.is_Function and constraint.is_Boolean:
            return f'({str(constraint.func).lower()} {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
        elif isinstance(constraint, sp.UnevaluatedExpr):
            return self.__to_smt(constraint.args[0])
        elif constraint.is_Symbol:
            return constraint.name
        elif constraint.is_Number:
            return str(constraint)
        elif constraint == sp.true:
            return 'true'
        elif constraint == sp.false:
            return 'false'
        else:
            raise ValueError(f'Unsupported constraint type: {type(constraint)}\n\tFor constraint: {constraint}')
        
