from __future__ import annotations

from typing import List, Set, Tuple, Union
from warnings import warn

import sympy as sp


class ConstraintSystem:
    """
    A class representing a constraint system.

    Attributes
    ----------
    free_constraints : List[Constraint]
        A list of free constraints in the constraint system.
    constraint_pairs : List[ConstraintPair]
        A list of constraint pairs in the constraint system.
    use_invariants : bool
        Whether to use invariants in the constraint system.
    """

    def __init__(self,
                 ) -> None:
        self.free_constraints: List[Constraint] = []
        self.constraint_pairs: List[ConstraintPair] = []

    def __str__(self) -> str:
        free = "\n".join([str(c) for c in self.free_constraints])
        pairs = "\n".join([f"[Pair {i+1}/{len(self.constraint_pairs)}] " + str(p) for i, p in enumerate(self.constraint_pairs)])

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

    def subs(self, substitution: dict) -> None:
        """
        Substitute variables in the constraint system.

        Parameters
        ----------
        substitution : dict
            The substitution dictionary.
        """
        for constraint in self.free_constraints:
            constraint.formula = constraint.formula.subs(substitution, simultaneous=True)
        for pair in self.constraint_pairs:
            pair.subs(substitution)

    def write_smt2(self, file_path: str) -> None:
        """
        Write the constraint system to an SMT2 file.

        Parameters
        ----------
        file_path : str
            The path to the SMT2 file.
        """
        free_variables = set().union(*[constraint.get_free_variables()
                               for constraint in self.free_constraints + self.constraint_pairs])
        print("Free variables: ", free_variables)
        declarations = [
            f'(declare-const {v.name} Real)' for v in free_variables]

        smt2_constraints = []
        for constraint in self.free_constraints + self.constraint_pairs:
            smt2_constraints.append(f'(assert {constraint.to_smt()})')

        smt2 = '\n'.join(declarations + smt2_constraints +
                         ['(check-sat)', '(get-model)'])

        with open(file_path, 'w') as f:
            f.write(smt2)


class ConstraintPair:
    """
    A class representing a constraint pair.

    Attributes
    ----------
    forall_vars : List[sp.Symbol]
        A list of universally quantified variables in the constraint pair.
    condition : sp.Basic
        The condition of the constraint pair.
    implication : sp.Basic
        The implication of the constraint pair.
    invariants : List[sp.Basic]
        A list of invariants in the constraint pair.
    """

    def __init__(self,
                 forall_vars: List[sp.Symbol],
                 condition: sp.Basic,
                 implication: sp.Basic,
                 ) -> None:
        self.forall_vars = forall_vars
        self.condition = Constraint(condition)
        self.implication = Constraint(implication)

    def __str__(self) -> str:
        return f'{self.condition.formula} -> {self.implication.formula}'

    def get_forall_variables(self) -> Set[sp.Symbol]:
        """
        Get the universally quantified variables in the constraint pair.

        Returns
        -------
        Set[sp.Symbol]
            The universally quantified variables in the constraint pair.
        """
        return set(self.forall_vars)

    def get_free_variables(self) -> Set[sp.Symbol]:
        """
        Get the variables in the constraint pair that are not universally quantified.

        Returns
        -------
        Set[sp.Symbol]
            The variables in the constraint pair.
        """
        return set().union(
            self.condition.get_free_variables(),
            self.implication.get_free_variables(),
        ).difference(self.get_forall_variables())
        
    def subs(self, substitution: dict) -> None:
        """
        Substitute variables in the constraint pair.

        Parameters
        ----------
        substitution : dict
            The substitution dictionary.
        """
        for i, var in enumerate(self.forall_vars):
            if var in substitution:
                print("Substituting", var, substitution[var])
                assert False, "Substitution of universally quantified variables is not supported"
                self.forall_vars[i] = substitution[var]
        self.condition.formula = self.condition.formula.subs(substitution, simultaneous=True)
        self.implication.formula = self.implication.formula.subs(substitution, simultaneous=True)

    def to_smt(self) -> str:
        """
        Convert the constraint pair to an SMT2 string.

        Returns
        -------
        str
            The SMT2 string representing the constraint pair.
        """
        forall_string = f"({' '.join([f'({v.name} Real)' for v in self.forall_vars])})"

        return f'(forall {forall_string} (=> {self.condition.to_smt()} {self.implication.to_smt()}))'


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

    def get_free_variables(self) -> Set[sp.Symbol]:
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
            arg_pair = f'{self.__to_smt(constraint.lhs)} {self.__to_smt(constraint.rhs)}'
            if constraint.rel_op == '==':
                return f'(and (<= {arg_pair}) (>= {arg_pair}))'
            else:
                return f'({constraint.rel_op} {arg_pair})'
        elif constraint.is_Add:
            return f'(+ {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
        elif constraint.is_Mul:
            return f'(* {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
        elif constraint.is_Function and constraint.is_Boolean:
            f = str(constraint.func).lower()
            if f == 'and':
                assert len(
                    constraint.args) >= 2, f'Expected 2 arguments, got {len(constraint.args)}'
                return f'(and {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
            elif f == 'or':
                assert len(
                    constraint.args) >= 2, f'Expected 2 arguments, got {len(constraint.args)}'
                return f'(or {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
            elif f == 'not':
                assert len(
                    constraint.args) == 1, f'Expected 1 argument, got {len(constraint.args)}'
                child = constraint.args[0]
                if isinstance(child, sp.Implies):
                    assert len(
                        child.args) == 2, f'Expected 2 arguments, got {len(child.args)}'
                    return f'(and {self.__to_smt(child.args[0])} {self.__to_smt(sp.Not(child.args[1]))})'
                elif isinstance(child, sp.And):
                    assert len(
                        child.args) >= 2, f'Expected 2 arguments, got {len(child.args)}'
                    return f'(or {" ".join([self.__to_smt(sp.Not(arg)) for arg in child.args])})'
                elif isinstance(child, sp.Or):
                    assert len(
                        child.args) >= 2, f'Expected 2 arguments, got {len(child.args)}'
                    return f'(and {" ".join([self.__to_smt(sp.Not(arg)) for arg in child.args])})'
                else:
                    raise ValueError(
                        f'Unable to reduce negation on: {type(child)}')
            elif f == 'implies':
                assert len(
                    constraint.args) == 2, f'Expected 2 arguments, got {len(constraint.args)}'
                # return f'(=> {to_smt(constraint.args[0])} {to_smt(constraint.args[1])})'
                return f'(or {self.__to_smt(sp.Not(constraint.args[0]))} {self.__to_smt(constraint.args[1])})'
            else:
                warn(f'Unsupported function: {f}')
                return f'({str(constraint.func).lower()} {" ".join([self.__to_smt(arg) for arg in constraint.args])})'
        
        
        
        elif isinstance(constraint, sp.UnevaluatedExpr):
            return self.__to_smt(constraint.args[0])
        elif constraint.is_Symbol:
            return constraint.name
        elif constraint.is_Number:
            return str(constraint)
        elif constraint == sp.true:
            return '(>= 1 0)'
        elif constraint == sp.false:
            return '(>= 0 1)'  # self.__to_smt(sp.UnevaluatedExpr(0) >= 1)
        else:
            raise ValueError(
                f'Unsupported constraint type: {type(constraint)}\n\tFor constraint: {constraint}')
