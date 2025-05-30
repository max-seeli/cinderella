from __future__ import annotations

import os
import subprocess
from functools import reduce
from typing import Tuple, Union

import regex as re
import sympy as sp

from util import CustomPrinter

FILE_LOCATION = os.path.dirname(os.path.realpath(__file__))
T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)


class TransitionSystem:

    def __init__(self,
                 name: str,
                 assertion: dict[Variable, Condition],
                 locations: list[Location],
                 initial_location: Location,
                 program_variables: list[Variable],
                 ) -> None:
        self.name = name
        self.assertion = assertion
        self.locations = locations
        self.initial_location = initial_location
        self.program_variables = program_variables

    @property
    def full_assertion(self) -> sp.Basic:
        return reduce(lambda x, y: x & y, [condition.formula for variable, condition in self.assertion.items()])

    def generate_invariants(self) -> None:
        """
        Generate the invariants for each location in the transition system.
        """
        self.generate_fst()
        PROGRAM = os.path.join(FILE_LOCATION, 'aspic')
        FILE = os.path.join(FILE_LOCATION, f'fst/{self.name}.fst')
        result = subprocess.run(
            [PROGRAM, FILE], capture_output=True, text=True)
        invariant_output = result.stdout

        for location in self.locations:
            invariant = re.search(
                f'{location.name}\s+-+>\s+\{{(.*)\}}', invariant_output)

            if result.returncode != 0 and invariant == None:
                raise ValueError(
                    f'Error while generating invariants: {result.stderr} \nOutput: {result.stdout}')

            invariant = invariant.group(1)
            invariants = [i.strip() for i in invariant.split(',')]
            invariants = [re.sub(r'([\w\s\+\*\-]+)=([\w\s\+\*\-]+)', r'Eq(\1,\2)', i)
                          for i in invariants]  # Replace = with Eq

            invariants = [re.sub(r'(\d)([a-zA-Z])', r'\1*\2', i)
                          for i in invariants]  # Add implicit multiplication
            sp_form = [sp.sympify(i) for i in invariants]
            print(f"Location {location.name} invariant: {sp_form}")
            location.invariant.formula = sp.And(
                *sp_form) if isinstance(sp_form, list) else sp_form

    def generate_fst(self) -> None:
        """
        Generate the FST file for the transition system.
        """
        OUT_DIR = os.path.join(FILE_LOCATION, 'fst')
        if not os.path.exists(OUT_DIR):
            os.makedirs(OUT_DIR)

        with open(os.path.join(OUT_DIR, f'{self.name}.fst'), 'w') as f:
            f.write(f'model {self.name} {{\n\n')
            f.write(
                f'var {",".join([var.name for var in self.program_variables + self.aux_variables])};\n\n')
            f.write(
                f'states {",".join([location.name for location in self.locations])};\n\n')
            for i, location in enumerate(self.locations):
                for j, transition in enumerate(location.transitions):
                    f.write(f'transition t{i}_{j} := {{\n')
                    f.write(f' from := {location.name};\n')
                    f.write(f' to := {transition.target.name};\n')
                    guard_conjunct = sp.simplify(
                        transition.guard.formula & transition.update.get_nondet_constraint())
                    guard_str = self.expression_to_fst(guard_conjunct)
                    f.write(f' guard := {guard_str};\n')
                    action_string = ",".join(
                        [f'{var.name}\'={update}' for var, update in transition.update.get_transform_dict().items()])
                    f.write(f' action := {action_string};\n')
                    f.write(f'}};\n\n')
            f.write('}')

            f.write(f'strategy s1 {{\n\n')
            assertion_conditions = [
                c.formula for c in self.assertion.values() if sp.simplify(c.formula) != sp.true]
            assertion_string = "".join(
                [f" && {CustomPrinter().doprint(condition)}" for condition in assertion_conditions])
            f.write(
                f'Region init := {{state={self.initial_location.name}{assertion_string}}};\n\n')
            f.write('}')

    def expression_to_fst(self, expression: sp.Basic) -> str:
        """
        Convert a sympy expression to a string that can be used in the FST file.

        Parameters
        ----------
        expression : sp.Basic
            The sympy expression to convert.

        Returns
        -------
        str
            The string representation of the expression.
        """
        if isinstance(expression, sp.And):
            return ' && '.join([self.expression_to_fst(arg) for arg in expression.args if sp.simplify(arg) != sp.true])
        elif isinstance(expression, sp.Or):
            return ' || '.join([self.expression_to_fst(arg) for arg in expression.args if sp.simplify(arg) != sp.false])
        elif isinstance(expression, sp.Eq):
            return f'{self.expression_to_fst(expression.lhs)} = {self.expression_to_fst(expression.rhs)}'
        elif expression == sp.true:
            return 'true'
        elif expression == sp.false:
            return 'false'
        else:
            return str(expression)


class Location:

    def __init__(self,
                 name: str,
                 transitions: list[Transition],
                 invariant: Union[Condition, sp.Basic],
                 is_non_deterministic: bool,
                 is_angelic: bool
                 ) -> None:
        self.name = name
        self.transitions = transitions
        self.__invariant = invariant if isinstance(invariant, Condition) else Condition(invariant)
        self.is_non_deterministic = is_non_deterministic
        self.is_angelic = is_angelic

    @property
    def invariant(self) -> sp.Basic:
        return self.__invariant.formula
        

class Transition:

    def __init__(self,
                 target: Location,
                 guard: Condition,
                 update: Update,
                 additional_update_constraint: Condition = None
                 ) -> None:
        self.target = target
        self.guard = guard
        self.update = update
        self.additional_update_constraint = additional_update_constraint

    def target_invariant(self, pre_transform=None) -> sp.Basic:
        """
        Get the invariant of the target location after the update.

        Parameters
        ----------
        pre_transform : dict[Variable, sp.Expr]
            A dictionary of pre-transformed variables.

        Returns
        -------
        sp.Basic
            The invariant of the target location after the update.
        """
        invariant = self.update(self.target.invariant)
        if pre_transform:
            invariant = invariant.subs(pre_transform)
        return invariant


class Condition:

    def __init__(self, formula: sp.Basic, use_template: bool = False) -> None:
        self.formula = formula
        self.use_template = use_template


class Update:

    def __init__(self, transform_per_variable) -> None:
        self.__transform_per_variable = transform_per_variable

    def __call__(self, expression: sp.Basic) -> sp.Basic:
        return expression.subs(self.__transform_per_variable, simultaneous=True)

    def get_transform_dict(self) -> dict[Variable, sp.Basic]:
        return self.__transform_per_variable


class Variable(sp.Symbol):

    def __init__(self,
                 name: str
                 ) -> None:
        super().__init__()
        self.name = name


class NondetGenerator():

    @staticmethod
    def generate_nondet_variable(name: str, min_val: float, max_val: float) -> NondeterministicVariable:
        nd = NondeterministicVariable(name)
        nd.nondet_constraint = sp.And(nd >= min_val, nd <= max_val)
        return nd


class NondeterministicVariable(Variable):

    def get_nondet_constraint(self) -> sp.Basic:
        return self.nondet_constraint
