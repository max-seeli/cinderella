from __future__ import annotations
import os
import regex as re
import sympy as sp
from functools import reduce
import subprocess

FILE_LOCATION = os.path.dirname(os.path.realpath(__file__))

class TransitionSystem:

    def __init__(self,
                 name: str,
                 assertion: dict[Variable, Condition],
                 locations: list[Location],
                 initial_location: Location,
                 variables: list[Variable],
                 aux_variables: list[Variable] = []
                 ) -> None:
        self.name = name
        self.assertion = assertion
        self.locations = locations
        self.initial_location = initial_location
        self.variables = variables
        self.aux_variables = aux_variables

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
        result = subprocess.run([PROGRAM, FILE], capture_output=True, text=True)
        if result.returncode != 0:
            raise ValueError(f'Error while generating invariants: {result.stderr}')
        
        invariant_output = result.stdout

        for location in self.locations:
            invariant = re.search(f'{location.name}\s+-+>\s+\{{(.*)\}}', invariant_output).group(1)
            sp_form = sp.sympify(invariant)
            location.invariant.formula = sp.And(*sp_form) if isinstance(sp_form, tuple) else sp_form

    def generate_fst(self) -> None:
        """
        Generate the FST file for the transition system.
        """
        OUT_DIR = os.path.join(FILE_LOCATION, 'fst')
        if not os.path.exists(OUT_DIR):
            os.makedirs(OUT_DIR)
        
        with open(os.path.join(OUT_DIR, f'{self.name}.fst'), 'w') as f:
            f.write(f'model {self.name} {{\n\n')
            f.write(f'var {",".join([var.name for var in self.variables + self.aux_variables])};\n\n')
            f.write(f'states {",".join([location.name for location in self.locations])};\n\n')
            for i, location in enumerate(self.locations):
                for j, transition in enumerate(location.transitions):
                    f.write(f'transition t{i}_{j} := {{\n')
                    f.write(f' from := {location.name};\n')
                    f.write(f' to := {transition.target.name};\n')
                    f.write(f' guard := {transition.guard.formula};\n')
                    action_string = ",".join([f'{var.name}\'={update}' for var, update in transition.update.transform_per_variable.items()])
                    f.write(f' action := {action_string};\n')
                    f.write(f'}};\n\n')
            f.write('}')

            f.write(f'strategy s1 {{\n\n')
            assertion_string = "".join([f" && {condition.formula}" for condition in self.assertion.values()])
            f.write(f'Region init := {{state={self.initial_location.name}{assertion_string}}};\n\n')
            f.write('}')

class Location:

    def __init__(self, 
                 name: str,
                 transitions: list[Transition],
                 invariant: Condition,
                 is_angelic: bool,
                 is_finite: bool
                 ) -> None:
        self.name = name
        self.transitions = transitions
        self.invariant = invariant
        self.is_angelic = is_angelic
        self.is_finite = is_finite

class Transition:

    def __init__(self, 
                 target: Location,
                 guard: Condition,
                 update: Update
                 ) -> None:
        self.target = target
        self.guard = guard
        self.update = update
    
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
        invariant = self.target.invariant.formula.subs(self.update.transform_per_variable)
        if pre_transform:
            invariant = invariant.subs(pre_transform)
        return invariant

class Condition:
    
    def __init__(self, formula) -> None:
        self.formula = formula

class Update:

    def __init__(self, transform_per_variable) -> None:
        self.transform_per_variable = transform_per_variable

    def __call__(self, expression: sp.Basic) -> sp.Basic:
        return expression.subs(self.transform_per_variable)

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