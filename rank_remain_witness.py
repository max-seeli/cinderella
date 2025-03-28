from __future__ import annotations

import os
from functools import reduce
from itertools import product
from math import ceil, floor
from typing import Any, Dict, List, Tuple, Union

import sympy as sp

from constraint import ConstraintPair, ConstraintSystem
from template import get_linear_expression, get_template
from transition import *

FILE_LOCATION = os.path.dirname(os.path.realpath(__file__))
T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)


class RRW:

    def __init__(self,
                 transition_system: TransitionSystem
                 ) -> None:
        self.ts: TransitionSystem = transition_system
        self.program_variables = self.ts.program_variables
        self.cs = ConstraintSystem()

        """
        self.ranking_function = [
            {
                "func": 2 - self.program_variables[1],
                "guard": self.program_variables[1] >= self.program_variables[3]
            },
            {
                "func": 2 - self.program_variables[3],
                "guard": self.program_variables[3] > self.program_variables[1]
            }
        ]
        """

        ranking_guard = get_linear_expression(
            "rank_guard", self.program_variables) >= 0
        self.ranking_function = [
            {
                "func": get_linear_expression("rank1", self.program_variables),
                "guard": ranking_guard
            },
            {
                "func": get_linear_expression("rank2", self.program_variables),
                "guard": sp.Not(ranking_guard)
            }
        ]

    def find_witness(self) -> Any:

        M = sp.Symbol("M")
        self.cs.add_free_constraint(M > 0)

        for l in self.ts.locations:
            if l.name == "goal":
                continue

            # One active ranking function
            exists_sat_rank_part = ConstraintPair(
                self.program_variables,
                sp.And(l.invariant, *[sp.Not(part["guard"])
                       for part in self.ranking_function[:-1]]),
                self.ranking_function[-1]["guard"],
            )
            self.cs.add_constraint_pair(exists_sat_rank_part)

            # One active transition
            transition_guards = [t.guard.formula for t in l.transitions]
            exists_sat_trans_guards = ConstraintPair(
                self.program_variables,
                sp.And(l.invariant, *[sp.Not(t_guard)
                       for t_guard in transition_guards[:-1]]),
                transition_guards[-1]
            )
            self.cs.add_constraint_pair(exists_sat_trans_guards)

            # Valid Successor Invariants
            for t in l.transitions:
                valid_succ_inv = ConstraintPair(
                    self.program_variables,
                    sp.And(t.guard.formula, l.invariant),
                    t.target_invariant()
                )
                self.cs.add_constraint_pair(valid_succ_inv)

        for l in self.ts.locations:  # TODO: Remove this line
            # Rank Constraints
            for t in l.transitions:
                if t.target.name == "goal":
                    continue
                for part_curr, part_succ in product(self.ranking_function, repeat=2):

                    rank_magnitude = part_curr["func"] - \
                        M if l.is_angelic else part_curr["func"]

                    rank_after_transition = t.update(part_succ["func"])
                    guard_after_transition = t.update(part_succ["guard"])

                    angelic_ranks = ConstraintPair(
                        # TODO: Remove additional variables
                        self.program_variables +
                        [sp.Symbol(f"rank_{l.name}_{t.target.name}")],
                        sp.And(t.guard.formula, l.invariant,
                               part_curr["guard"], guard_after_transition),
                        sp.And(0 <= rank_after_transition,
                               rank_after_transition <= rank_magnitude)
                    )
                    self.cs.add_constraint_pair(angelic_ranks)

        print(self.cs)
        self.cs.write_smt2(os.path.join(
            FILE_LOCATION, 'out', f'{self.ts.name}.smt2'))

    def print_model(self, model: Dict[str, Union[int, float]]):
        """
        Print the model of the SMT2 solver in a human-readable format.

        Parameters
        ----------
        model : Dict[str, Union[int, float]]
            The model from the SMT2 solver.

        """
        from prefix_parser.parser import parse_expression
        print(model)
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        print("Ranking Functions:")
        print(
            f"If {self.ranking_function[0]['guard'].subs(model)} then {self.ranking_function[0]['func'].subs(model)}")
        print(
            f"Else If {self.ranking_function[1]['guard'].subs(model)} then {self.ranking_function[1]['func'].subs(model)}")
