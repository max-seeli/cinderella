from __future__ import annotations

import os
from typing import Any, Dict, Union

import sympy as sp

from constraint import ConstraintPair, ConstraintSystem
from template import get_linear_expression, get_template
from transition import *

FILE_LOCATION = os.path.dirname(os.path.realpath(__file__))


class CLW:

    def __init__(self,
                 transition_system: TransitionSystem,
                 eps: float,
                 ) -> None:
        self.ts: TransitionSystem = transition_system
        self.eps = sp.Symbol("eps")
        self.buckets = self.ts.program_variables
        self.cs = ConstraintSystem()

        self.functional_frames = []

    def find_witness(self) -> Any:

        b1, b3 = self.buckets[1], self.buckets[3]

        # Minimum decrease of the ranking function per loop
        # M = sp.Symbol("M")
        #self.cs.add_free_constraint(M > 0)

        self.eps = sp.Symbol("eps")

        t = sp.Symbol("t")
        self.cs.add_free_constraint(t > 0)
        fct_eps = t * self.eps

        # All possible updates by cinderella
        cind_updates = [
            {self.buckets[i]: 0, self.buckets[(i + 1) % len(self.buckets)]: 0} for i in range(len(self.buckets))
        ]

        # Buckets are positive (game invariant)
        all_buckets_positive = sp.And(*[b >= 0 for b in self.buckets])

        # Negated intermediate goal
        #intermediate_goal = get_template("intermediate_goal", self.buckets, 1, 2, 1)
        intermediate_goal = sp.Or(b1 > 1-self.eps, b3 > 1-self.eps)

        self.constrain_partial_solution(
            cind_updates=cind_updates,
            invariant=all_buckets_positive,
            target=intermediate_goal,
            rank_fn_eps=fct_eps,
        )

        """
        final_goal = sp.Or(*[b > 2 - self.eps for b in self.buckets])
        for i, inter_goal_part in enumerate(intermediate_goal.args):
            self.constrain_partial_solution(
                cind_updates=cind_updates,
                invariant=sp.And(all_buckets_positive, inter_goal_part),
                target=final_goal,
                rank_fn_eps=fct_eps,
                additional_target_not_reached=False)
        """
        print(self.cs)
        self.cs.write_smt2(os.path.join(
            FILE_LOCATION, 'out', f'{self.ts.name}.smt2'))

    __id = 0

    def constrain_partial_solution(self,
                                   cind_updates: Dict[sp.Symbol, sp.Basic],
                                   invariant: sp.Basic,
                                   target: sp.Basic,
                                   rank_fn_eps: sp.Symbol,
                                   additional_target_not_reached: bool = True,
                                   ) -> None:
        """
        Given a set of updates, an invariant, and a target, this function
        constrains the partial solution to ensure that the updates are
        correct and that there exists a ranking function that decreases
        with each update.
        """
        global __id
        self.__id += 1

        rank_fn = get_linear_expression(f"rank_{self.__id}", self.buckets)
        sm_update = {
            b: b + get_linear_expression(f"sm_upd_{self.__id}_{b}", self.buckets + [self.eps]) for b in self.buckets
        }

        # Ensure that updates are correct
        enforce_sm_added_one = sp.GreaterThan(
            sp.Add(*self.buckets) + 1, sp.Add(*sm_update.values()))
        enforce_sm_no_removal = sp.And(
            *[sm_update[b] - b >= 0 for b in self.buckets])
        updates_correct = ConstraintPair(
            self.buckets + [self.eps],
            sp.And(invariant, 0 < self.eps, self.eps < 1),
            sp.And(enforce_sm_added_one, enforce_sm_no_removal),
        )
        self.cs.add_constraint_pair(updates_correct)

        target_not_reached = sp.Not(target).simplify()
        for cind_update in cind_updates:
            rank_fn_upd = rank_fn.subs(cind_update, simultaneous=True).subs(
                sm_update, simultaneous=True)
            target_not_reached_upd = target_not_reached.subs(
                cind_update, simultaneous=True).subs(sm_update, simultaneous=True)

            # This is somewhat of a hack, but if we include the target_not_reached for the constraints from
            # the second part, it does not terminate.
            target_not_reached_const = target_not_reached if additional_target_not_reached else sp.true

            # Ensure that the ranking function is deacreasing, if the loop has to be executed again
            cp = ConstraintPair(
                self.buckets + [self.eps],
                sp.And(invariant, target_not_reached_const,
                       target_not_reached_upd, 0 < self.eps, self.eps < 1),
                sp.And(rank_fn - rank_fn_upd >= rank_fn_eps, rank_fn_upd >= 0)
            )
            self.cs.add_constraint_pair(cp)

        functional_frame = {"rank_fn": rank_fn, "sm_update": sm_update}
        self.functional_frames.append(functional_frame)

    def print_model(self, model: Dict[str, Union[int, float]]):
        """
        Print the model of the SMT2 solver in a human-readable format.

        Parameters
        ----------
        model : Dict[str, Union[int, float]]
            The model from the SMT2 solver.

        """
        from prefix_parser.parser import parse_expression
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        #print("M:")
        #print(model[sp.Symbol("M")])

        print("t:")
        print(model[sp.Symbol("t")])

        for i, frame in enumerate(self.functional_frames):
            print(f"Functional Frame {i}:")

            print("Rank Function:")
            print(frame["rank_fn"].subs(model, simultaneous=True))
            print("Stepmother Update:")
            for key, value in frame["sm_update"].items():
                if isinstance(value, sp.Basic):
                    value = value.evalf()
                print(f"{key}: {value.subs(model, simultaneous=True)}")
