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
        self.eps = eps
        self.buckets = self.ts.program_variables
        self.cs = ConstraintSystem()

    def find_witness(self) -> Any:

        # Minimum decrease of the ranking function per loop
        M = sp.Symbol("M")
        self.cs.add_free_constraint(M > 0)


        b1, b3 = self.buckets[1], self.buckets[3]

        self.ranking_f = get_linear_expression("rank", self.buckets)

        self.sm_update = {
            b: get_linear_expression(f"{b}_upd", self.buckets) for b in self.buckets
        }

        cind_updates = [
            {self.buckets[i]: 0, self.buckets[(i + 1) % len(self.buckets)]: 0} for i in range(len(self.buckets))
        ]

        all_buckets_positive = sp.And(*[b >= 0 for b in self.buckets])
        all_buckets_less_than_one_minus_eps = sp.And(*[b <= 1-self.eps for b in self.buckets])

        # Uncomment the following lines, if you want to ensure, that the system finds the solution with buckets b1 and b3
        b1, b3 = self.buckets[1], self.buckets[3]
        all_buckets_positive = sp.And(b1 >= 0, b3 >= 0)
        all_buckets_less_than_one_minus_eps = sp.And(b1 <= 1-self.eps, b3 <= 1-self.eps)

        
        sm_added_one = sp.Eq(sp.Add(*self.buckets).subs(self.sm_update, simultaneous=True) - sp.Add(*self.buckets), 1)
        sm_did_not_remove = sp.And(*[pv.subs(self.sm_update, simultaneous=True) - pv >= 0 for pv in self.buckets])

        # Ensure that updates are correct
        updates_correct = ConstraintPair(
            self.buckets,
            sp.And(all_buckets_positive, all_buckets_less_than_one_minus_eps),
            sp.And(sm_added_one, sm_did_not_remove),
        )
        self.cs.add_constraint_pair(updates_correct)

        for cind_update in cind_updates:
            
            # Value of the ranking function, after one loop of stepmother and cinderella updates
            ranking_f_after = self.ranking_f.subs(cind_update, simultaneous=True).subs(self.sm_update, simultaneous=True)

            # Loop condition still holds after the updates
            after_update_again_this_loop = all_buckets_less_than_one_minus_eps.subs(cind_update, simultaneous=True).subs(self.sm_update, simultaneous=True)

            # Ensure that the ranking function is deacreasing, if the loop has to be executed again
            cp = ConstraintPair(
                self.buckets,
                sp.And(all_buckets_positive, all_buckets_less_than_one_minus_eps, after_update_again_this_loop),
                sp.And(self.ranking_f - ranking_f_after > M, ranking_f_after >= 0, self.ranking_f >= 0),
            )
            self.cs.add_constraint_pair(cp)

            
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
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        print("M:")
        print(model[sp.Symbol("M")])

        print("Ranking Function:")
        print(self.ranking_f.subs(model, simultaneous=True))

        print("Stepmother Updates:")
        for key, value in self.sm_update.items():
            if isinstance(value, sp.Basic):
                value = value.evalf()
            print(f"{key}: {value.subs(model, simultaneous=True)}")
