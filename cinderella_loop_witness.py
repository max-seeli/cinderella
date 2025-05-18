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

        b1, b3 = self.buckets[1], self.buckets[3]


        # Minimum decrease of the ranking function per loop
        M = sp.Symbol("M")
        self.cs.add_free_constraint(M > 0)

        # All possible updates by cinderella
        cind_updates = [
            {self.buckets[i]: 0, self.buckets[(i + 1) % len(self.buckets)]: 0} for i in range(len(self.buckets))
        ]



        # Buckets are positive (game invariant)
        all_buckets_positive = sp.And(*[b >= 0 for b in self.buckets])


        # First Quintet
        self.ranking_first = get_linear_expression("rank_1", self.buckets)

        self.sm_update_first = {
            b: b + get_linear_expression(f"{b}_upd", self.buckets) for b in self.buckets
        }

        
        # Negated intermediate goal
        neg_intermediate_goal = get_template("intermediate_goal", self.buckets, 1, 2, 1)
        neg_intermediate_goal = sp.And(b1 <= 1-self.eps, b3 <= 1-self.eps)
        all_buckets_less_than_one_minus_eps = sp.And(*[b <= 1-self.eps for b in self.buckets])

        # Uncomment the following lines, if you want to ensure, that the system finds the solution with buckets b1 and b3
        #all_buckets_positive = sp.And(b1 >= 0, b3 >= 0)
        all_buckets_less_than_one_minus_eps = sp.And(b1 <= 1-self.eps, b3 <= 1-self.eps)

        
        self.sm_added_one = sp.LessThan(sp.Add(*self.buckets).subs(self.sm_update_first, simultaneous=True) - sp.Add(*self.buckets), 1)
        self.sm_did_not_remove = sp.And(*[pv.subs(self.sm_update_first, simultaneous=True) - pv >= 0 for pv in self.buckets])

        # Ensure that updates are correct
        updates_correct = ConstraintPair(
            self.buckets,
            sp.And(all_buckets_positive, neg_intermediate_goal),
            sp.And(self.sm_added_one, self.sm_did_not_remove),
        )
        self.cs.add_constraint_pair(updates_correct)

        for cind_update in cind_updates:
            print("---------------------------------------")
            print(cind_update)
            # Value of the ranking function, after one loop of stepmother and cinderella updates
            ranking_f_after = self.ranking_first.subs(cind_update, simultaneous=True).subs(self.sm_update_first, simultaneous=True)
            print("Ranking function after update:")
            print(ranking_f_after)
            # Loop condition still holds after the updates
            after_update_again_this_loop = neg_intermediate_goal.subs(cind_update, simultaneous=True).subs(self.sm_update_first, simultaneous=True)
            print("Loop condition after update:")
            print(neg_intermediate_goal.subs(cind_update, simultaneous=True))
            print(after_update_again_this_loop)

            # Ensure that the ranking function is deacreasing, if the loop has to be executed again
            cp = ConstraintPair(
                self.buckets,
                sp.And(all_buckets_positive, neg_intermediate_goal, after_update_again_this_loop),
                sp.And(self.ranking_first - ranking_f_after >= M, ranking_f_after >= 0) #, self.ranking_first >= 0),
            )
            self.cs.add_constraint_pair(cp)

        # Second Quintet
        # Intermediate goals
        any_bucket_larger_than_one_minus_eps = [b > 1-self.eps for b in self.buckets]
        # Uncomment the following lines, if you want to ensure, that the system finds the solution with buckets b1 and b3
        any_bucket_larger_than_one_minus_eps = [b > 1-self.eps for b in [b1, b3]]

        # Negated intermediate goal
        self.second_quintet_ranking = []
        self.second_sm_updates = []

        final_goal = sp.Or(*[b > 2 - self.eps for b in self.buckets])

        intermediate_goal = sp.Not(neg_intermediate_goal).simplify()
        # Ensure that the intermediate goal is a disjunction of the buckets
        print(intermediate_goal)
        assert type(intermediate_goal) == sp.Or
        assert len(intermediate_goal.args) == 2

        for i, inter_goal_part in enumerate(intermediate_goal.args):
            ranker = get_linear_expression(f"rank_2_{i}", self.buckets)
            self.second_quintet_ranking.append(ranker)
            sm_updater = {
                b: get_linear_expression(f"{b}_upd_2_{i}", self.buckets) for b in self.buckets
            }
            self.second_sm_updates.append(sm_updater)

            inter_sm_added_one = sp.LessThan(sp.Add(*self.buckets).subs(sm_updater, simultaneous=True) - sp.Add(*self.buckets), 1)
            inter_sm_did_not_remove = sp.And(*[pv.subs(sm_updater, simultaneous=True) - pv >= 0 for pv in self.buckets])

            # Ensure that updates are correct
            inter_updates_correct = ConstraintPair(
                self.buckets,
                sp.And(all_buckets_positive, inter_goal_part),
                sp.And(inter_sm_added_one, inter_sm_did_not_remove),
            )
            self.cs.add_constraint_pair(inter_updates_correct)

            for cind_update in cind_updates:
                # Value of the ranking function, after one loop of stepmother and cinderella updates
                ranking_f_after = ranker.subs(cind_update, simultaneous=True).subs(sm_updater, simultaneous=True)

                # Loop condition still holds after the updates
                after_update_again_this_loop = sp.Not(final_goal).subs(cind_update, simultaneous=True).subs(sm_updater, simultaneous=True)

                # Ensure that the ranking function is deacreasing, if the loop has to be executed again
                cp = ConstraintPair(
                    self.buckets,
                    sp.And(all_buckets_positive, inter_goal_part, after_update_again_this_loop),
                    sp.And(ranker - ranking_f_after >= M, ranking_f_after >= 0) #, ranker >= 0),
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
        print(self.ranking_first.subs(model, simultaneous=True))

        print("Stepmother Updates:")
        for key, value in self.sm_update_first.items():
            if isinstance(value, sp.Basic):
                value = value.evalf()
            print(f"{key}: {value.subs(model, simultaneous=True)}")

        print("Stepmother Updates Valid:")
        print(self.sm_added_one.subs(model, simultaneous=True))
        print(self.sm_did_not_remove.subs(model, simultaneous=True))

        for i, ranker in enumerate(self.second_quintet_ranking):
            print(f"Ranking Function {i}:")
            print(ranker.subs(model, simultaneous=True))


        print("Inter Stepmother Updates:")
        for i, sm_updater in enumerate(self.second_sm_updates):
            print(f"Update {i}:")
            for key, value in sm_updater.items():
                if isinstance(value, sp.Basic):
                    value = value.evalf()
                print(f"{key}: {value.subs(model, simultaneous=True)}")
