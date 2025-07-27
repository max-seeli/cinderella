from __future__ import annotations

import os
from typing import Any, Dict, Union

import sympy as sp

from cinderella.constraint import ConstraintPair, ConstraintSystem
from cinderella.template import get_linear_expression, get_polynomial_expression, get_template

from cinderella import OUT_DIR


class TAG:

    def __init__(self,
                 ) -> None:
        self.v1 = 2
        self.v2 = 1
        self.x1 = sp.Symbol("x1")
        self.x2 = sp.Symbol("x2")
        self.x2_d = sp.Symbol("x2_d")
        self.M = sp.Symbol("M")

        self.cs = ConstraintSystem()
        self.functional_frames = []

    def find_witness(self) -> Any:

        # Add free constraints
        self.cs.add_free_constraint(self.M > 0)

        self.P1_update = {
                self.x1: get_polynomial_expression("x1_upd", 
                                                   [self.x1, self.x2],
                                                   degree=1),
            }
        #self.P1_update[self.x1] = self.x1 + self.v1

        # P2 updates
        P2_update = {
            self.x2: self.x2 + self.x2_d,
        }

        # Ranking function - distance of P1 to P2
        self.rank_fn = get_polynomial_expression("rank_fn", 
                                            [self.x1, self.x2],
                                            degree=1) # (self.x1 - self.x2) ** 2
        #self.rank_fn = 100 - self.x1


        # Goal - P1 is close (within eps) to P2
        intermediate_goal = sp.And(
            sp.LessThan(self.x1 - self.x2, self.v1),
            sp.GreaterThan(self.x1 - self.x2, -self.v1),
        )

        # Make sure the game is played within some boundaries
        enforce_boundaries = sp.And(
            self.x1 >= 0,
            self.x2 >= 0,
            self.x1 <= 100,
            self.x2 <= 100,
        )

        # Make sure P1 moves with velocity at most v1
        enforce_P1_velocity = sp.And(
            (self.x1 - self.P1_update[self.x1]) <= self.v1,
            (self.x1 - self.P1_update[self.x1]) >= -self.v1
        )
        
        enforce_P2_velocity = sp.And(
            self.x2_d <= self.v2,
            self.x2_d >= -self.v2)
        

        # Ensure that ranking function is non-negative
        updates_correct = ConstraintPair(
            [self.x1, self.x2],
            sp.And(enforce_boundaries, sp.Not(intermediate_goal)),
            sp.And(self.rank_fn >= 0)
        )
        self.cs.add_constraint_pair(updates_correct)


        # Ranking constraint
        rank_fn_upd = self.rank_fn.subs(P2_update, simultaneous=True).subs(
            self.P1_update, simultaneous=True)
        rank_constraint = ConstraintPair(
            [self.x1, self.x2, self.x2_d],
            sp.And(enforce_boundaries, 
                   sp.Not(intermediate_goal), 
                   #self.rank_fn >= 0, # Should be implied by the previous constraint
                   enforce_P2_velocity, 
                   enforce_boundaries.subs(P2_update, simultaneous=True),
                   self.x1 < self.x2),
            sp.And(
                sp.LessThan(rank_fn_upd, self.rank_fn - self.M),
                enforce_P1_velocity,
                enforce_boundaries.subs(P2_update, simultaneous=True).subs(self.P1_update, simultaneous=True))
        )
        self.cs.add_constraint_pair(rank_constraint)

        print(self.cs)
        self.cs.write_smt2(OUT_DIR / 'tag.smt2')

    
    def print_model(self, model: Dict[str, Union[int, float]]):
        """
        Print the model of the SMT2 solver in a human-readable format.

        Parameters
        ----------
        model : Dict[str, Union[int, float]]
            The model from the SMT2 solver.

        """
        from cinderella.prefix_parser.parser import parse_expression
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        #print("M:")
        #print(model[sp.Symbol("M")])

        print("M:")
        print(model[sp.Symbol("M")])

        print("Updates:")
        print("P1 update:", self.P1_update[self.x1].subs(model, simultaneous=True))

        print("Ranking function:")
        print(self.rank_fn)
        print(self.rank_fn.subs(model, simultaneous=True))

        

if __name__ == "__main__":
    import argparse
    from cinderella.executor import execute_polyqent

    parser = argparse.ArgumentParser(
        description='Find a witness for a given program', allow_abbrev=False)
    args = parser.parse_args()

    witness = TAG()
    
    witness_path = os.path.join(OUT_DIR, 'tag_linear.smt2')
    witness.find_witness()
    witness.cs.write_smt2(witness_path)

    result, model = execute_polyqent(witness_path)
    if result == 'sat':
        print("Witness found:")
        witness.print_model(model)
