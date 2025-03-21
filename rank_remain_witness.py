from __future__ import annotations

import os
from functools import reduce
from itertools import product
from math import ceil, floor
from typing import Any, Dict, List, Tuple, Union
from itertools import product

import sympy as sp

from constraint import ConstraintPair, ConstraintSystem
from transition import *
from template import get_template, get_linear_expression

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

    def find_witness(self) -> Any:


        M = sp.Symbol("M")
        self.cs.add_free_constraint(M > 0.05)

        for l in self.ts.locations:
            if l.name == "goal":
                continue

            # One active ranking function
            exists_sat_rank_part = ConstraintPair(
                self.program_variables,
                sp.And(l.invariant, *[sp.Not(part["guard"]) for part in self.ranking_function[:-1]]),
                self.ranking_function[-1]["guard"],
            )
            self.cs.add_constraint_pair(exists_sat_rank_part)


            # One active transition
            transition_guards = [t.guard.formula for t in l.transitions]
            exists_sat_trans_guards = ConstraintPair(
                self.program_variables,
                sp.And(l.invariant, *[sp.Not(t_guard) for t_guard in transition_guards[:-1]]),
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

        for l in self.ts.locations: # TODO: Remove this line 
            # Rank Constraints
            for t in l.transitions:
                if t.target.name == "goal":
                    continue
                for part_curr, part_succ in product(self.ranking_function, repeat=2):

                    rank_magnitude = part_curr["func"] - M if l.is_angelic else part_curr["func"]
                    
                    rank_after_transition = t.update(part_succ["func"])
                    guard_after_transition = t.update(part_succ["guard"])

                    angelic_ranks = ConstraintPair(
                        self.program_variables + [sp.Symbol(f"rank_{l.name}_{t.target.name}")], # TODO: Remove additional variables
                        sp.And(t.guard.formula, l.invariant, part_curr["guard"], guard_after_transition),
                        sp.And(0 <= rank_after_transition, rank_after_transition <= rank_magnitude)
                    )
                    self.cs.add_constraint_pair(angelic_ranks)

        print(self.cs)
        self.cs.write_smt2(os.path.join(
            FILE_LOCATION, 'out', f'{self.ts.name}.smt2'))

    def create_templates(self) -> Tuple[Dict, Dict, Dict]:
        """
        Create the templates for the witness.

        More specifically, create the templates for the functions:
        - f: L x R^n -> R
        - g: Succ -> R
        - t: L_angelic -> Succ
        - h: L x R^n -> R
        - s: TempGuard -> R

        Returns
        -------
        Fs : Dict
            The templates for the ranking functions.
        Gs : Dict
            The templates for the transition value functions.
        Ts : Dict
            The templates for the angelic functions.
        Hs : Dict
            The templates for the heuristic functions.
        Ss : Dict
            The templates for the temporary guard functions.

        """
        # f: L x R^n -> R  "Ranking function" for each location
        Fs = {}
        for i, location in enumerate(self.ts.locations):
            f = get_linear_expression(f'f_{i}', self.ts.program_variables)
            Fs[location] = f

        # g: Succ -> R  Transition value function
        # TODO: renew this
        Gs = {}
        for i, location in enumerate(self.ts.locations):
            for j, transition in enumerate(location.transitions):
                if self.use_trivial_g:
                    g = sp.Number(self.trivial_g)
                else:
                    g = get_linear_expression(
                        f'g_{i}_{j}', self.ts.program_variables)
                Gs[(location, transition)] = g

        # t: L_angelic -> Succ  "Angel" function
        # TODO: renew this
        Ts = {}
        for i, location in enumerate(self.ts.locations):
            if location.is_non_deterministic and location.is_angelic and not location.is_finite:
                transition = location.transitions[0]  # Only one transition
                nondet_vars = transition.update.get_nondet_vars()
                for j, nondet_var in enumerate(nondet_vars):
                    t = get_linear_expression(
                        f't_{i}_{j}', self.ts.program_variables)
                    Ts[(location, nondet_var)] = t

        # h: L -> R  "Heuristic" function
        # TODO: renew this
        Hs = {}
        for i, location in enumerate(self.ts.locations):
            h_conjuncts = []
            for j in range(self.c):
                h_disjuncts = []
                for k in range(self.d):
                    h_disjuncts.append(
                        get_linear_expression(f'h_{i}_{j}_{k}', self.ts.program_variables) >= 0)
                h_conjuncts.append(sp.Or(*h_disjuncts))
            Hs[location] = sp.And(*h_conjuncts)

        return Fs, Gs, Ts, Hs

    def get_templates_from_model(self, model: Dict[str, Union[int, float]]) -> Tuple[Dict, Dict, Dict, Dict]:
        """
        This model takes a model from the SMT2 solver and returns the templates for the witness.

        Parameters
        ----------
        model : Dict[str, Union[int, float]]
            The model from the SMT2 solver.

        Returns
        -------
        Fs : Dict
            The templates for the ranking functions.
        Gs : Dict
            The templates for the transition value functions.
        Ts : Dict
            The templates for the angelic functions.
        Hs : Dict
            The templates for the heuristic functions.
        """
        from prefix_parser.parser import parse_expression
        print(model)
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        initialized_Fs = {}
        for location, F in self.Fs.items():

            initialized_Fs[location] = F.subs(model)

        initialized_Gs = {}
        for (location, transition), G in self.Gs.items():
            initialized_Gs[(location, transition)] = G.subs(model)

        initialized_Ts = {}
        for (location, nondet_var), T in self.Ts.items():
            initialized_Ts[(location, nondet_var)] = T.subs(model)

        initialized_Hs = {}
        for location, H in self.Hs.items():
            initialized_Hs[location] = H.subs(model)

        initialized_Ss = {}
        for (location, transition), S in self.Ss.items():
            initialized_Ss[(location, transition)] = S.subs(model)

        return initialized_Fs, initialized_Gs, initialized_Ts, initialized_Hs, initialized_Ss
