from __future__ import annotations
from typing import Any, Tuple, Union, Dict, List
from functools import reduce
import os
import sympy as sp

from constraint import ConstraintSystem, ConstraintPair
from transition import *

FILE_LOCATION = os.path.dirname(os.path.realpath(__file__))
T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)


class CINDem:

    def __init__(self,
                 transition_system: TransitionSystem,
                 use_invariants: bool = False,
                 use_trivial_g: bool = False
                 ) -> None:
        self.ts = transition_system
        self.use_invariants = use_invariants
        self.use_trivial_g = use_trivial_g

        self.cs = ConstraintSystem(self.ts.variables, use_invariants)
        self.Fs, self.Gs, self.Ts = self.create_templates()
        for location, F in self.Fs.items():
            print(f"f({location.name}) = {F}")
        for (location, transition), G in self.Gs.items():
            print(f"g({location.name}, {transition.target.name}) = {G}")
        for (location, nondet_var), T_func in self.Ts.items():
            print(f"t_{nondet_var}({location.name}) = {T_func}")


    def find_witness(self) -> Any:
        

        # 1. Generates invariants using ASPIC
        if self.use_invariants:
            self.ts.generate_invariants()
        
        # 2. Positive constant 'M'
        M = sp.Symbol('M')
        self.cs.add_free_constraint(sp.And(M >= 0))

        # 3. Initial condition
        self.cs.add_constraint_pair((self.ts.full_assertion, self.Fs[self.ts.initial_location] >= 0))
        
        # 4. Angelic and demonic location constraints
        for location in self.ts.locations:
            this_f = self.Fs[location]
            if not location.is_non_deterministic:
                for transition in location.transitions:
                    target_f = transition.update(self.Fs[transition.target])
                    pair = ConstraintPair(
                        transition.guard.formula,
                        ((self.Fs[location] - target_f) * self.Gs[(location, transition)] >= 1) & (target_f >= 0),
                        [location.invariant.formula] #, transition.target_invariant()]
                    )
                    self.cs.add_constraint_pair(pair)
            elif location.is_angelic:
                # 4a. Angelic location constraints
                if location.is_finite:
                    # Only if all transitions have the same guard
                    # I(s0) & guard(s0, sN) & (f(s0) - f(s1) < 1/g(s0, s1) | f(s1) < 0) & (f(s0) - f(s2) < 1/g(s0, s2) | f(s2) < 0) 
                    #       & ... => (f(s0) - f(sN) >= 1/g(s0, sN)) & f(sN) >= 0
                    location_conjunct = T
                    for transition in location.transitions[:-1]:
                        target_f = transition.update(self.Fs[transition.target])
                        location_conjunct &= sp.Or((this_f - target_f) * self.Gs[(location, transition)] < 1, target_f < 0)

                    lst_transition = location.transitions[-1]
                    target_f = lst_transition.update(self.Fs[lst_transition.target])
                    pair = ConstraintPair(
                        location_conjunct & lst_transition.guard.formula,
                        ((this_f - target_f) * self.Gs[(location, lst_transition)] >= 1) & (target_f >= 0),
                        [location.invariant.formula]
                    )
                    self.cs.add_constraint_pair(pair)

                else:
                    # I(s0) & I(s1) & guard(s0, s1) => nondet_constraint(s0, s1) &
                    #       (f(s0) >= f(t(s0)) + 1/g(s0, s1)) & f(t(s0)) >= 0
                    # Where t(s0) is different for each nondet assignment and
                    # nondet_constraint is the conjunction of all nondet assignments:
                    # f(s0) := f_0 + f_1 * x_1 + ... + f_n * x_n
                    # t_i(s0) := t_i_0 + t_i_1 * x_1 + ... + t_i_n * x_n
                    # f(t(s0)) := f_0 + f_1 * t_1(s0) + ... + f_n * t_n(s0)
                    if len(location.transitions) != 1:
                        raise ValueError('Angelic infinite location must have exactly one transition.')
                    
                    nondet_constraint = location.transitions[0].update.get_nondet_constraint()
                    
                    transition = location.transitions[0]
                    target_f = transition.update(self.Fs[transition.target])
                    
                    if transition.additional_update_constraint is not None:
                        nondet_constraint &= transition.additional_update_constraint.formula

                    pair = ConstraintPair(
                        transition.guard.formula,
                        nondet_constraint & ((self.Fs[location] - target_f) * self.Gs[(location, transition)] >= 1) & (target_f >= 0),
                        [location.invariant.formula] #, transition.target_invariant()]
                    )
                    self.cs.add_constraint_pair(pair)
            
            else:
                # 4b. Demonic location constraints
                # I(s0) & I(s1) & guard(s0, s1) => f(s0) >= f(s1) + 1/g(s0, s1)
                # Transformed to:
                # I(s0) & I(s1) & guard(s0, s1) => (f(s0) - f(s1)) * g(s0, s1) >= 1
                for transition in location.transitions:
                    nondet_vars = transition.update.get_nondet_vars()
                    nondet_constraint = transition.update.get_nondet_constraint()

                    target_f = transition.update(self.Fs[transition.target])
                    pair = ConstraintPair(
                        transition.guard.formula & nondet_constraint,
                        ((self.Fs[location] - target_f) * self.Gs[(location, transition)] >= 1) & (target_f >= 0),
                        [location.invariant.formula], #, transition.target_invariant()],
                        additional_all_quantized_vars = nondet_vars 
                    )
                    self.cs.add_constraint_pair(pair)

        # 5. Decreasing transition value constraints
        # I(s0) & I(s1) & I(s2) => g(s0, s1) - g(s1, s2) <= M
        if not self.use_trivial_g:
            for location in self.ts.locations:
                for transition1 in location.transitions:
                    for transition2 in transition1.target.transitions:
                        target1_invariant = transition1.target_invariant()
                        target2_invariant = transition2.target_invariant(transition1.update.get_transform_dict())
                        
                        g_1 = self.Gs[(location, transition1)]
                        g_2 = transition1.update(self.Gs[(transition1.target, transition2)])
                        
                        guard2 = transition1.update(transition2.guard.formula)
                      
                        if location.is_non_deterministic and location.is_angelic and not location.is_finite:
                            
                            pair = ConstraintPair(
                                transition1.guard.formula & guard2,
                                (g_1 - g_2 <= M) & transition1.update.get_nondet_constraint(),
                                [location.invariant.formula] #, target1_invariant, target2_invariant],
                            )
                            self.cs.add_constraint_pair(pair)
    
    
                        elif location.is_non_deterministic and not location.is_angelic and not location.is_finite:
                            nondet_vars = transition1.update.get_nondet_vars()
                            nondet_constraint = transition1.update.get_nondet_constraint()
    
                            pair = ConstraintPair(
                                transition1.guard.formula & guard2 & nondet_constraint,
                                (g_1 - g_2 <= M),
                                [location.invariant.formula, target1_invariant, target2_invariant],
                                additional_all_quantized_vars = nondet_vars
                            )
    
                        else:
                            pair = ConstraintPair(
                                transition1.guard.formula & guard2,
                                (g_1 - g_2 <= M),
                                [location.invariant.formula, target1_invariant, target2_invariant],
                            )
                            self.cs.add_constraint_pair(pair)

                    
 
        # 6. Positivity constraints
        # I(s0) & I(s1) => g(s0, s1) > 0
        if not self.use_trivial_g:
            for location in self.ts.locations:
                for transition in location.transitions:
                    pair = ConstraintPair(
                        transition.guard.formula,
                        self.Gs[(location, transition)] > 0,
                        [location.invariant.formula] #, transition.target_invariant()]
                    )
                    self.cs.add_constraint_pair(pair)

        # 8. Transform constraint pairs to SMT2 format
        angelic_functions = {
            **{sp.Symbol(nondet_var.name): self.Ts[location, nondet_var] for location, nondet_var in self.Ts},
            **{nondet_var: self.Ts[location, nondet_var] for location, nondet_var in self.Ts}
        }

        self.cs.subs(angelic_functions)

        print(self.cs)
        self.cs.write_smt2(os.path.join(FILE_LOCATION, 'out', f'{self.ts.name}.smt2'))

    def create_templates(self) -> Tuple[Dict, Dict, Dict]:
        """
        Create the templates for the witness.

        More specifically, create the templates for the functions:
        - f: L x R^n -> R
        - g: Succ -> R
        - t: L_angelic -> Succ

        Returns
        -------
        Fs : Dict
            The templates for the ranking functions.
        Gs : Dict
            The templates for the transition value functions.
        Ts : Dict
            The templates for the angelic functions.
        
        """
        # f: L x R^n -> R  "Ranking function" for each location
        Fs = {}
        for i, location in enumerate(self.ts.locations):
            f = self.get_linear_expression(f'f_{i}', self.ts.variables)
            Fs[location] = f

        
        # g: Succ -> R  Transition value function
        Gs = {}
        for i, location in enumerate(self.ts.locations):
            for j, transition in enumerate(location.transitions):
                if self.use_trivial_g:
                    g = sp.Integer(1)
                else:
                    g = self.get_linear_expression(f'g_{i}_{j}', self.ts.variables)
                Gs[(location, transition)] = g


        # t: L_angelic -> Succ  "Angel" function 
        Ts = {}
        for i, location in enumerate(self.ts.locations):
            if location.is_non_deterministic and location.is_angelic and not location.is_finite:
                transition = location.transitions[0] # Only one transition
                nondet_vars = transition.update.get_nondet_vars()
                for j, nondet_var in enumerate(nondet_vars):
                    t = self.get_linear_expression(f't_{i}_{j}', self.ts.variables)
                    Ts[(location, nondet_var)] = t

        return Fs, Gs, Ts

    def get_linear_expression(self, coeffs_name: str, variables: List[sp.Symbol]) -> sp.Expr:
        """
        Get a linear expression given the coefficients and the variables.

        Parameters
        ----------
        coeffs_name : str
            The name of the coefficients.
        variables : List[sp.Symbol]
            The variables of the linear expression.

        Returns
        -------
        sp.Expr
            The linear expression.
        """
        coeffs = [sp.Symbol(f'{coeffs_name}_{i}') for i in range(len(variables) + 1)]
        return coeffs[0] + sum([coeff * variable for variable, coeff in zip(variables, coeffs[1:])])
