from __future__ import annotations
from typing import Any, Tuple, Union, Dict, List
from functools import reduce
import subprocess
import os
import regex as re
import sympy as sp

from constraint import ConstraintSystem, ConstraintPair
from transition import *

FILE_LOCATION = os.path.dirname(os.path.realpath(__file__))
T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)


class CINDem:

    def __init__(self,
                 transition_system: TransitionSystem,
                 k: int
                 ) -> None:
        self.ts = transition_system
        self.k = k


    def find_witness(self) -> Any:
        
        cs = ConstraintSystem(self.ts.variables, True)

        # 1. Generates invariants using ASPIC
        ts.generate_invariants()
        
        # 2. Positive constant 'M'
        M = sp.Symbol('M')
        cs.add_free_constraint(sp.And(M >= 0, *[aux.get_nondet_constraint() for aux in self.ts.aux_variables]))

        # 3. Create the templates for the witness
        Fs, Gs, Ts = self.create_templates()
        for location, F in Fs.items():
            print(location.name, F)
        for (location, transition), G in Gs.items():
            print(location.name, transition.target.name, G)
        for location, T_func in Ts.items():
            print(location.name, T_func)
        # 4. Initial condition
        cs.add_constraint_pair((self.ts.full_assertion, Fs[self.ts.initial_location] >= 0))
        
        # 5. Angelic and demonic location constraints
        for location in self.ts.locations:
            this_f = Fs[location]
            if location.is_angelic:
                # 5a. Angelic location constraints
                if location.is_finite:
                    # I(s0) & (f(s0) - f(s1) < 1/g(s0, s1)) & (f(s0) - f(s2) < 1/g(s0, s2)) 
                    #       & ... => (f(s0) - f(sN) >= 1/g(s0, sN))
                    # Transformed to:
                    # I(s0) & ((f(s0) - f(s1)) * g(s0, s1) < 1) & ((f(s0) - f(s2)) * g(s0, s2) < 1)
                    #       & ... => ((f(s0) - f(sN)) * g(s0, sN) >= 1)
                    location_conjunct = T
                    for transition in location.transitions[:-1]:
                        target_f = Fs[transition.target].subs(transition.update.transform_per_variable)
                        location_conjunct &= sp.Or((this_f - target_f) * Gs[(location, transition)] < -1, sp.Not(transition.guard.formula))

                    lst_transition = location.transitions[-1]
                    target_f = Fs[lst_transition.target].subs(lst_transition.update.transform_per_variable)
                    pair = ConstraintPair(
                        location_conjunct,
                        ((this_f - target_f) * Gs[(location, lst_transition)] >= -1) & lst_transition.guard.formula,
                        [location.invariant.formula]
                    )
                    cs.add_constraint_pair(pair)
                else:
                    # I(s0) & I(s1) => (f(s0) >= f(t(s1)) - 1/g(s0, s1))
                    # Transformed to:
                    # I(s0) & I(s1) => (f(s0) - f(t(s1)) * g(s0, s1) >= -1)
                    #
                    # f(s0) := f_0 + f_1 * x_1 + ... + f_n * x_n
                    # t(s0) := t_0 + t_1 * x_1 + ... + t_n * x_n
                    # f(t(s0)) := f_0 + f_1 * t(s0) + ... + f_n * t(s0)
                    # TODO: Is this correct? Should it be f(s0) >= f(t(s1)) + 1/g(s0, s1)?
                    if len(location.transitions) != 1:
                        raise ValueError('Angelic infinite location must have exactly one transition.')
                    transition = location.transitions[0]
                    target_f = Fs[transition.target].subs({var: Ts[location] for var in self.ts.variables})
                    target_f = target_f.subs(transition.update.transform_per_variable)
                    
                    pair = ConstraintPair(
                        transition.guard.formula,
                        (Fs[location] - target_f) * Gs[(location, transition)] >= - 1,
                        [location.invariant.formula, transition.target_invariant()]
                    )
                    cs.add_constraint_pair(pair)
            
            else:
                # 5b. Demonic location constraints
                # I(s0) & I(s1) & guard(s0, s1) => f(s0) >= f(s1) - 1/g(s0, s1)
                # Transformed to:
                # I(s0) & I(s1) & guard(s0, s1) => f(s0) - f(s1) * g(s0, s1) >= -1
                # TODO: is this correct? Should it be f(s0) >= f(s1) + 1/g(s0, s1)?
                for transition in location.transitions:
                    pair = ConstraintPair(
                        transition.guard.formula,
                        (Fs[location] - Fs[transition.target].subs(transition.update.transform_per_variable)) * Gs[(location, transition)] >= - 1,
                        [location.invariant.formula, transition.target_invariant()]
                    )
                    cs.add_constraint_pair(pair)

        # 6. Decreasing transition value constraints
        # I(s0) & I(s1) & I(s2) => g(s0, s1) - g(s1, s2) <= M
        for location in self.ts.locations:
            for transition1 in location.transitions:
                for transition2 in transition1.target.transitions:
                    target1_invariant = transition1.target_invariant()
                    target2_invariant = transition2.target_invariant(transition1.update.transform_per_variable)
                    pair = ConstraintPair(
                        transition1.guard.formula & transition2.guard.formula.subs(transition1.update.transform_per_variable),
                        Gs[(location, transition1)] - Gs[(transition1.target, transition2)].subs(transition1.update.transform_per_variable) <= M,
                        [location.invariant.formula, target1_invariant, target2_invariant]
                    )
                    cs.add_constraint_pair(pair)
 
        # 7. Non-negativity constraints
        # I(s0) & I(s1) => g(s0, s1) >= 0
        for location in self.ts.locations:
            for transition in location.transitions:
                pair = ConstraintPair(
                    transition.guard.formula,
                    Gs[(location, transition)] >= 0,
                    [location.invariant.formula, transition.target_invariant()]
                )
                cs.add_constraint_pair(pair)

        # 8. Transform constraint pairs to SMT2 format
        print(cs)
        cs.write_smt2(os.path.join(FILE_LOCATION, 'out/test.smt2'))

        
        
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
                g = self.get_linear_expression(f'g_{i}_{j}', self.ts.variables)
                Gs[(location, transition)] = g


        # t: L_angelic -> Succ  "Angel" function 
        Ts = {}
        for i, location in enumerate(self.ts.locations):
            if location.is_angelic:
                t = self.get_linear_expression(f't_{i}', self.ts.variables)
                Ts[location] = t

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

if __name__ == '__main__':
    x = Variable('x')
    i = Variable('i')

    c = {x: Condition(T), i: Condition(sp.Eq(i, 1))}

    l1 = Location("l1", None, Condition(T), True, True)
    l2 = Location("l2", None, Condition(T), True, True)
    l3 = Location("l3", None, Condition(T), False, True)


    t1 = Transition(l2, Condition(T), Update({x: x, i: i}))
    #t2 = Transition(l3, Condition(i > x), Update({x: x, i: i}))
    l1.transitions = [t1]

    non_det_0_1: NondeterministicVariable = NondetGenerator.generate_nondet_variable('non_det_0_1', 0, 1)
    t2 = Transition(l2, Condition(i <= x), Update({x: x, i: i + 1}))
    t3 = Transition(l3, Condition(i > x), Update({x: x, i: i}))
    l2.transitions = [t2, t3]

    #t4 = Transition(l3, Condition(T), Update({x: x}))
    #l3.transitions = [t4]
    l3.transitions = []


    ts = TransitionSystem("example1", c, [l1, l2, l3], l1, [x, i])#, [non_det_0_1])

    cin = CINDem(ts, 1)
    cin.find_witness()


