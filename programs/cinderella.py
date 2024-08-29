import math

import sympy as sp

from transition import *
from witness import CINDem

from . import Program

T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)

class Cinderella(Program):

    def __init__(self, eps, num_buckets=5):
        self.c = 2 - eps
        self.eps = eps
        self.num_buckets = num_buckets

    def get_transition_system(self):

        buckets = [Variable(f'b{i}') for i in range(self.num_buckets)]

        assertion = {bucket: Condition(sp.Eq(bucket, 0)) for bucket in buckets}
        
        invariant_all = sp.And(*[bucket >= 0 for bucket in buckets])
        invariant_sm = sp.And(*[bucket <= self.c for bucket in buckets])
        
        sm = Location("stepmother", None, Condition(sp.And(invariant_all, invariant_sm, sp.And(buckets[1] <= (1 - self.eps), buckets[3] <= (1 - self.eps)))), False, True, False)
        cind = Location("cind", None, Condition(sp.simplify(
            sp.And(
                invariant_all, 
                sp.Or(buckets[1] > (2 - self.eps), buckets[3] > (2 - self.eps), sp.Eq(buckets[1], buckets[3])),
                sp.Not(sp.Or(buckets[1] > (2 - self.eps), buckets[3] > (2 - self.eps), sp.And(buckets[1] > (1 - self.eps), buckets[3] > (1 - self.eps))))))), True, False, True)
        goal = Location("goal", [], Condition(invariant_all), False, False, False)

        print("Please,", cind.invariant.formula)

        """
        # Actual Cinderella program
        nondet_water_split = [NondetGenerator.generate_nondet_variable(f'non_det_water_split{i}', 0, 1) for i in range(self.num_buckets)]
        t1 = Transition(cind,
                        Condition(T),
                        Update({bucket: bucket + add_water for bucket, add_water in zip(buckets, nondet_water_split)}),
                        additional_update_constraint=Condition(sp.Eq(sp.Add(*nondet_water_split), 1)))
        sm.transitions = [t1]
        """
        
        # Precalculation cinderella program
        t1 = Transition(cind,
                        Condition(buckets[1] > 1 - self.eps),
                        Update({buckets[1]: buckets[1] + 1}))
        t2 = Transition(cind,
                        Condition(buckets[3] > 1 - self.eps),
                        Update({buckets[3]: buckets[3] + 1}))
        t3 = Transition(cind,
                        Condition(sp.And(buckets[1] <= 1 - self.eps, buckets[3] <= 1 - self.eps)),
                        Update({
                            buckets[1]: 0.5 * (buckets[1] + buckets[3] + 1),
                            buckets[3]: 0.5 * (buckets[1] + buckets[3] + 1)
                        }))
        sm.transitions = [t1, t2, t3] 
        
        overflow_condition = sp.Or(*[bucket > self.c for bucket in buckets])
        not_overflow_condition = sp.simplify_logic(sp.Not(overflow_condition))
        cind.transitions = []
        for i in range(self.num_buckets):
            t = Transition(sm, 
                           Condition(not_overflow_condition), 
                           Update({buckets[i]: sp.Integer(0), buckets[(i + 1) % self.num_buckets]: sp.Integer(0)}))
            cind.transitions.append(t)
        cind.transitions.append(Transition(goal, Condition(overflow_condition), Update({})))

        ts = TransitionSystem("cinderella", assertion, [sm, cind, goal], sm, buckets)#, nondet_water_split)
        return ts
    
    def get_trivial_g(self):
        return math.ceil((2/self.eps) * 100) / 100

if __name__ == "__main__":
    c = 0.8
    cg = Cinderella(c, num_buckets=5)
    ts = cg.get_transition_system()
    cin = CINDem(ts, True, trivial_g=False)
    cin.find_witness()
