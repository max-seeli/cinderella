import math

import sympy as sp

from transition import Variable, Condition, Location, Transition, Update, TransitionSystem
from template import get_template, get_linear_expression
from . import Program

T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)


class Cinderella(Program):

    def __init__(self, eps, num_buckets=5):
        self.c_thresh = 2 - eps
        self.eps = eps
        self.num_buckets = num_buckets

    def get_transition_system(self):

        buckets = [Variable(f'x{i}') for i in range(self.num_buckets)]

        assertion = {bucket: Condition(sp.Eq(bucket, 0)) for bucket in buckets}

        non_neg_buckets = sp.And(*[bucket >= 0 for bucket in buckets])
        non_overflow_buckets = sp.And(
            *[bucket <= self.c_thresh for bucket in buckets])

        sm = Location(
            name="stepmother",
            transitions=None,  # added below
            invariant=sp.And(non_neg_buckets, non_overflow_buckets),
            is_non_deterministic=True,
            is_angelic=True)

        """
        inter = Location(
            name="inter",
            transitions=None,  # added below
            invariant=T,
            is_non_deterministic=False,
            is_angelic=False)
        """
            
        cind = Location(
            name="cind",
            transitions=None,  # added below
            invariant=sp.And(non_neg_buckets, non_overflow_buckets, sp.Eq(buckets[1], buckets[3])), 
            is_non_deterministic=True,
            is_angelic=False)

        goal = Location(
            name="goal",
            transitions=[],
            invariant=T,
            is_non_deterministic=False,
            is_angelic=False)

        # Stepmother transitions:
        sm1 = Transition(cind,
                         Condition(sp.And(sp.LessThan(buckets[1], 1 - self.eps), sp.LessThan(buckets[3], 1 - self.eps))), Update({
                             buckets[1]: buckets[1] * 0.5 + buckets[3] * 0.5 + 0.5,
                             buckets[3]: buckets[1] * 0.5 + buckets[3] * 0.5 + 0.5
                         }))

        sm2 = Transition(goal,
                         Condition(sp.StrictGreaterThan(buckets[1], 1 - self.eps)), Update({
                             buckets[1]: buckets[1] + 1.0
                         }))

        sm3 = Transition(goal,
                         Condition(sp.StrictGreaterThan(buckets[3], 1 - self.eps)), Update({
                             buckets[3]: buckets[3] + 1.0
                         }))
        
        sm.transitions = [sm1, sm2, sm3]

        """
        # Inter transitions:
        inter1 = Transition(cind, Condition(sp.And(*[bucket <= self.c_thresh for bucket in buckets])), Update({}))
        inter2 = Transition(goal, Condition(sp.Or(*[bucket > self.c_thresh for bucket in buckets])), Update({}))
        inter.transitions = [inter1, inter2]
        """
        
        # Cinderella transitions:
        cind1 = Transition(sm, Condition(T), Update({
            buckets[0]: 0,
            buckets[1]: 0,
        }))
        cind.transitions = [cind1]
        
        ts = TransitionSystem("cinderella", assertion, [
                              sm, cind, goal], sm, buckets)
        return ts
