from . import Program
from transition import *


class NondetLoop(Program):

    def get_transition_system(self):
        
        x = Variable('x')
        i = Variable('i')

        c = {x: Condition(x > 0), i: Condition(sp.Eq(i, 1))}

        l1 = Location("l1", None, Condition(T), False, True, False)
        l2 = Location("l2", None, Condition(T), True, False, False)
        l3 = Location("l3", None, Condition(T), False, True, False)

        t1 = Transition(l2, Condition(i <= x), Update({x: x, i: i}))
        t2 = Transition(l3, Condition(i > x), Update({x: x, i: i}))
        l1.transitions = [t1, t2]

        non_det_1: NondeterministicVariable = NondetGenerator.generate_nondet_variable('non_det_1', 0.1, 0.2)
        t3 = Transition(l1, Condition(T), Update({x: x, i: i + non_det_1}))
        l2.transitions = [t3]

        l3.transitions = []

        return TransitionSystem("nondet_loop", c, [l1, l2, l3], l1, [x, i], [non_det_1])

    def get_trivial_g(self) -> float:
        return 1.0