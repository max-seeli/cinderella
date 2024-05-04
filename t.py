from __future__ import annotations
from typing import Any
from functools import reduce
import sympy as sp
import z3

def to_z3(expr):
    if isinstance(expr, sp.LessThan):
        return to_z3(expr.lhs) <= to_z3(expr.rhs)
    elif isinstance(expr, sp.StrictLessThan):
        return to_z3(expr.lhs) < to_z3(expr.rhs)
    elif isinstance(expr, sp.GreaterThan):
        return to_z3(expr.lhs) >= to_z3(expr.rhs)
    elif isinstance(expr, sp.StrictGreaterThan):
        return to_z3(expr.lhs) > to_z3(expr.rhs)
    elif isinstance(expr, sp.Eq):
        return to_z3(expr.lhs) == to_z3(expr.rhs)
    elif isinstance(expr, sp.And):
        return z3.And([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Or):
        return z3.Or([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Not):
        return z3.Not(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Add):
        return z3.Sum([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Mul):
        return z3.Product([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Number):
        return z3.RealVal(expr)
    elif isinstance(expr, sp.UnevaluatedExpr):
        return to_z3(expr.args[0])
    elif isinstance(expr, sp.Symbol):
        return z3.Real(expr.name)
    else:
        raise ValueError(f'Unsupported expression type: {type(expr)}')

class IRW:

    def __init__(self,
                 transition_system: TransitionSystem,
                 k: int
                 ) -> None:
        self.ts = transition_system
        self.k = k

    def find_witness(self) -> Any:

        all_coeffs = []
        final_constraints = []

        epsilon = sp.Symbol('epsilon', real=True, positive=True)
        all_coeffs.append(epsilon)

        As = {}
        Fs = {}
        
        # 1. Create Templates
        for i, location in enumerate(self.ts.locations):
            A = []
            for j in range(self.k):
                # Create a linear inequality on the variables
                A_coeffs = [sp.Symbol(f'c_{i}_{j}_{k}') for k in range(len(self.ts.variables) + 1)]
                all_coeffs.extend(A_coeffs)
                lhs = A_coeffs[0] + sum([coeff * self.ts.variables[j] for j, coeff in enumerate(A_coeffs[1:])])
                A.append(lhs >= 0)
            As[location] = reduce(sp.And, A)

            f_coeffs = [sp.Symbol(f'd_{i}_{j}') for j in range(len(self.ts.variables) + 1)]
            all_coeffs.extend(f_coeffs)
            f = f_coeffs[0] + sum([coeff * self.ts.variables[j] for j, coeff in enumerate(f_coeffs[1:])])
            Fs[location] = f

        # 2a. Compute IRW Constraint Pairs
        def get_xi(location, transition):
            formula = transition.condition.formula

            goal_A = As[transition.target]
            
            for variable, update in transition.update.transform_per_variable.items():
                formula &= goal_A.subs(variable, update)
            
            this_F = Fs[location]
            goal_F = Fs[transition.target]

            for variable, update in transition.update.transform_per_variable.items():
                goal_F = goal_F.subs(variable, update)
            
            formula &= goal_F <= this_F - epsilon
            return formula
        
        Ps = {}
        for i, location in enumerate(self.ts.locations):
            P = []
            for j, transition in enumerate(location.transitions):
                P.append(sp.Not(get_xi(location, transition)))
            P = reduce(sp.And, P)

            this_A = As[location]
            Ps[location] = this_A & P

        Gamma = []
        for i, location in enumerate(self.ts.locations):

            P_i = sp.simplify_logic(Ps[location], form='dnf', force=True)

            components = P_i.args if isinstance(P_i, sp.Or) else [P_i]
            for component in components:
                print("Here:", location.tau.formula)
                Gamma.append((component, location.tau.formula))

        # 2c. Non-Negativity Constraints
        for i, location in enumerate(self.ts.locations):
            
            this_A = As[location]
            this_F = Fs[location]

            Gamma.append((this_A, this_F >= 0))


        # 3. Applying Farkas' Lemma
        for i, (lamb, rho) in enumerate(Gamma):

            components = lamb.args if isinstance(lamb, sp.And) else [lamb]
            
            
            constraints = []
            strict = [isinstance(component, sp.StrictLessThan) for component in components]
            for component in components:
                # Make the right-hand side 0
                assert isinstance(component, sp.LessThan) or isinstance(component, sp.StrictLessThan) or isinstance(component, sp.GreaterThan) or isinstance(component, sp.StrictGreaterThan), f'Unsupported component type: {type(component)}'
                expr = component.lhs - component.rhs
                if isinstance(component, sp.LessThan) or isinstance(component, sp.StrictLessThan):
                    expr = -expr
                constraints.append(expr)
            
            
            # Case 1: -1 >= 0
            case1_constraints = []
            d_coeffs = [sp.Symbol(f'y_{i}_{j}') for j in range(len(components) + 1)]
            all_coeffs.extend(d_coeffs)
            eq = d_coeffs[0] + sum([coeff * constraint for coeff, constraint in zip(d_coeffs[1:], constraints)])

            for coeff in d_coeffs:
                case1_constraints.append(("1", coeff >= 0))

            for j, var in enumerate(self.ts.variables):
                poli = sp.Poly(eq, var)
                coeffs = poli.all_coeffs()
                
                assert len(coeffs) == 2, f'Expected 2 coefficients, got {len(coeffs)}'
                case1_constraints.append(("1", sp.Eq(coeffs[0], 0)))
            
            constant_factor = eq.subs({var: 0 for var in self.ts.variables})
            case1_constraints.append(("1", sp.Eq(constant_factor, -1)))

            # Case 2: 0 > 0
            case2_constraints = []
            z_coeffs = [sp.Symbol(f'z_{i}_{j}') for j in range(len(components) + 1)]
            all_coeffs.extend(z_coeffs)
            eq = z_coeffs[0] + sum([coeff * constraint for coeff, constraint in zip(z_coeffs[1:], constraints)])

            for coeff in z_coeffs:
                case2_constraints.append(("2", coeff >= 0))

            for j, var in enumerate(self.ts.variables):
                poli = sp.Poly(eq, var)
                coeffs = poli.all_coeffs()
                assert len(coeffs) == 2, f'Expected 2 coefficients, got {len(coeffs)}'
                case2_constraints.append(("2", sp.Eq(coeffs[0], 0)))

            constant_factor = eq.subs({var: 0 for var in self.ts.variables})
            case2_constraints.append(("2", sp.Eq(constant_factor, 0)))

            # Ensure that strict is used
            sum_strict_coeff = sp.Add(*[coeff for coeff, strictness in zip(z_coeffs[1:], strict) if strictness])

            case2_constraints.append(("2", sum_strict_coeff > 0))


            # Case 3: alpha_0 + alpha * V >= 0
            case3_constraints = []
            rohs = []
            for r in [rho]: # TODO: for each rho
                # Make the right-hand side 0
                expr = r.lhs - r.rhs
                if isinstance(r, sp.LessThan) or isinstance(r, sp.StrictLessThan):
                    expr = -expr
                rohs.append(expr)
            curr_rho = rohs[0]

            w_coeffs = [sp.Symbol(f'w_{i}_{j}') for j in range(len(components) + 1)]
            all_coeffs.extend(w_coeffs)
            
            for coeff in w_coeffs:
                case3_constraints.append(("3", coeff >= 0))

            eq = w_coeffs[0] + sum([coeff * constraint for coeff, constraint in zip(w_coeffs[1:], constraints)])

            for j, var in enumerate(self.ts.variables):
                poli_lhs = sp.Poly(eq, var)
                coeffs_lhs = poli_lhs.all_coeffs()
                poli_rhs = sp.Poly(curr_rho, var)
                coeffs_rhs = poli_rhs.all_coeffs()
                print(curr_rho)
                print(poli_rhs)
                print(coeffs_lhs)
                assert len(coeffs_lhs) == 2, f'Expected 2 coefficients, got {len(coeffs_lhs)}'
                if len(coeffs_rhs) == 1:
                    coeffs_rhs[0] = 0
                case3_constraints.append(("3", sp.Eq(coeffs_lhs[0], coeffs_rhs[0])))

            constant_factor_lhs = eq.subs({var: 0 for var in self.ts.variables})
            constant_factor_rhs = curr_rho.subs({var: 0 for var in self.ts.variables})
            case3_constraints.append(("3", sp.Eq(constant_factor_lhs, constant_factor_rhs)))

            c1 = sp.And(*[constraint for _, constraint in case1_constraints])
            c2 = sp.And(*[constraint for _, constraint in case2_constraints])
            c3 = sp.And(*[constraint for _, constraint in case3_constraints])
            final_constraints.append(("3", sp.Or(c1, c2, c3)))

        # 4. Computing Initialization Constraints
        initial_location = self.ts.initial_location

        this_A = As[initial_location]

        v_coeffs = [sp.Symbol(f'v_{i}') for i in range(len(self.ts.variables))]
        all_coeffs.extend(v_coeffs)

        for i, (variable, condition) in enumerate(self.ts.assertion.items()):
            final_constraints.append(("4", condition.formula.subs(variable, v_coeffs[i])))

        components = this_A.args if isinstance(this_A, sp.And) else [this_A]
        for component in components:
            final_constraints.append(("4", component.subs({var: val for var, val in zip(self.ts.variables, v_coeffs)})))
        
        
        # 5. Solve the system of constraints
        constraint_system = (constraint for _, constraint in final_constraints)
        print("Checking linearity of the constraint system...")
        #is_linear_system(constraint_system, all_coeffs)      
        converted_constraints = [to_z3(constraint) for constraint in constraint_system]

        print(len(converted_constraints))
        conjuncted_constraints = z3.And(converted_constraints)
        simplified_constraints = z3.simplify(conjuncted_constraints)
        converted_constraints = simplified_constraints.children()
        print(len(converted_constraints))
        for converted_constraint in converted_constraints:
            print(converted_constraint)
            print('-' * 80)

        print("Checking satisfiability of the constraint system...")
        z3.set_param(verbose=2)
        s = z3.Solver()
        s.add(converted_constraints)
        res = s.check()
        if res == z3.sat:
            print("SAT")
            print("Model:")
            for i, v in enumerate(all_coeffs):
                name = v.name
                print(f'{name} = {s.model()[z3.Real(name)]}')
        elif res == z3.unsat:
            print("UNSAT")
        elif res == z3.unknown:
            print("UNKNOWN")
        else:
            print("ERROR", res)
                
                

class TransitionSystem:


    def __init__(self,
                 assertion: dict[Variable, Condition],
                 locations: list[Location],
                 initial_location: Location,
                 variables: list[Variable]
                 ) -> None:
        self.assertion = assertion
        self.locations = locations
        self.initial_location = initial_location
        self.variables = variables

class Location:

    def __init__(self, 
                 transitions: list[Transition],
                 tau: Condition
                 ) -> None:
        self.transitions = transitions
        self.tau = tau

class Transition:

    def __init__(self, 
                 target: Location,
                 condition: Condition,
                 update: Update
                 ) -> None:
        self.target = target
        self.condition = condition
        self.update = update

class Condition:
    
    def __init__(self, formula) -> None:
        self.formula = formula

class Update:

    def __init__(self, transform_per_variable) -> None:
        self.transform_per_variable = transform_per_variable

class Variable(sp.Symbol):

    def __init__(self, 
                 name: str
                 ) -> None:
        super().__init__()
        self.name = name


if __name__ == '__main__':
    x = Variable('x')
    y = Variable('y')

    c = {x: Condition(sp.Eq(x, 10)), y: Condition(y <= 10)}

    l1 = Location(None, Condition(sp.Ge(sp.UnevaluatedExpr(-4444), 0)))
    l2 = Location(None, Condition(sp.Ge(sp.UnevaluatedExpr(-5555), 0)))
    l3 = Location(None, Condition(sp.Ge(sp.UnevaluatedExpr(-6666), 0)))
    l4 = Location(None, Condition(x >= y + 8))

    t1 = Transition(l2, Condition(x < y), Update({x: x, y: y}))
    t2 = Transition(l3, Condition(x < y), Update({x: x, y: y}))
    t3 = Transition(l4, Condition(x >= y), Update({x: x, y: y}))
    l1.transitions = [t1, t2, t3]

    t4 = Transition(l4, Condition(sp.true), Update({x: x, y: y}))
    l2.transitions = [t4]

    t5 = Transition(l4, Condition(sp.true), Update({x: x, y: y}))
    l3.transitions = [t5]

    t6 = Transition(l4, Condition(sp.true), Update({x: x, y: y}))
    l4.transitions = [t6]

    ts = TransitionSystem(c, [l1, l2, l3, l4], l1, [x, y])

    irw = IRW(ts, 1)
    irw.find_witness()