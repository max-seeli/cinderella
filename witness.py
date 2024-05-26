from __future__ import annotations
from typing import Any, Tuple, Union, Dict, List
from functools import reduce
import regex as re
import sympy as sp
import z3


T = sp.Ge(sp.UnevaluatedExpr(1), 0)
F = sp.Ge(sp.UnevaluatedExpr(-1), 0)


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
        print(expr.args)
        return z3.Or([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Not):
        return z3.Not(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Add):
        return z3.Sum([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Mul):
        return z3.Product([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Abs):
        return z3.Abs(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Pow):
        return to_z3(expr.base) ** to_z3(expr.exp)
    elif isinstance(expr, sp.Number):
        return z3.RealVal(expr)
    elif isinstance(expr, sp.UnevaluatedExpr):
        return to_z3(expr.args[0])
    elif isinstance(expr, sp.Symbol):
        return z3.Real(expr.name)
    elif isinstance(expr, sp.logic.boolalg.BooleanTrue):
        return z3.BoolVal(True)
    elif isinstance(expr, sp.logic.boolalg.BooleanFalse):
        return z3.BoolVal(False)
    else:
        raise ValueError(f'Unsupported expression type: {type(expr)}')

def inline_let_expressions(smt_code):
    
    # Match all "(assert ...)" expressions, regardless of the content
    matches = re.finditer(r'\(assert\s+((?:[^()]+|\((?1)\))*)\)', smt_code)

    final_smt_code = ""
    # For each match, inline the let expression
    for m in matches:
        
        if "let" not in m.group(1):
            final_smt_code += f"{m.group(0)}\n"
            continue

        # Extract the let expression by name
        lets = re.findall(r'\(let\s+\(((?:[^()]+|\((?1)\))*)\)', m.group(1))

        named_lets = {}
        for let in lets:
            # Extract the name of the let expression
            name_clause = re.finditer(r'\(([\?\$]\w+)\s+(\(((?:[^()]+|\((?3)\))*)\))', let)
            
            for nc in name_clause:
                name, expr = nc.group(1), nc.group(2)
                named_lets[name] = expr

        total_clause = re.search(r'\n\s+(\(=>\s+((?:[^()]+|\((?2)\))*)\))', m.group(1))
        print(total_clause.group(1))
        print(fill_expression(total_clause.group(1), named_lets))
        print()
        final_smt_code += f"(assert \n {fill_expression(total_clause.group(1), named_lets)})\n"

    return final_smt_code

def fill_expression(expr, variables):

    # Substitute every appearance of r'[\?\$]\w+' with the corresponding expression from variables
    while curr_var := re.search(r'[\?\$]\w+', expr):

        if curr_var.group() in variables:
            # Replace the match in the expression with the corresponding expression
            sub_expr = fill_expression(variables[curr_var.group()], variables)
            variables[curr_var.group()] = sub_expr
            expr = re.sub(re.escape(curr_var.group()), sub_expr, expr)
        else:
            raise ValueError(f'Variable {curr_var.group()} not found in variables.')
        
    return expr

class CINDem:

    def __init__(self,
                 transition_system: TransitionSystem,
                 k: int
                 ) -> None:
        self.ts = transition_system
        self.k = k

        self.coeffs: set[sp.Symbol] = set()
        self.constraints: list[sp.core.relational.Relational] = []

    def add_constraint(self, constraint: sp.core.relational.Relational) -> None:
        """
        Add a constraint to the constraint system. Also, register the free
        symbols of the constraint, so that they can be used to compute the
        witness.

        Parameters
        ----------
        constraint : sp.core.relational.Relational
            The constraint to be added to the constraint system.
        """
        self.constraints.append(constraint) 
        self.coeffs.update(constraint.free_symbols)

    def find_witness(self) -> Any:

        

        # 1. Create the constraints
        constraint_pairs = []
        
        # Positive constant 'M'
        M = sp.Symbol('M')
        constraint_pairs.append((T, M >= 0))

        # 2. Create the templates for the witness
        Fs, Gs, Ts = self.create_templates()

        
        # 3. Initial condition
        constraint_pairs.append((self.ts.full_assertion, Fs[self.ts.initial_location] >= 0))
        
        for location in self.ts.locations:
            this_f = Fs[location]
            # 4a. Angelic location constraints
            if location.is_angelic:
                if location.is_finite:
                    location_conjunct = sp.true
                    for transition in location.transitions[:-1]:
                        target_f = Fs[transition.target]
                        location_conjunct &= (this_f - target_f) * Gs[(location, transition)] < 1
                    constraint_pairs.append((location.invariant.formula & location_conjunct, (this_f - Fs[location.transitions[-1].target]) * Gs[(location, location.transitions[-1])] >= 1))
                else:
                    if len(location.transitions) != 1:
                        raise ValueError('Angelic infinite location must have exactly one transition.')
                    target_f = Fs[location.transitions[0].target]
                    target_f = target_f.subs({var: Ts[location] for var in self.ts.variables})
                    
                    constraint_pairs.append((location.invariant.formula, (this_f - target_f) * Gs[(location, location.transitions[0])] >= - 1))
            # 4b. Demonic location constraints
            else:
                for transition in location.transitions:
                    constraint_pairs.append((location.invariant.formula, (Fs[location] - Fs[transition.target]) * Gs[(location, transition)] >= - 1))

        # 5. Decreasing transition value constraints
        for location in self.ts.locations:
            for transition1 in location.transitions:
                for transition2 in transition1.target.transitions:
                    constraint_pairs.append((location.invariant.formula, Gs[(location, transition1)] - Gs[(transition1.target, transition2)] <= M))
 
        # 6. Non-negativity constraints
        for location in self.ts.locations:
            for j, transition in enumerate(location.transitions):
                constraint_pairs.append((location.invariant.formula, Gs[(location, transition)] >= 0))


        # 7. Solve constraint pairs
        print(constraint_pairs)
        s = z3.Solver()
        for lhs, rhs in constraint_pairs:
            s.add(z3.Implies(to_z3(lhs), to_z3(rhs)))
        
        
        smt2 = s.to_smt2()

        # Convert all "(declare-fun <name> () Real)" to "(declare-const <name> Real)"
        declarations = re.search(r'(\(declare-fun [a-zA-Z0-9_]+ \(\) Real\)\s+)+', smt2).group()
        declarations = re.sub(r'\(declare-fun (\w+) \(\) Real\)', r'(declare-const \1 Real)', declarations)
        

        assertions = inline_let_expressions(smt2)

        smt2 = f"""{declarations}{assertions}(check-sat)
(get-model)
        """

        with open('../out/test.smt2', 'w') as f:
            f.write(smt2)

        
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

    @property
    def full_assertion(self) -> sp.Basic:
        return reduce(lambda x, y: x & y, [condition.formula for variable, condition in self.assertion.items()])

class Location:

    def __init__(self, 
                 transitions: list[Transition],
                 invariant: Condition,
                 is_angelic: bool,
                 is_finite: bool
                 ) -> None:
        self.transitions = transitions
        self.invariant = invariant
        self.is_angelic = is_angelic
        self.is_finite = is_finite

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

    c = {x: Condition(x > 0)}

    l1 = Location(None, Condition(T), True, True)
    l2 = Location(None, Condition(T), False, False)
    l3 = Location(None, Condition(T), True, True)


    t1 = Transition(l2, Condition(x > 0), Update({x: x}))
    t2 = Transition(l3, Condition(x <= 0), Update({x: x}))
    l1.transitions = [t1, t2]

    t3 = Transition(l1, Condition(T), Update({x: x - 1}))
    l2.transitions = [t3]

    t4 = Transition(l3, Condition(T), Update({x: x}))
    l3.transitions = [t4]


    ts = TransitionSystem(c, [l1, l2, l3], l1, [x])

    cin = CINDem(ts, 1)
    cin.find_witness()


