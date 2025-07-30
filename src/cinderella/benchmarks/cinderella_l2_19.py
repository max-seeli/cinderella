import os

import sympy as sp

from cinderella import OUT_DIR
from cinderella.executor import execute_polyqent
from cinderella.prefix_parser.parser import parse_expression
from cinderella.template import get_polynomial_expression
from cinderella.witness import construct_constraints

if __name__ == "__main__":
    # -------------------------------------
    # Game Specification
    # -------------------------------------
    eps = 0.1 # bucket size is 2 - eps

    M = sp.Symbol("M")
    variables = [M]
    free_constraints = [M > 0]

    x0, x1, x2, x3, x4 = [sp.Symbol(f"x{i}") for i in range(5)]
    game_variables = [x0, x1, x2, x3, x4]
    game_variable_invariants = [sp.And(x0 >= 0, x1 >= 0, x2 >= 0, x3 >= 0, x4 >= 0)]

    safety_updates = [
        {
            x0: 0,
            x1: 0,
        },
        {
            x1: 0,
            x2: 0,
        },
        {
            x2: 0,
            x3: 0,
        },
        {
            x3: 0,
            x4: 0,
        },
        {
            x4: 0,
            x0: 0,
        }
    ]

    reach_updates = {
            var: get_polynomial_expression(f"{var}_upd", game_variables, degree=1) for var in game_variables
    }

    # Functions over updated vars f: x0', x1', x2', x3', x4' -> T/F
    reach_update_constraints = [
        lambda x0_p, x1_p, x2_p, x3_p, x4_p: sp.GreaterThan(
            1,
            sp.Add((x0_p - x0) * (x0_p - x0),
                   (x1_p - x1) * (x1_p - x1),
                   (x2_p - x2) * (x2_p - x2),
                   (x3_p - x3) * (x3_p - x3),
                   (x4_p - x4) * (x4_p - x4))
        ),
        lambda x0_p, x1_p, x2_p, x3_p, x4_p: sp.And(
            x0_p >= x0,
            x1_p >= x1,
            x2_p >= x2,
            x3_p >= x3,
            x4_p >= x4,
        ),
    ]

    goal = sp.Or(
        x0 > 1 - eps,
        x1 > 1 - eps,
        x2 > 1 - eps,
        x3 > 1 - eps,
        x4 > 1 - eps,
    )

    rank_fn = get_polynomial_expression("rank_fn", game_variables, degree=1)
    ranking_offset = M
    # -------------------------------------


    cs = construct_constraints(
        game_variables,
        game_variable_invariants,
        free_constraints,
        reach_updates,
        reach_update_constraints,
        safety_updates,
        goal,
        rank_fn,
        ranking_offset
    )

    witness_path = os.path.join(OUT_DIR, 'cinderella_l2_19.smt2')
    cs.write_smt2(witness_path)

    result, model = execute_polyqent(witness_path)
    if result == 'sat':
        print("Witness found:")
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        print("M:")
        print(model[sp.Symbol("M")])

        print("Rank Function:")
        print(rank_fn.subs(model, simultaneous=True))
        print("Stepmother Update:")
        for key, value in reach_updates.items():
            if isinstance(value, sp.Basic):
                value = value.evalf()
            print(f"{key}: {value.subs(model, simultaneous=True)}")
