import os

import sympy as sp

from cinderella import OUT_DIR
from cinderella.executor import execute_polyqent
from cinderella.prefix_parser.parser import parse_expression
from cinderella.template import get_polynomial_expression
from cinderella.witness.witness import construct_constraints

if __name__ == "__main__":
    # -------------------------------------
    # Game Specification
    # -------------------------------------
    v0, v1 = 2, 1

    M = sp.Symbol("M")
    variables = [M]
    free_constraints = [M > 0]

    x0, x1 = [sp.Symbol(f"x{i}") for i in range(2)]
    game_variables = [x0, x1]
    game_variable_invariants = [sp.And(x0 >= 0, x1 >= 0, x0 <= 100, x1 <= 100, x0 <= x1)]

    x1_d = sp.Symbol("x1_d")
    safety_updates = [
        {
            x1: x1 + x1_d,
        },
    ]

    reach_updates = {
            x0: get_polynomial_expression(f"x0_upd", game_variables, degree=1),
            x1: x1
    }

    # Functions over updated vars f: x0', x1', x2', x3', x4' -> T/F
    reach_update_constraints = [
        lambda x0_p, x1_p: sp.And(
            x0 - reach_updates[x0] <= v0,
            x0 - reach_updates[x0] >= -v0,
        ),
    ]

    goal = sp.And(
        sp.LessThan(x0 - x1, v1),
        sp.GreaterThan(x0 - x1, -v1),
    )

    rank_fn = get_polynomial_expression("rank_fn", [x0, x1], degree=1)
    ranking_offset = M

    non_det_aux_vars = [x1_d]
    non_det_bounds = [
        x1_d <= v1,
        x1_d >= -v1,
    ]
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
        ranking_offset,
        non_det_aux_vars=non_det_aux_vars,
        non_det_bounds=non_det_bounds,
        use_target_not_reached=True,
    )

    witness_path = os.path.join(OUT_DIR, 'tag.smt2')
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
        print("Player 1 Update:")
        for key, value in reach_updates.items():
            if isinstance(value, sp.Basic):
                value = value.evalf()
            print(f"{key}: {value.subs(model, simultaneous=True)}")
