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
    vol = 1
    spillage = 0.2

    M = sp.Symbol("M")
    variables = [M]
    free_constraints = [M > 0]

    x0, x1 = [sp.Symbol(f"x{i}") for i in range(2)]
    game_variables = [x0, x1]
    game_variable_invariants = [sp.And(x0 >= 0, x1 >= 0)]

    x0_spill = sp.Symbol("x0_spill")
    x1_spill = sp.Symbol("x1_spill")
    safety_updates = [
        {
            x0: x0 - x0_spill,
            x1: x1 - x1_spill
        },
    ]

    reach_updates = {
            x0: get_polynomial_expression(f"x0_upd", game_variables, degree=1),
            x1: get_polynomial_expression(f"x1_upd", game_variables, degree=1)
    }

    # Functions over updated vars f: x0', x1', x2', x3', x4' -> T/F
    reach_update_constraints = [
        lambda x0_p, x1_p: sp.And(
            (x0_p - x0) + (x1_p - x1) <= vol,
            x0_p >= x0, # Does this need to consider spillage?
            x1_p >= x1, # Does this need to consider spillage?
        ),
    ]

    goal = sp.And(
        x0 >= 0,
        x1 >= 0,
        x0 + x1 > 9,
        sp.GreaterThan(x0, 10 * x1 - 1)
    )

    rank_fn = get_polynomial_expression("rank_fn", [x0, x1], degree=1)
    ranking_offset = M

    non_det_aux_vars = [x0_spill, x1_spill]
    non_det_bounds = [
        x0_spill <= spillage / 2,
        x1_spill <= spillage / 2,
        x0_spill >= 0,
        x1_spill >= 0,
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

    witness_path = os.path.join(OUT_DIR, 'robot-cocktail.smt2')
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
