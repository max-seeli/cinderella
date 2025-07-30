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
    eps = sp.Symbol("eps") # bucket size is 2 - eps
    t = sp.Symbol("t")
    
    free_constraints = [t > 0]
    fct_eps = t * eps

    x0, x1, x2, x3, x4 = [sp.Symbol(f"x{i}") for i in range(5)]
    game_variables = [x0, x1, x2, x3, x4, eps]
    game_variable_invariants = [sp.And(x0 >= 0, x1 >= 0, x2 >= 0, x3 >= 0, x4 >= 0, eps > 0, eps < 1)]

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
    reach_updates[eps] = eps

    # Functions over updated vars f: x0', x1', x2', x3', x4' -> T/F
    reach_update_constraints = [
        lambda x0_p, x1_p, x2_p, x3_p, x4_p, eps: sp.GreaterThan(
            sp.Add(x0, x1, x2, x3, x4) + 1,
            sp.Add(x0_p, x1_p, x2_p, x3_p, x4_p)
        ),
        lambda x0_p, x1_p, x2_p, x3_p, x4_p, eps: sp.And(
            x0_p >= x0,
            x1_p >= x1,
            x2_p >= x2,
            x3_p >= x3,
            x4_p >= x4,
        ),
    ]

    goal = sp.Or(
        x1 > 1 - eps,
        x3 > 1 - eps,
    )

    rank_fn = get_polynomial_expression("rank_fn", [x0, x1, x2, x3, x4], degree=1)
    ranking_offset = fct_eps
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
        use_target_not_reached=True,
    )

    witness_path = os.path.join(OUT_DIR, 'cinderella_vareps.smt2')
    cs.write_smt2(witness_path)

    result, model = execute_polyqent(witness_path)
    if result == 'sat':
        print("Witness found:")
        model = {sp.Symbol(key): parse_expression(value)
                 for key, value in model.items()}

        print("t:")
        print(model[sp.Symbol("t")])

        print("Rank Function:")
        print(rank_fn.subs(model, simultaneous=True))
        print("Stepmother Update:")
        for key, value in reach_updates.items():
            if isinstance(value, sp.Basic):
                value = value.evalf()
            print(f"{key}: {value.subs(model, simultaneous=True)}")
