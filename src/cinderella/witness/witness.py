import sympy as sp

from cinderella.constraint import ConstraintSystem, ConstraintPair


def construct_constraints(game_variables: list[sp.Symbol],
         game_variable_invariants: list[sp.Basic],
         free_constraints: list[sp.Basic],
         reach_updates: dict[sp.Symbol, sp.Basic],
         reach_update_constraints: list[sp.Basic],
         safety_updates: list[dict[sp.Symbol, sp.Basic]],
         goal: sp.Basic,
         rank_fn: sp.Basic,
         ranking_offset: sp.Basic,
         non_det_aux_vars: list[sp.Symbol] = [],
         non_det_bounds: list[sp.Basic] = [],
         use_target_not_reached: bool = False) -> ConstraintSystem:

    # Construct the constraint system
    cs = ConstraintSystem()


    for fc in free_constraints:
        cs.add_free_constraint(fc)


    reach_update_constraints = [
        constraint(*[reach_updates[var] for var in game_variables])
        for constraint in reach_update_constraints
    ]

    # Ensure update correctness
    updates_correct = ConstraintPair(
        game_variables, sp.And(*game_variable_invariants), sp.And(*reach_update_constraints)
    )
    cs.add_constraint_pair(updates_correct)

    # Ensure that the ranking function is non-negative
    
    rank_non_neg = ConstraintPair(
        game_variables,
        sp.And(*game_variable_invariants, sp.Not(goal)),
        sp.And(rank_fn >= 0),
    )
    cs.add_constraint_pair(rank_non_neg)
    
    for update in safety_updates:
        # Ranking Constraint
        target_not_reached = sp.Not(goal).simplify()
        target_not_reached_upd = target_not_reached.subs(update, simultaneous=True).subs(
            reach_updates, simultaneous=True
        )

        rank_fn_upd = rank_fn.subs(update, simultaneous=True).subs(
            reach_updates, simultaneous=True
        )

        game_variable_invariants_upd = [
            inv.subs(update, simultaneous=True).subs(reach_updates, simultaneous=True)
            for inv in game_variable_invariants
        ]
        game_variable_invariants_after_safety = [
            inv.subs(update, simultaneous=True) for inv in game_variable_invariants
        ]

        rank_correct = ConstraintPair(
            game_variables + non_det_aux_vars,  # Add infinite nondeterminism variables
            sp.And(
                *game_variable_invariants,
                target_not_reached if use_target_not_reached else sp.true,
                target_not_reached_upd,
                *non_det_bounds,
                *game_variable_invariants_after_safety,
            ),  # Add infinite nondeterminism limits (ensure that only when invariants are satisfied with infinite nondeterminism, the lhs is satisfied, i.e. update the invariants)
            sp.And(rank_fn - rank_fn_upd >= ranking_offset, *game_variable_invariants_upd),
        )
        cs.add_constraint_pair(rank_correct)

    return cs
