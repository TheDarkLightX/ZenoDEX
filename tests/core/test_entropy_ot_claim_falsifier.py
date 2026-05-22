from __future__ import annotations

from fractions import Fraction


def test_entropy_regularization_does_not_imply_unique_integer_clearing() -> None:
    # Falsifier for the strong "entropy-regularized OT clearing is uniquely
    # deterministic" claim once you reintroduce *integer* feasibility.
    #
    # Tiny 2x2 transport instance:
    # - supply = [1, 1], demand = [1, 1]
    # - cost matrix is all zeros
    #
    # Over the reals, an entropy-regularized objective has a unique minimizer
    # (it spreads mass). But if you require integer flows, there are multiple
    # optimal solutions with identical (linear) cost.
    supply = (1, 1)
    demand = (1, 1)
    cost = ((0, 0), (0, 0))

    # Enumerate integer-feasible couplings (small enough to do by hand).
    plans = [
        ((1, 0), (0, 1)),
        ((0, 1), (1, 0)),
    ]

    def _is_feasible(plan: tuple[tuple[int, int], tuple[int, int]]) -> bool:
        row0 = plan[0][0] + plan[0][1]
        row1 = plan[1][0] + plan[1][1]
        col0 = plan[0][0] + plan[1][0]
        col1 = plan[0][1] + plan[1][1]
        return (row0, row1) == supply and (col0, col1) == demand and all(x >= 0 for row in plan for x in row)

    def _linear_cost(plan: tuple[tuple[int, int], tuple[int, int]]) -> int:
        return plan[0][0] * cost[0][0] + plan[0][1] * cost[0][1] + plan[1][0] * cost[1][0] + plan[1][1] * cost[1][1]

    assert all(_is_feasible(p) for p in plans)
    costs = [_linear_cost(p) for p in plans]
    assert costs == [0, 0]
    assert plans[0] != plans[1]


def test_entropy_style_fairness_is_sybilable_by_order_splitting() -> None:
    # Falsifier for the naive "entropy makes clearing fair / sybil-resistant" claim.
    #
    # If a scarce unit of output is allocated by an entropy criterion among
    # identical orders, the symmetric optimum is uniform. Splitting an order
    # into many identical sub-orders increases share.
    #
    # This is *not* a DEX settlement spec; it's a minimal warning regression.
    scarce = Fraction(1, 1)

    # Case A: 1 victim + 1 attacker order (2 symmetric orders) => 1/2 each.
    share_attacker_a = scarce * Fraction(1, 2)

    # Case B: victim + attacker split into 2 identical orders (3 symmetric orders) => 1/3 each.
    share_attacker_b = scarce * Fraction(2, 3)

    assert share_attacker_b > share_attacker_a
