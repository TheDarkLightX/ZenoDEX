from __future__ import annotations

from src.core.cpmm import swap_exact_in


def test_cpmm_exact_in_is_not_commutative_under_integer_rounding() -> None:
    # Falsifier for the strong "abelian network / confluent AMM" claim:
    # even with fee=0, sequential integer-floor CPMM swaps can be order-dependent.
    #
    # Minimal witness mined by brute-force:
    #   reserves (x,y)=(3,7), dx1=2, dx2=3
    # Order (2 then 3): outputs 2 then 1 => final reserves (8,4)
    # Order (3 then 2): outputs 3 then 1 => final reserves (8,3)
    x0, y0 = 3, 7
    dx1, dx2 = 2, 3

    out1, (x1, y1) = swap_exact_in(x0, y0, dx1, 0)
    out2, (x2, y2) = swap_exact_in(x1, y1, dx2, 0)

    out2b, (x1b, y1b) = swap_exact_in(x0, y0, dx2, 0)
    out1b, (x2b, y2b) = swap_exact_in(x1b, y1b, dx1, 0)

    assert (x2, y2) == (8, 4)
    assert (x2b, y2b) == (8, 3)
    assert (x2, y2) != (x2b, y2b)
    assert (out1 + out2) != (out1b + out2b)

