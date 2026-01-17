from __future__ import annotations

from src.core.quadratic_cpmm import quadratic_k, swap_exact_in_quadratic, swap_exact_out_quadratic


def test_quadratic_exact_in_invariant_monotone() -> None:
    x, y = 10, 100
    k0 = quadratic_k(x, y)
    out, (x1, y1) = swap_exact_in_quadratic(x, y, 3, fee_bps=0)
    assert out > 0
    assert x1 == x + 3
    assert y1 == y - out
    assert quadratic_k(x1, y1) >= k0


def test_quadratic_exact_out_round_trips() -> None:
    x, y = 7, 200
    desired = 5
    dx, (x1, y1) = swap_exact_out_quadratic(x, y, desired, fee_bps=0)
    assert dx > 0
    out_check, (x2, y2) = swap_exact_in_quadratic(x, y, dx, fee_bps=0)
    assert out_check >= desired
    assert (x1, y1) == (x2, y2)


def test_quadratic_rejects_nonzero_fee_for_now() -> None:
    try:
        swap_exact_in_quadratic(10, 10, 1, fee_bps=1)
        assert False, "expected ValueError"
    except ValueError:
        pass

