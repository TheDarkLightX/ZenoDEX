# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.cubic_sum_amm import swap_exact_in_cubic_sum, swap_exact_out_cubic_sum


def _k(*, x: int, y: int, p: int, q: int) -> int:
    return x * y * (p * x + q * y)


def _bruteforce_exact_in(*, x: int, y: int, dx: int, p: int, q: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("empty reserves")
    if dx <= 0:
        raise ValueError("dx must be positive")
    k0 = _k(x=x, y=y, p=p, q=q)
    x1 = x + dx
    # y' is the minimal y' in [0..y] with K(x1,y') >= k0
    for y1 in range(0, y + 1):
        if _k(x=x1, y=y1, p=p, q=q) >= k0:
            return y1
    raise ValueError("no feasible y' found (should be impossible for finite y)")


def _fee_total(*, gross: int, fee_bps: int) -> int:
    if gross < 0:
        raise ValueError("gross must be non-negative")
    if not (0 <= fee_bps <= 10000):
        raise ValueError("fee_bps must be in [0,10000]")
    if gross == 0 or fee_bps == 0:
        return 0
    return (gross * fee_bps + 9999) // 10000


def _bruteforce_exact_in_fee(*, x: int, y: int, dx_gross: int, p: int, q: int, fee_bps: int) -> tuple[int, int, int]:
    if dx_gross <= 0:
        raise ValueError("dx must be positive")
    fee = _fee_total(gross=dx_gross, fee_bps=fee_bps)
    dx_net = dx_gross - fee
    if dx_net <= 0:
        raise ValueError("dx too small after fee")
    y1 = _bruteforce_exact_in(x=x, y=y, dx=dx_net, p=p, q=q)
    return y1, dx_net, fee


def _bruteforce_exact_out(*, x: int, y: int, dy: int, p: int, q: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("empty reserves")
    if dy <= 0 or dy >= y:
        raise ValueError("invalid dy")
    # Find minimal dx such that exact-in output >= dy.
    # For this bounded test, a conservative upper bound is enough.
    max_dx = 8 * (x + y + 1)
    for dx in range(1, max_dx + 1):
        y1 = _bruteforce_exact_in(x=x, y=y, dx=dx, p=p, q=q)
        if (y - y1) >= dy:
            return dx
    raise ValueError("no feasible dx found within bound")


def _bruteforce_exact_out_fee(*, x: int, y: int, dy: int, p: int, q: int, fee_bps: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("empty reserves")
    if dy <= 0 or dy >= y:
        raise ValueError("invalid dy")
    max_dx = 12 * (x + y + 1)
    for dx_gross in range(1, max_dx + 1):
        try:
            y1, _, _ = _bruteforce_exact_in_fee(x=x, y=y, dx_gross=dx_gross, p=p, q=q, fee_bps=fee_bps)
        except ValueError:
            continue
        if (y - y1) >= dy:
            return dx_gross
    raise ValueError("no feasible dx found within bound")


@pytest.mark.parametrize("p,q", [(1, 1), (2, 1), (1, 3)])
def test_exact_in_matches_bruteforce_small_grid(p: int, q: int) -> None:
    for x in range(1, 25):
        for y in range(1, 25):
            k0 = _k(x=x, y=y, p=p, q=q)
            for dx in range(1, 25):
                y1 = _bruteforce_exact_in(x=x, y=y, dx=dx, p=p, q=q)
                out = y - y1
                if out <= 0:
                    with pytest.raises(ValueError):
                        swap_exact_in_cubic_sum(x, y, dx, p=p, q=q)
                    continue
                out2, (x2, y2) = swap_exact_in_cubic_sum(x, y, dx, p=p, q=q)
                assert out2 == out
                assert (x2, y2) == (x + dx, y1)
                assert _k(x=x2, y=y2, p=p, q=q) >= k0


@pytest.mark.parametrize("p,q", [(1, 1), (2, 1), (1, 3)])
def test_exact_out_minimality_and_no_underdelivery_small_grid(p: int, q: int) -> None:
    for x in range(1, 20):
        for y in range(2, 20):
            k0 = _k(x=x, y=y, p=p, q=q)
            for dy in range(1, y):
                dx = _bruteforce_exact_out(x=x, y=y, dy=dy, p=p, q=q)
                dx2, (x2, y2) = swap_exact_out_cubic_sum(x, y, dy, p=p, q=q)
                assert dx2 == dx
                assert (x2, y2) == (x + dx, y - dy)
                assert _k(x=x2, y=y2, p=p, q=q) >= k0

                # No underdelivery: exact-in with dx must output at least dy.
                out_check, _ = swap_exact_in_cubic_sum(x, y, dx, p=p, q=q)
                assert out_check >= dy

                # Minimality: dx-1 must fail to reach dy.
                if dx > 1:
                    try:
                        out_prev, _ = swap_exact_in_cubic_sum(x, y, dx - 1, p=p, q=q)
                        assert out_prev < dy
                    except ValueError:
                        pass


@pytest.mark.parametrize("p,q,fee_bps", [(1, 1, 30), (2, 1, 50), (1, 3, 100)])
def test_exact_in_fee_matches_bruteforce_tiny_grid(p: int, q: int, fee_bps: int) -> None:
    for x in range(1, 15):
        for y in range(1, 15):
            k0 = _k(x=x, y=y, p=p, q=q)
            for dx_gross in range(1, 30):
                try:
                    y1, dx_net, fee = _bruteforce_exact_in_fee(
                        x=x, y=y, dx_gross=dx_gross, p=p, q=q, fee_bps=fee_bps
                    )
                except ValueError:
                    with pytest.raises(ValueError):
                        swap_exact_in_cubic_sum(x, y, dx_gross, p=p, q=q, fee_bps=fee_bps)
                    continue

                out = y - y1
                if out <= 0:
                    with pytest.raises(ValueError):
                        swap_exact_in_cubic_sum(x, y, dx_gross, p=p, q=q, fee_bps=fee_bps)
                    continue

                out2, (x2, y2) = swap_exact_in_cubic_sum(x, y, dx_gross, p=p, q=q, fee_bps=fee_bps)
                assert out2 == out
                assert (x2, y2) == (x + dx_gross, y1)
                assert _k(x=x2, y=y2, p=p, q=q) >= k0
                assert dx_net == dx_gross - fee


@pytest.mark.parametrize("p,q,fee_bps", [(1, 1, 30), (2, 1, 50), (1, 3, 100)])
def test_exact_out_fee_minimality_tiny_grid(p: int, q: int, fee_bps: int) -> None:
    for x in range(2, 12):
        for y in range(3, 12):
            k0 = _k(x=x, y=y, p=p, q=q)
            for dy in range(1, min(6, y - 1)):
                dx_brute = _bruteforce_exact_out_fee(x=x, y=y, dy=dy, p=p, q=q, fee_bps=fee_bps)
                dx2, (x2, y2) = swap_exact_out_cubic_sum(x, y, dy, p=p, q=q, fee_bps=fee_bps)
                assert dx2 == dx_brute
                assert (x2, y2) == (x + dx2, y - dy)
                assert _k(x=x2, y=y2, p=p, q=q) >= k0

                out_check, _ = swap_exact_in_cubic_sum(x, y, dx2, p=p, q=q, fee_bps=fee_bps)
                assert out_check >= dy

                if dx2 > 1:
                    try:
                        out_prev, _ = swap_exact_in_cubic_sum(x, y, dx2 - 1, p=p, q=q, fee_bps=fee_bps)
                        assert out_prev < dy
                    except ValueError:
                        pass
