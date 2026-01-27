# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.sum_boost_amm import swap_exact_in_sum_boost, swap_exact_out_sum_boost


def _k(*, x: int, y: int, mu_num: int, mu_den: int) -> int:
    s = x + y
    return x * y * s * (mu_den + mu_num * s)


def _bruteforce_exact_in(*, x: int, y: int, dx_net: int, mu_num: int, mu_den: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("empty reserves")
    if dx_net <= 0:
        raise ValueError("dx must be positive")
    k0 = _k(x=x, y=y, mu_num=mu_num, mu_den=mu_den)
    x1 = x + dx_net
    for y1 in range(0, y + 1):
        if _k(x=x1, y=y1, mu_num=mu_num, mu_den=mu_den) >= k0:
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


def _bruteforce_exact_in_fee(
    *, x: int, y: int, dx_gross: int, mu_num: int, mu_den: int, fee_bps: int
) -> tuple[int, int, int]:
    if dx_gross <= 0:
        raise ValueError("dx must be positive")
    fee = _fee_total(gross=dx_gross, fee_bps=fee_bps)
    dx_net = dx_gross - fee
    if dx_net <= 0:
        raise ValueError("dx too small after fee")
    y1 = _bruteforce_exact_in(x=x, y=y, dx_net=dx_net, mu_num=mu_num, mu_den=mu_den)
    return y1, dx_net, fee


def _bruteforce_exact_out(*, x: int, y: int, dy: int, mu_num: int, mu_den: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("empty reserves")
    if dy <= 0 or dy >= y:
        raise ValueError("invalid dy")
    max_dx = 12 * (x + y + 1)
    for dx in range(1, max_dx + 1):
        y1 = _bruteforce_exact_in(x=x, y=y, dx_net=dx, mu_num=mu_num, mu_den=mu_den)
        if (y - y1) >= dy:
            return dx
    raise ValueError("no feasible dx found within bound")


def _bruteforce_exact_out_fee(*, x: int, y: int, dy: int, mu_num: int, mu_den: int, fee_bps: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("empty reserves")
    if dy <= 0 or dy >= y:
        raise ValueError("invalid dy")
    max_dx = 18 * (x + y + 1)
    for dx_gross in range(1, max_dx + 1):
        try:
            y1, _, _ = _bruteforce_exact_in_fee(
                x=x, y=y, dx_gross=dx_gross, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps
            )
        except ValueError:
            continue
        if (y - y1) >= dy:
            return dx_gross
    raise ValueError("no feasible dx found within bound")


@pytest.mark.parametrize("mu_num,mu_den", [(0, 10_000), (200, 10_000)])
def test_exact_in_matches_bruteforce_small_grid(mu_num: int, mu_den: int) -> None:
    for x in range(1, 20):
        for y in range(1, 20):
            k0 = _k(x=x, y=y, mu_num=mu_num, mu_den=mu_den)
            for dx in range(1, 20):
                y1 = _bruteforce_exact_in(x=x, y=y, dx_net=dx, mu_num=mu_num, mu_den=mu_den)
                out = y - y1
                if out <= 0:
                    with pytest.raises(ValueError):
                        swap_exact_in_sum_boost(x, y, dx, mu_num=mu_num, mu_den=mu_den)
                    continue
                out2, (x2, y2) = swap_exact_in_sum_boost(x, y, dx, mu_num=mu_num, mu_den=mu_den)
                assert out2 == out
                assert (x2, y2) == (x + dx, y1)
                assert _k(x=x2, y=y2, mu_num=mu_num, mu_den=mu_den) >= k0


@pytest.mark.parametrize("mu_num,mu_den", [(0, 10_000), (200, 10_000)])
def test_exact_out_minimality_and_no_underdelivery_small_grid(mu_num: int, mu_den: int) -> None:
    for x in range(1, 16):
        for y in range(2, 16):
            k0 = _k(x=x, y=y, mu_num=mu_num, mu_den=mu_den)
            for dy in range(1, y):
                dx = _bruteforce_exact_out(x=x, y=y, dy=dy, mu_num=mu_num, mu_den=mu_den)
                dx2, (x2, y2) = swap_exact_out_sum_boost(x, y, dy, mu_num=mu_num, mu_den=mu_den)
                assert dx2 == dx
                assert (x2, y2) == (x + dx, y - dy)
                assert _k(x=x2, y=y2, mu_num=mu_num, mu_den=mu_den) >= k0

                out_check, _ = swap_exact_in_sum_boost(x, y, dx, mu_num=mu_num, mu_den=mu_den)
                assert out_check >= dy

                if dx > 1:
                    try:
                        out_prev, _ = swap_exact_in_sum_boost(x, y, dx - 1, mu_num=mu_num, mu_den=mu_den)
                        assert out_prev < dy
                    except ValueError:
                        pass


@pytest.mark.parametrize("mu_num,mu_den,fee_bps", [(0, 10_000, 30), (200, 10_000, 30)])
def test_exact_in_fee_matches_bruteforce_tiny_grid(mu_num: int, mu_den: int, fee_bps: int) -> None:
    for x in range(2, 14):
        for y in range(2, 14):
            k0 = _k(x=x, y=y, mu_num=mu_num, mu_den=mu_den)
            for dx_gross in range(1, 30):
                try:
                    y1, dx_net, fee = _bruteforce_exact_in_fee(
                        x=x, y=y, dx_gross=dx_gross, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps
                    )
                except ValueError:
                    with pytest.raises(ValueError):
                        swap_exact_in_sum_boost(x, y, dx_gross, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps)
                    continue

                out = y - y1
                if out <= 0:
                    with pytest.raises(ValueError):
                        swap_exact_in_sum_boost(x, y, dx_gross, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps)
                    continue

                out2, (x2, y2) = swap_exact_in_sum_boost(x, y, dx_gross, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps)
                assert out2 == out
                assert (x2, y2) == (x + dx_gross, y1)
                assert _k(x=x2, y=y2, mu_num=mu_num, mu_den=mu_den) >= k0
                assert dx_net == dx_gross - fee


@pytest.mark.parametrize("mu_num,mu_den,fee_bps", [(0, 10_000, 30), (200, 10_000, 30)])
def test_exact_out_fee_minimality_tiny_grid(mu_num: int, mu_den: int, fee_bps: int) -> None:
    for x in range(2, 12):
        for y in range(3, 12):
            k0 = _k(x=x, y=y, mu_num=mu_num, mu_den=mu_den)
            for dy in range(1, min(6, y - 1)):
                dx_brute = _bruteforce_exact_out_fee(x=x, y=y, dy=dy, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps)
                dx2, (x2, y2) = swap_exact_out_sum_boost(x, y, dy, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps)
                assert dx2 == dx_brute
                assert (x2, y2) == (x + dx2, y - dy)
                assert _k(x=x2, y=y2, mu_num=mu_num, mu_den=mu_den) >= k0

                out_check, _ = swap_exact_in_sum_boost(x, y, dx2, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps)
                assert out_check >= dy

                if dx2 > 1:
                    try:
                        out_prev, _ = swap_exact_in_sum_boost(
                            x, y, dx2 - 1, mu_num=mu_num, mu_den=mu_den, fee_bps=fee_bps
                        )
                        assert out_prev < dy
                    except ValueError:
                        pass

