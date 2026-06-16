from __future__ import annotations

import pytest

from src.core.perp_rounding import euclid_div_rem, largest_remainder_adjust_net_zero


def test_rounding_leak_witness_under_euclidean_division() -> None:
    # Mirrors the minimal witness recorded in:
    # internal/popperpad_mcp/bootstrap_zenodex_pad.py
    #
    # With net-zero exposures, per-account Euclidean division can leak value:
    # xs = [1, -1], d = 1e8  =>  [0, -1], sum = -1
    d = 100_000_000
    xs = [1, -1]
    assert sum(xs) == 0
    qs = [x // d for x in xs]
    assert qs == [0, -1]
    assert sum(qs) == -1


def test_largest_remainder_dust_allocator_restores_net_zero_conservation() -> None:
    d = 100_000_000
    xs = [1, -1]
    keys = ["alice", "bob"]
    adj = largest_remainder_adjust_net_zero(xs=xs, keys=keys, d=d)
    assert sum(adj) == 0
    # Each adjusted value is either floor(x/d) or floor(x/d)+1.
    floors = [x // d for x in xs]
    for a, f in zip(adj, floors, strict=True):
        assert a in (f, f + 1)


def test_largest_remainder_ties_break_by_key() -> None:
    adj = largest_remainder_adjust_net_zero(
        xs=[1, 1, -2],
        keys=["bob", "alice", "carol"],
        d=3,
    )

    assert adj == [0, 1, -1]
    assert sum(adj) == 0


def test_largest_remainder_rejects_bool_amount_before_net_zero_check() -> None:
    with pytest.raises(TypeError, match=r"xs\[0\] must be an int"):
        largest_remainder_adjust_net_zero(xs=[True, -1], keys=["alice", "bob"], d=3)


def test_largest_remainder_rejects_nonzero_sum_after_shape_checks() -> None:
    with pytest.raises(ValueError, match=r"sum\(xs\) must be 0"):
        largest_remainder_adjust_net_zero(xs=[1, 1], keys=["alice", "bob"], d=3)


def test_euclid_divisor_rejects_bool() -> None:
    with pytest.raises(TypeError, match="d must be an int"):
        euclid_div_rem(1, True)


def test_breaker_quantization_can_stall_witness() -> None:
    # Mirrors the minimal clamp-quantization witness recorded in:
    # internal/popperpad_mcp/bootstrap_zenodex_pad.py
    #
    # Quantization-safe clamp (ceil-div) avoids the zero-width-band stall:
    # when `P*m_bps/10000` is smaller than one price tick, we still allow a
    # single-tick move.
    def clamp_step(p: int, p_raw: int, m_bps: int) -> tuple[int, bool, int]:
        delta = ((p * m_bps) + 9_999) // 10_000
        lo = p - delta
        hi = p + delta
        if p_raw > hi:
            return hi, True, delta
        if p_raw < lo:
            return lo, True, delta
        return p_raw, False, delta

    p0 = 1
    p_raw = 2
    m_bps = 1
    p1, violated, delta = clamp_step(p0, p_raw, m_bps)
    assert delta == 1
    assert violated is False
    assert p1 == 2
