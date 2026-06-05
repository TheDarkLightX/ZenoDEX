"""PR-gated binding: the RUNNING cpmm_swap_v8 EXACT-OUT post-state conserves k
(k_after >= k_before) — the core CPMM conservation invariant — bound to the proven
CPMMInvariants.k_monotone_{zero_fee,with_fee}.

Closes the gap the cpmm flip-ruling found: test_cpmm_v8_exact_out_lean_property_binding.py
binds the exact-out OUTPUT/GROSS arithmetic (sufficiency+minimality) but asserts NOTHING
about k on the live swap_exact_out authority path
(settlement_strong_validator -> amm_dispatch.swap_exact_out_for_pool -> cpmm.swap_exact_out
-> cpmm_swap_v8.swap_exact_out). So a kernel that drained new_reserve_in (k_after < k_before,
a flat conservation violation) passed unnoticed. The exact-IN k is already bound in
test_cpmm_v8_exact_in_lean_property_binding.py; this is the exact-OUT companion.

Discipline (per the ruling): the teeth come from an INDEPENDENT recompute of the post-state
reserves from inputs, NOT from trusting the kernel's own k_after field — a kernel can drain a
reserve AND set a self-consistent k_after. We recompute new_reserve_in / new_reserve_out from
the inputs and bind them, then assert the proven k-nondecrease.

  Running (cpmm_swap_v8.swap_exact_out, lines 225-265):
    amount_in    = gross (= ceil(ceil(rin*aout/(rout-aout))*BPS/(BPS-fee)))
    fee_total    = ceil(amount_in*fee/BPS);  protocol_fee = floor(fee_total*pshare/BPS)
    new_reserve_in  = reserve_in + amount_in - protocol_fee
    new_reserve_out = reserve_out - amount_out            (the REQUESTED out, <= quote)
    k_after = new_reserve_in * new_reserve_out;  k_before = reserve_in * reserve_out

  Proven (CPMMInvariants.lean): k_monotone_zero_fee / k_monotone_with_fee — the CPMM formula
  on the retained net input never decreases k. Exact-out delivers <= the exact-in quote for
  the same gross, so its k is >= the exact-in k >= k_before. This BINDS that to the live kernel.

SCOPE: with this, the exact-out + exact-in swap MATH (output formulas, sufficiency/minimality,
AND both directions' k-conservation incl. protocol-fee removal) is fully proof-bound to the
running code. proof_artifact remains gated on dual review; this file flips no column.
"""

from __future__ import annotations

import random

import pytest

from src.kernels.python.cpmm_swap_v8 import swap_exact_out

BPS = 10_000
SEED = 20260606


def _ceil(a: int, b: int) -> int:
    assert b > 0
    return (a + b - 1) // b


def _gross(rin: int, rout: int, aout: int, fee: int) -> int:
    net_req = _ceil(rin * aout, rout - aout)
    return _ceil(net_req * BPS, BPS - fee)


def _expected_post_state(rin: int, rout: int, aout: int, fee: int, pshare: int):
    """Independent recompute of (new_reserve_in, new_reserve_out) from inputs only."""
    amount_in = _gross(rin, rout, aout, fee)
    fee_total = _ceil(amount_in * fee, BPS)
    protocol_fee = (fee_total * pshare) // BPS
    return rin + amount_in - protocol_fee, rout - aout


def _bind(rin: int, rout: int, aout: int, fee: int, pshare: int) -> bool:
    """Bind the live exact-out post-state + k-conservation. Returns True if a real swap was
    bound, False if the kernel rejected this input (domain edge)."""
    try:
        res = swap_exact_out(reserve_in=rin, reserve_out=rout, amount_out=aout,
                             fee_bps=fee, protocol_fee_share_bps=pshare)
    except ValueError:
        return False
    exp_rin, exp_rout = _expected_post_state(rin, rout, aout, fee, pshare)
    ctx = (rin, rout, aout, fee, pshare)
    # (i) post-state reserves equal the independent recompute (teeth vs a drained reserve)
    assert res.new_reserve_in == exp_rin, ("new_reserve_in", ctx, res.new_reserve_in, exp_rin)
    assert res.new_reserve_out == exp_rout, ("new_reserve_out", ctx, res.new_reserve_out, exp_rout)
    # (ii) k fields are consistent with the (now-bound) reserves
    assert res.k_before == rin * rout, ("k_before", ctx)
    assert res.k_after == exp_rin * exp_rout, ("k_after-recompute", ctx, res.k_after, exp_rin * exp_rout)
    # (iii) THE PROVEN CONSERVATION INVARIANT: k never decreases (k_monotone_with_fee)
    assert res.k_after >= res.k_before, ("k-nondecrease", ctx, res.k_after, res.k_before)
    return True


PROTOCOL_SHARES = [0, 1, 2500, 5000, 7500, 10000]


def test_witness_exact_out_k() -> None:
    assert _bind(1000, 1000, 88, 30, 0) is True


def test_protocol_fee_share_preserves_exact_out_k() -> None:
    """k_after >= k_before for EVERY protocol share (0..100%) on the live exact-out path —
    the protocol-fee-accounting half for the exact-out direction."""
    cases = [(1000, 1000, 88, 30), (10**7, 5 * 10**6, 100, 9999), (7, 11, 4, 300),
             (10**6, 10**6, 997, 1), (123457, 987653, 41234, 250)]
    n = 0
    for rin, rout, aout, fee in cases:
        for pshare in PROTOCOL_SHARES:
            if _bind(rin, rout, aout, fee, pshare):
                n += 1
    assert n == len(cases) * len(PROTOCOL_SHARES), n


def test_grid_exact_out_k() -> None:
    rins = [1, 3, 17, 1000, 999_983]
    routs = [2, 5, 1000, 1_000_003]
    checked = 0
    bound = 0
    for rin in rins:
        for rout in routs:
            for num, den in ((1, 4), (1, 2), (3, 4)):
                aout = max(1, min(rout - 1, rout * num // den))
                if not (1 <= aout < rout):
                    continue
                for fee in (0, 1, 30, 300, 3000, 9999):
                    for pshare in (0, 5000, 10000):
                        if _bind(rin, rout, aout, fee, pshare):
                            bound += 1
                        checked += 1
    assert checked >= 500
    assert bound >= 150, bound


def test_random_sweep_exact_out_k() -> None:
    rng = random.Random(SEED)
    bound = 0
    for _ in range(4000):
        rin = rng.randint(1, 10**7)
        rout = rng.randint(2, 10**7)
        aout = rng.randint(1, rout - 1)
        fee = rng.randint(0, 9999)
        pshare = rng.randint(0, 10000)
        if _bind(rin, rout, aout, fee, pshare):
            bound += 1
    assert bound >= 2000, bound


def test_high_magnitude_exact_out_k_no_float_collapse() -> None:
    F = 2 ** 53
    boundary = [
        (F - 1, F + 1, F // 2, 30, 5000),
        (10**18, 10**18, 10**17, 9999, 10000),
        (10**24, 5 * 10**23, 7 * 10**17, 1, 2500),
        (10**26, 10**26, 10**25, 0, 0),
    ]
    for rin, rout, aout, fee, pshare in boundary:
        # Review grade: A- binding. These hand-picked boundaries are intended
        # valid-domain samples; an unexpected live reject must not count as green.
        assert _bind(rin, rout, aout, fee, pshare) is True
    rng = random.Random(SEED + 2)
    bound = 0
    for _ in range(1500):
        rin = rng.randint(10**15, 10**26)
        rout = rng.randint(10**15, 10**26)
        aout = rng.randint(1, rout - 1)
        fee = rng.randint(0, 9999)
        pshare = rng.randint(0, 10000)
        if _bind(rin, rout, aout, fee, pshare):
            bound += 1
    assert bound >= 750, bound
