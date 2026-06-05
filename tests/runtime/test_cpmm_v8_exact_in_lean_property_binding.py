"""PR-gated binding: the RUNNING cpmm_swap_v8 exact-in path satisfies the Lean-PROVEN
output formula AND the k-nondecrease safety invariant — INCLUDING when a protocol fee
is removed from the pool (the protocol-fee-share-accounting residual).

Companion to test_cpmm_v8_exact_out_lean_property_binding.py. Same discipline: pin the
live kernel to an INDEPENDENT transcription of the Lean formula defs, then the proven
theorems give safety for free.

  Lean (lean-mathlib/Proofs):
    CPMMInvariants.k_monotone_zero_fee : for the CPMM formula out=floor(rout*net/(rin+net)),
        (rin+net)*(rout-out) >= rin*rout        -- k never decreases on the NET input
    CPMMInvariants.k_monotone_with_fee : same with the fee retained
    CpmmSwapV8ExactInAdmissibility      : admission predicate (output>0) is monotone in net

  Running (src/kernels/python/cpmm_swap_v8.py swap_exact_in):
    fee_total  = ceil(amount_in*fee/BPS);  net_in = amount_in - fee_total
    amount_out = floor(rout*net_in / (rin+net_in))
    protocol_fee = floor(fee_total*pshare/BPS);  lp_fee = fee_total - protocol_fee
    new_rin = rin + amount_in - protocol_fee  (= rin + net_in + lp_fee  >=  rin + net_in)
    k_after = new_rin*(rout-amount_out);  k_before = rin*rout

WHY k holds even when the protocol fee is EXTRACTED (pshare up to 100%): the pricing
denominator uses rin+net_in and net_in is always retained in the pool, so
new_rin >= rin+net_in; k_monotone_zero_fee gives (rin+net_in)*(rout-out) >= rin*rout,
hence k_after >= k_before for ANY protocol_fee_share. This test BINDS that to the live
kernel across a protocol-share sweep, closing the protocol-fee-accounting half of the
exact-in safety residual.

This is the exact-IN companion increment of the proof->running-code binding; like its
exact-out sibling it does NOT by itself clear cpmm_swap proof_artifact (reject
precedence, state-root binding, and the formal-spec cross-check remain). No column is
flipped by this file.
"""

from __future__ import annotations

import random

import pytest

from src.kernels.python.cpmm_swap_v8 import swap_exact_in

BPS = 10_000
SEED = 20260605


def _ceil(a: int, b: int) -> int:
    assert b > 0
    return (a + b - 1) // b


def _lean_net_in(amount_in: int, fee: int) -> int:
    return amount_in - _ceil(amount_in * fee, BPS)


def _lean_out(rin: int, rout: int, amount_in: int, fee: int) -> int:
    """Independent transcription of swap_exact_in's output. Returns None for the
    domain points where the kernel rejects (net<=0 / out<=0 / out>rout), matching the
    kernel raising ValueError there."""
    net = _lean_net_in(amount_in, fee)
    if net <= 0:
        return None
    out = (rout * net) // (rin + net)
    if out <= 0 or out > rout:
        return None
    return out


def _lean_k_after(rin: int, rout: int, amount_in: int, fee: int, pshare: int) -> int:
    net = _lean_net_in(amount_in, fee)
    out = (rout * net) // (rin + net)
    fee_total = _ceil(amount_in * fee, BPS)
    protocol_fee = (fee_total * pshare) // BPS
    new_rin = rin + amount_in - protocol_fee
    new_rout = rout - out
    return new_rin * new_rout


def _check(rin: int, rout: int, amount_in: int, fee: int, pshare: int) -> bool:
    """Bind the live exact-in result to the transcribed formula + the proven k-safety.
    Returns False if the kernel rejects (domain edge), True if a real swap was bound."""
    expected_out = _lean_out(rin, rout, amount_in, fee)
    try:
        res = swap_exact_in(reserve_in=rin, reserve_out=rout, amount_in=amount_in,
                            fee_bps=fee, protocol_fee_share_bps=pshare)
    except ValueError:
        # kernel rejected this input; the transcription must AGREE it is a non-swap
        assert expected_out is None, ("kernel-rejected-but-formula-accepts", rin, rout, amount_in, fee, pshare, expected_out)
        return False
    ctx = (rin, rout, amount_in, fee, pshare)
    # (i) output equals the independently-transcribed Lean formula
    assert expected_out is not None and res.amount_out == expected_out, ("out-formula", ctx, res.amount_out, expected_out)
    # (ii) the kernel's k_before/k_after fields equal an independent recomputation
    assert res.k_before == rin * rout, ("k_before", ctx)
    assert res.k_after == _lean_k_after(rin, rout, amount_in, fee, pshare), ("k_after-formula", ctx)
    # (iii) THE SAFETY PROPERTY (k_monotone): k never decreases, even with protocol fee removed
    assert res.k_after >= res.k_before, ("k-nondecrease", ctx, res.k_after, res.k_before)
    return True


PROTOCOL_SHARES = [0, 1, 2500, 5000, 7500, 10000]


def test_lean_witness_point_exact_in() -> None:
    assert _check(1000, 1000, 100, 30, 0) is True


def test_protocol_fee_share_preserves_k() -> None:
    """The protocol-fee-accounting residual: k_after >= k_before for EVERY protocol
    share (0..100%), bound on the live kernel."""
    # all chosen to be VALID swaps (net_in>0, out>0) for every protocol share, so the
    # k-preservation assertion in _check runs on a real swap for each (case, share).
    cases = [(1000, 1000, 100, 30), (10**7, 5 * 10**6, 123400, 9999), (7, 11, 5, 300),
             (10**6, 10**6, 999, 1), (123457, 987653, 54321, 250)]
    n = 0
    for rin, rout, amt, fee in cases:
        for pshare in PROTOCOL_SHARES:
            if _check(rin, rout, amt, fee, pshare):
                n += 1
    assert n == len(cases) * len(PROTOCOL_SHARES), n  # every case is a valid bound swap


def test_deterministic_grid_exact_in() -> None:
    rins = [1, 3, 17, 1000, 999_983]
    routs = [2, 5, 1000, 1_000_003]
    amts = [1, 2, 7, 100, 9973]
    fees = [0, 1, 30, 300, 3000, 9999]
    checked = 0
    bound = 0
    for rin in rins:
        for rout in routs:
            for amt in amts:
                for fee in fees:
                    for pshare in (0, 5000, 10000):
                        if _check(rin, rout, amt, fee, pshare):
                            bound += 1
                        checked += 1
    assert checked >= 1000
    assert bound >= 200, bound  # real swaps bound, not all domain-rejected


def test_random_sweep_exact_in() -> None:
    rng = random.Random(SEED)
    bound = 0
    for _ in range(4000):
        rin = rng.randint(1, 10**7)
        rout = rng.randint(2, 10**7)
        amt = rng.randint(1, 10**7)
        fee = rng.randint(0, 9999)
        pshare = rng.randint(0, 10000)
        if _check(rin, rout, amt, fee, pshare):
            bound += 1
    assert bound >= 2000, bound


def test_high_magnitude_exact_in_no_float_collapse() -> None:
    """18-26 decimal magnitudes, past the 2**53 float64 ceiling — a stray float()
    cast in the exact-in path or k computation would diverge here."""
    F = 2 ** 53
    boundary = [
        (F - 1, F + 1, F // 3, 30, 5000),
        (10**18, 10**18, 10**17, 9999, 10000),
        (10**24, 5 * 10**23, 7 * 10**17, 1, 2500),
        (10**26, 10**26, 10**25, 0, 0),
    ]
    for rin, rout, amt, fee, pshare in boundary:
        _check(rin, rout, amt, fee, pshare)
    rng = random.Random(SEED + 2)
    bound = 0
    for _ in range(1500):
        rin = rng.randint(10**15, 10**26)
        rout = rng.randint(10**15, 10**26)
        amt = rng.randint(10**12, 10**24)
        fee = rng.randint(0, 9999)
        pshare = rng.randint(0, 10000)
        if _check(rin, rout, amt, fee, pshare):
            bound += 1
    assert bound >= 750, bound
