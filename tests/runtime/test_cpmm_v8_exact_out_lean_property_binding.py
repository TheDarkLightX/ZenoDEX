"""PR-gated binding: the RUNNING cpmm_swap_v8 exact-out path satisfies the
Lean-PROVEN sufficiency + minimality theorem.

This converts the (previously only empirical) Lean<->Python formula fidelity into a
deterministic, PR-gated CI check that needs NO prover toolchain. `tests/runtime/**`
is globbed by runtime-shadow.yml and run via `pytest tests/runtime`, so a drift of
the live exact-out/exact-in math away from the proven formula fails CI here.

It binds the RUNNING code to the proven theorem two complementary ways, so the
check is not circular through the kernel's own swap_exact_in: (a) the live
swap_exact_out gross and swap_exact_in output EQUAL an independent transcription of
the Lean formula definitions, and (b) those proven formulas satisfy sufficiency +
minimality. Together: the live code computes the proven-safe formulas.

  Lean  lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean
        theorem swap_exact_out_sufficient_and_minimal  (rin>0, aout<rout, fee<10000):
          gross      = ceil( ceil(rin*aout/(rout-aout)) * BPS / (BPS-fee) )
          out_quote(g) = floor( rout*na / (rin+na) ),  na = g - ceil(g*fee/BPS)
          SUFFICIENT:  aout <= out_quote(gross)
          MINIMAL:     for all g < gross,  out_quote(g) < aout

  Running  swap_exact_out(...).gross_in  IS that `gross`, and
           swap_exact_in(..., amount_in=g, ...).amount_out  IS `out_quote(g)`
           (same ceil fee chain, same floor output; protocol_fee_share_bps=0).

So we assert the LIVE gross is SUFFICIENT (out_quote(gross) >= aout) and MINIMAL
(out_quote(gross-1) < aout; gross-1 is the tightest witness since out_quote is
monotone non-decreasing in g).

SCOPE (honest, matches the Lean docstring + the cpmm_swap proof_artifact note):
this binds the OUTPUT/GROSS arithmetic under protocol_fee_share_bps=0 — the model
the theorem covers. It does NOT cover protocol-fee-share pool ACCOUNTING, reject-code
precedence, or state-root binding, which remain the open residual keeping the
cpmm_swap proof_artifact column verified:false. This test is one increment of that
binding (formula -> running code), not the whole column.
"""

from __future__ import annotations

import random

import pytest

from src.kernels.python.cpmm_swap_v8 import swap_exact_in, swap_exact_out

BPS = 10_000
SEED = 20260604


# --- Independent transcription of the Lean definitions (closes circularity) -----
# These mirror lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean EXACTLY:
#   exactOutNetReq   = ceil(rin*aout / (rout-aout))           (line 31-32)
#   exactOutGross    = ceil(net_req*BPS / (BPS-fee))          (line 34-35)
#   exactOutNetActual= g - ceil(g*fee / BPS)                  (line 37-38)
#   exactOutQuote    = floor(rout*na / (rin+na))              (line 40-41)
# Pinning the LIVE kernel to these (below) means the property check is NOT
# circular through the kernel's own swap_exact_in: running == proven-formula, and
# the proven-formula satisfies sufficiency+minimality (the Lean theorem).


def _ceil(a: int, b: int) -> int:
    assert b > 0
    return (a + b - 1) // b


def _lean_gross(rin: int, rout: int, aout: int, fee: int) -> int:
    net_req = _ceil(rin * aout, rout - aout)
    return _ceil(net_req * BPS, BPS - fee)


def _lean_out_quote(rin: int, rout: int, g: int, fee: int) -> int:
    if g <= 0:
        return 0
    na = g - _ceil(g * fee, BPS)
    return (rout * na) // (rin + na)


def _out_quote(rin: int, rout: int, g: int, fee: int) -> int:
    """out_quote(g): the live exact-in output for gross input g (Lean's
    `exactOutQuote`). A ValueError (output 0 / trade too small / net<=0) means the
    floor formula yields 0, i.e. out_quote(g) == 0 — faithful to the Lean Nat
    semantics where the floor of a sub-unit quotient is 0."""
    if g <= 0:
        return 0
    try:
        return swap_exact_in(
            reserve_in=rin, reserve_out=rout, amount_in=g, fee_bps=fee,
            protocol_fee_share_bps=0,
        ).amount_out
    except ValueError:
        return 0


def _assert_sufficient_and_minimal(rin: int, rout: int, aout: int, fee: int) -> bool:
    """Assert the LIVE exact-out gross is sufficient + minimal vs the proven theorem.
    Returns True iff minimality was checked non-vacuously (gross-1 >= 1)."""
    res = swap_exact_out(
        reserve_in=rin, reserve_out=rout, amount_out=aout, fee_bps=fee,
        protocol_fee_share_bps=0,
    )
    gross = res.gross_in
    ctx = (rin, rout, aout, fee, gross)
    # (i) the LIVE gross equals the independently-transcribed Lean gross formula
    assert gross == _lean_gross(rin, rout, aout, fee), ("gross-formula", ctx)
    # (ii) the LIVE exact-in output equals the independently-transcribed Lean
    #      out_quote formula (so the property below is not circular through the
    #      kernel's own swap_exact_in)
    assert _out_quote(rin, rout, gross, fee) == _lean_out_quote(rin, rout, gross, fee), ("quote-formula", ctx)
    # the result's own quote must also equal the forward exact-in output
    assert res.amount_out_quote == _out_quote(rin, rout, gross, fee), ("quote-mismatch", ctx)
    # SUFFICIENCY: out_quote(gross) >= aout
    assert _out_quote(rin, rout, gross, fee) >= aout, ("sufficiency", ctx)
    # MINIMALITY: out_quote(gross-1) < aout  (tightest g < gross)
    if gross - 1 >= 1:
        assert _out_quote(rin, rout, gross - 1, fee) == _lean_out_quote(rin, rout, gross - 1, fee), ("quote-formula-min", ctx)
        assert _out_quote(rin, rout, gross - 1, fee) < aout, ("minimality", ctx)
        return True
    return False


def test_lean_witness_point_binds() -> None:
    # The Lean file's own witness: exactOutAccepts 10 10 1 0 with minimality.
    res = swap_exact_out(reserve_in=10, reserve_out=10, amount_out=1, fee_bps=0,
                         protocol_fee_share_bps=0)
    assert res.gross_in == 2  # exactOutGross 10 10 1 0 = 2 (matches Lean #eval)
    assert _assert_sufficient_and_minimal(10, 10, 1, 0) is True


BOUNDARY_CASES = [
    (1, 2, 1, 0),
    (1, 1_000_000, 1, 0),
    (1_000_000, 1_000_000, 1, 9999),
    (1_000_000, 1_000_000, 999_999, 0),
    (1_000_000, 1_000_000, 999_999, 9999),
    (7, 11, 5, 300),
    (10**7, 10**7, 5_000_000, 3000),
    (2, 10**7, 9_999_999, 1),
]


@pytest.mark.parametrize("rin,rout,aout,fee", BOUNDARY_CASES)
def test_boundary_cases_bind(rin: int, rout: int, aout: int, fee: int) -> None:
    _assert_sufficient_and_minimal(rin, rout, aout, fee)


def test_deterministic_grid_binds() -> None:
    rins = [1, 3, 17, 1000, 999_983]
    routs = [2, 5, 1000, 1_000_003]
    fees = [0, 1, 30, 300, 3000, 9999]
    nonvacuous = 0
    checked = 0
    for rin in rins:
        for rout in routs:
            # aout fractions of rout, strictly inside (0, rout)
            for num, den in ((1, 1), (1, 4), (1, 2), (3, 4), (None, None)):
                aout = rout - 1 if num is None else max(1, min(rout - 1, rout * num // den))
                if not (1 <= aout < rout):
                    continue
                for fee in fees:
                    if _assert_sufficient_and_minimal(rin, rout, aout, fee):
                        nonvacuous += 1
                    checked += 1
    assert checked >= 200, checked
    assert nonvacuous >= 100, nonvacuous  # minimality non-vacuously exercised


def test_random_sweep_binds() -> None:
    rng = random.Random(SEED)
    checked = 0
    nonvacuous = 0
    for _ in range(3000):
        rin = rng.randint(1, 10**7)
        rout = rng.randint(2, 10**7)
        aout = rng.randint(1, rout - 1)
        fee = rng.randint(0, 9999)
        if _assert_sufficient_and_minimal(rin, rout, aout, fee):
            nonvacuous += 1
        checked += 1
    assert checked == 3000
    assert nonvacuous >= 1500, nonvacuous  # most cases have gross>1 -> real minimality


def test_gross_is_independent_of_protocol_fee_share() -> None:
    """The proven model fixes protocol_fee_share_bps=0. The live gross_in (and the
    output quote) depend only on net_in/fee_bps, NOT on how the fee is split — so the
    share=0 proof covers the gross/output for ANY protocol share. (The protocol-fee
    pool ACCOUNTING that the share DOES affect is the separate, still-open residual.)"""
    cases = [(1000, 1000, 500, 300), (10**7, 5 * 10**6, 1_234_567, 30), (7, 11, 5, 9999)]
    shares = [0, 1, 2500, 5000, 10000]
    for rin, rout, aout, fee in cases:
        base = swap_exact_out(reserve_in=rin, reserve_out=rout, amount_out=aout,
                              fee_bps=fee, protocol_fee_share_bps=0)
        for share in shares:
            r = swap_exact_out(reserve_in=rin, reserve_out=rout, amount_out=aout,
                               fee_bps=fee, protocol_fee_share_bps=share)
            assert r.gross_in == base.gross_in, (rin, rout, aout, fee, share)
            assert r.amount_out_quote == base.amount_out_quote, (rin, rout, aout, fee, share)
