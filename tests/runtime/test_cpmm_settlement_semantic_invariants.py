"""Independent **semantic invariants** for the CPMM settlement surface.

These tests do NOT compare Python against Rust. They assert properties derived
from the *intended economics* of a constant-product swap, against the Python
authority (`apply_tx` over `quote_cpmm_swap_exact_in/out`) alone — the class of
defect a cross-language differential cannot see, because two implementations of
the same flawed model agree with each other.

This file closes the gap noted in review: the cherry-picked CPMM slice shipped
golden traces + the Rust differential, but not the per-surface semantic
invariants the checklist in docs/runtime/SEMANTIC_DRIFT_CONTROLS.md requires.

Invariants asserted:
  I1  constant product is non-decreasing across an accepted swap (the fee is a
      strict margin in favour of the pool);
  I2  reserves stay positive and within the domain after an accepted swap;
  I3  slippage admission — an accepted swap meets its bound, and a bound one
      unit tighter than the realized amount is rejected with ``slippage``;
  I4  a rejected tx is a no-op (identical reserves and state root);
  I5  the fee is non-negative and never exceeds the input.
"""

from __future__ import annotations

import random

import pytest

from src.kernels.python.settlement_swap_runtime_v1 import (
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from tools.runtime.cpmm_settlement_lib import Pool, REJ_SLIPPAGE, apply_tx


def _directed(pool: Pool, zfo: bool) -> tuple[int, int]:
    return (pool.reserve0, pool.reserve1) if zfo else (pool.reserve1, pool.reserve0)


def _k(pool: Pool) -> int:
    return pool.reserve0 * pool.reserve1


def _random_pool(rng: random.Random) -> Pool:
    r0 = rng.randint(1_000, 5_000_000)
    r1 = rng.randint(1_000, 5_000_000)
    fee = rng.choice([0, 1, 5, 30, 100, 300, 1000])
    return Pool(initialized=True, reserve0=r0, reserve1=r1, fee_bps=fee)


# --- I1 + I2 + I5: accepted swaps preserve k, stay in domain, bound the fee ----


@pytest.mark.parametrize("seed", [1, 2, 99, 20260529])
def test_accepted_exact_in_preserves_k_and_domain(seed):
    rng = random.Random(seed)
    accepted = 0
    for _ in range(800):
        pool = _random_pool(rng)
        zfo = rng.random() < 0.5
        amount_in = rng.randint(1, 2_000_000)
        ok, new_pool, reason, _ = apply_tx(
            pool,
            {
                "kind": "swap_exact_in",
                "zero_for_one": zfo,
                "amount_in": amount_in,
                "min_amount_out": 0,
            },
        )
        if not ok:
            continue
        accepted += 1
        # I1: constant product is non-decreasing.
        assert _k(new_pool) >= _k(pool), (
            f"k decreased: {_k(pool)} -> {_k(new_pool)} (pool={pool}, in={amount_in})"
        )
        # I2: reserves remain positive and within the domain.
        assert 1 <= new_pool.reserve0 <= DEX_POOL_RESERVE_MAX
        assert 1 <= new_pool.reserve1 <= DEX_POOL_RESERVE_MAX
        # I5: fee is non-negative and bounded by the input.
        reserve_in, reserve_out = _directed(pool, zfo)
        q = quote_cpmm_swap_exact_in(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=pool.fee_bps,
        )
        assert 0 <= q.fee_paid <= amount_in
        # Output never drains the out-side reserve.
        assert q.amount_out < reserve_out
    assert accepted > 50, f"too few accepted swaps to be meaningful ({accepted})"


@pytest.mark.parametrize("seed", [3, 4, 7])
def test_accepted_exact_out_preserves_k_and_domain(seed):
    rng = random.Random(seed)
    accepted = 0
    for _ in range(800):
        pool = _random_pool(rng)
        zfo = rng.random() < 0.5
        amount_out = rng.randint(1, 1_000_000)
        ok, new_pool, reason, _ = apply_tx(
            pool,
            {
                "kind": "swap_exact_out",
                "zero_for_one": zfo,
                "amount_out": amount_out,
                "max_amount_in": DEX_SWAP_AMOUNT_MAX,
            },
        )
        if not ok:
            continue
        accepted += 1
        assert _k(new_pool) >= _k(pool)
        assert 1 <= new_pool.reserve0 <= DEX_POOL_RESERVE_MAX
        assert 1 <= new_pool.reserve1 <= DEX_POOL_RESERVE_MAX
    assert accepted > 50, f"too few accepted swaps to be meaningful ({accepted})"


# --- I3: slippage admission --------------------------------------------------


def test_slippage_admission_exact_in():
    pool = Pool(initialized=True, reserve0=1_000_000, reserve1=2_000_000, fee_bps=30)
    q = quote_cpmm_swap_exact_in(
        reserve_in=pool.reserve0,
        reserve_out=pool.reserve1,
        amount_in=10_000,
        fee_bps=pool.fee_bps,
    )
    base = {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 10_000}
    # Exactly at the realized amount: accepted, and the realized output >= bound.
    ok, _, _, _ = apply_tx(pool, {**base, "min_amount_out": q.amount_out})
    assert ok
    # One unit tighter than realizable: rejected with the slippage code.
    ok, new_pool, reason, _ = apply_tx(pool, {**base, "min_amount_out": q.amount_out + 1})
    assert not ok and reason == REJ_SLIPPAGE
    # I4 corollary: the rejected attempt did not move the pool.
    assert (new_pool.reserve0, new_pool.reserve1) == (pool.reserve0, pool.reserve1)


def test_slippage_admission_exact_out():
    pool = Pool(initialized=True, reserve0=2_000_000, reserve1=1_000_000, fee_bps=30)
    q = quote_cpmm_swap_exact_out(
        reserve_in=pool.reserve0,
        reserve_out=pool.reserve1,
        amount_out=5_000,
        fee_bps=pool.fee_bps,
    )
    base = {"kind": "swap_exact_out", "zero_for_one": True, "amount_out": 5_000}
    ok, _, _, _ = apply_tx(pool, {**base, "max_amount_in": q.amount_in})
    assert ok
    ok, new_pool, reason, _ = apply_tx(pool, {**base, "max_amount_in": q.amount_in - 1})
    assert not ok and reason == REJ_SLIPPAGE
    assert (new_pool.reserve0, new_pool.reserve1) == (pool.reserve0, pool.reserve1)


# --- I4: rejects are no-ops --------------------------------------------------


def test_reject_is_noop():
    pool = Pool(initialized=True, reserve0=1_000_000, reserve1=1_000_000, fee_bps=30)
    pre_root = pool.state_root()
    rejecting_txs = [
        {"kind": "init_pool", "reserve0": 1, "reserve1": 1, "fee_bps": 0},  # already_initialized
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 0, "min_amount_out": 0},
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 100, "min_amount_out": 10**18},
        {"kind": "swap_exact_out", "zero_for_one": True, "amount_out": 10**18, "max_amount_in": 1},
        {"kind": "bogus_kind"},
        {"kind": "swap_exact_in", "zero_for_one": "yes", "amount_in": 1, "min_amount_out": 0},
    ]
    for tx in rejecting_txs:
        ok, new_pool, reason, rh = apply_tx(pool, tx)
        assert not ok and reason is not None and rh is None, tx
        assert (new_pool.reserve0, new_pool.reserve1, new_pool.fee_bps) == (
            pool.reserve0,
            pool.reserve1,
            pool.fee_bps,
        ), tx
        assert new_pool.state_root() == pre_root, tx


def test_pool_not_initialized_rejects_swaps():
    empty = Pool()
    for kind, extra in (
        ("swap_exact_in", {"amount_in": 1, "min_amount_out": 0}),
        ("swap_exact_out", {"amount_out": 1, "max_amount_in": 10**9}),
    ):
        ok, new_pool, reason, _ = apply_tx(
            empty, {"kind": kind, "zero_for_one": True, **extra}
        )
        assert not ok and reason == "pool_not_initialized"
        assert new_pool == empty
