"""Independent **semantic invariants** for the CPMM settlement swap kernel.

Driven against the authoritative quote functions alone (not a Python/Rust diff):
the constant-product invariant (k never decreases), exact reserve conservation,
slippage admission, and no-op-on-reject. See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import cpmm_settlement_lib as c  # noqa: E402


def _k(pool) -> int:
    return pool.reserve0 * pool.reserve1


def _directed(pool, zfo):
    return (pool.reserve0, pool.reserve1) if zfo else (pool.reserve1, pool.reserve0)


def _init():
    ok, pool, code, _rh = c.apply_tx(
        c.Pool(), {"kind": "init_pool", "reserve0": 1_000_000, "reserve1": 1_000_000, "fee_bps": 30}
    )
    assert ok, code
    return pool


def test_constant_product_never_decreases_and_conserves_reserves():
    rng = random.Random(7)
    pool = _init()
    accepted = 0
    for _ in range(400):
        zfo = rng.choice([True, False])
        if rng.random() < 0.5:
            tx = {
                "kind": "swap_exact_in",
                "zero_for_one": zfo,
                "amount_in": rng.randint(1, 50_000),
                "min_amount_out": 0,
            }
        else:
            tx = {
                "kind": "swap_exact_out",
                "zero_for_one": zfo,
                "amount_out": rng.randint(1, 50_000),
                "max_amount_in": 10_000_000,
            }
        r_in_before, r_out_before = _directed(pool, zfo)
        k_before = _k(pool)
        ok, new_pool, code, _rh = c.apply_tx(pool, tx)
        if not ok:
            assert new_pool == pool  # rejection is a no-op
            continue
        accepted += 1
        # Constant-product invariant.
        assert _k(new_pool) >= k_before
        r_in_after, r_out_after = _directed(new_pool, zfo)
        if tx["kind"] == "swap_exact_in":
            # input side grows by exactly amount_in (protocol fee stays in pool here).
            assert r_in_after == r_in_before + tx["amount_in"]
            assert r_out_after < r_out_before  # some output left the pool
        else:
            # output side shrinks by exactly the requested amount_out.
            assert r_out_after == r_out_before - tx["amount_out"]
            assert r_in_after > r_in_before
        assert new_pool.reserve0 >= 1 and new_pool.reserve1 >= 1
        pool = new_pool
    assert accepted > 50


def test_slippage_is_respected_on_accept():
    pool = _init()
    # Exact-in: a satisfiable floor accepts; an impossible floor rejects.
    ok, _, _, _ = c.apply_tx(
        pool, {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 10_000, "min_amount_out": 1}
    )
    assert ok
    ok, _, code, _ = c.apply_tx(
        pool,
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 10_000, "min_amount_out": 10_000},
    )
    assert not ok and code == "slippage"
    # Exact-out: a generous cap accepts; a tiny cap rejects.
    ok, _, _, _ = c.apply_tx(
        pool,
        {"kind": "swap_exact_out", "zero_for_one": True, "amount_out": 5_000, "max_amount_in": 10_000_000},
    )
    assert ok
    ok, _, code, _ = c.apply_tx(
        pool, {"kind": "swap_exact_out", "zero_for_one": True, "amount_out": 5_000, "max_amount_in": 1}
    )
    assert not ok and code == "slippage"


def test_rejections_are_no_ops():
    pool = _init()
    root = pool.state_root()
    for tx in [
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 0, "min_amount_out": 0},
        {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 10_000, "min_amount_out": 10**12},
        {"kind": "init_pool", "reserve0": 1, "reserve1": 1, "fee_bps": 0},
        {"kind": "frobnicate"},
    ]:
        ok, new_pool, _, _ = c.apply_tx(pool, tx)
        assert not ok
        assert new_pool.state_root() == root
