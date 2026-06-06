"""Python/Rust liquidity-kernel conformance (differential).

Drives ``src/core/liquidity.py`` (authority) and the Rust
``replay-liquidity-trace`` shadow over a shared corpus - randomized sequences,
rounding edges, domain boundaries, and reject-precedence pairs - asserting
identical accept/reject, identical stable reject codes, and identical numeric
outputs (receipt hashes + state roots).

Skipped (not failed) when neither a prebuilt binary nor ``cargo`` is available.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "liquidity_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import liquidity_kernel_lib as L  # noqa: E402
from src.state.pools import compute_pool_id  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

A0, A1 = "AAA", "BBB"
MAX_AMOUNT = L.DEX_LP_AMOUNT_MAX
MAX_RESERVE = L.DEX_POOL_RESERVE_MAX
MAX_SUPPLY = L.DEX_LP_SUPPLY_MAX
U128_MAX = L.U128_MAX


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {"version": 1, "kernel": "liquidity", "steps": [{"tx": tx} for tx in txs]}
    trace_path = tmp_path / "lq_diff.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def _assert_parity(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    """Run both sides over ``txs``; assert byte-identical documents."""
    python_out = L.replay_txs([json.loads(json.dumps(tx)) for tx in txs])
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)
    if python_out != rust_out:
        for i, (p, r) in enumerate(
            zip(python_out["results"], rust_out["results"], strict=False)
        ):
            if p != r:
                raise AssertionError(
                    f"differential mismatch at step {i}:\n"
                    f"  tx     = {json.dumps(txs[i])}\n"
                    f"  python = {json.dumps(p)}\n"
                    f"  rust   = {json.dumps(r)}"
                )
        assert python_out["final_state_root"] == rust_out["final_state_root"]
        assert len(python_out["results"]) == len(rust_out["results"])
        raise AssertionError("documents differ but per-step results matched")
    return rust_out


def _run_liquidity_op(rust_bin: Path, pool: dict, tx: dict, tmp_path: Path, name: str) -> dict:
    request = {"version": 1, "pool": pool, "tx": tx}
    req_path = tmp_path / f"{name}.json"
    req_path.write_text(json.dumps(request), encoding="utf-8")

    import subprocess

    proc = subprocess.run(
        [str(rust_bin), "liquidity-op", str(req_path)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    return json.loads(proc.stdout)


# --- helpers to build txs -----------------------------------------------------


def _create(amount0=1_000_000, amount1=1_000_000, fee_bps=30, created_at=0,
            curve_tag="CPMM", curve_params="", asset0=A0, asset1=A1):
    return {
        "kind": "create_pool",
        "asset0": asset0,
        "asset1": asset1,
        "amount0": amount0,
        "amount1": amount1,
        "fee_bps": fee_bps,
        "created_at": created_at,
        "curve_tag": curve_tag,
        "curve_params": curve_params,
    }


def _add(d0, d1, m0=0, m1=0):
    return {
        "kind": "add_liquidity",
        "amount0_desired": d0,
        "amount1_desired": d1,
        "amount0_min": m0,
        "amount1_min": m1,
    }


def _remove(lp, m0=0, m1=0):
    return {"kind": "remove_liquidity", "lp_amount": lp, "amount0_min": m0, "amount1_min": m1}


def _pool_id(asset0=A0, asset1=A1, fee_bps=30):
    return compute_pool_id(asset0, asset1, fee_bps)


# --- tests --------------------------------------------------------------------


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def test_initial_mint_boundary(rust_bin, tmp_path):
    # isqrt boundary: a0*a1 around MIN_LP_LOCK^2 = 1_000_000.
    txs = [
        _create(amount0=1_000_000, amount1=1),   # isqrt 1000 -> reject (<= lock)
        _create(amount0=1_000_001, amount1=1),   # isqrt 1000 -> reject
        _create(amount0=1_002_001, amount1=1),   # isqrt 1001 -> mint 1 (accept; threads)
        _create(amount0=1_004_004, amount1=1),   # isqrt 1002 (re-create replaces pool)
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert [r["accept"] for r in out["results"]] == [False, False, True, True]


def test_perfect_square_vs_nonsquare_floor(rust_bin, tmp_path):
    # Exercises isqrt floor: products that are / are not perfect squares.
    # These are too small to mint (isqrt <= 1000) so all reject identically -
    # the point is the isqrt VALUE agreeing, surfaced via the same code.
    txs = [
        _create(amount0=2, amount1=2),       # n=4, r=2
        _create(amount0=2, amount1=3),       # n=6, r=2
        _create(amount0=1_050_625, amount1=1),  # n=1_050_625 = 1025^2 -> isqrt 1025 -> mint 25
        _create(amount0=1_050_624, amount1=1),  # n just below -> isqrt 1024 -> mint 24
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert [r["accept"] for r in out["results"]] == [False, False, True, True]


def test_optimal_liquidity_tie_branch(rust_bin, tmp_path):
    # Tie d0*r1 == d1*r0 takes branch-1 (use d0 fully); +1 flips to branch-2.
    # Pool 1:2 reserves. d0=100, d1=200 -> d0*r1 = 100*2e6, d1*r0 = 200*1e6 equal.
    txs = [
        _create(amount0=1_000_000, amount1=2_000_000),  # 1:2
        _add(100_000, 200_000),       # tie -> used=(100000, 200000)
        _add(100_000, 200_001),       # d1+1 -> branch flips, used0 floors
    ]
    _assert_parity(rust_bin, txs, tmp_path)


def test_degenerate_ratio_zero_used_rejects(rust_bin, tmp_path):
    # Extreme skew so one used amount floors to 0 -> mint_amountN reject (add),
    # contrasted with remove producing out=0 and accepting (min=0).
    txs = [
        _create(amount0=1_000_000, amount1=2),   # creates with skew? n=2e6 -> isqrt 1414 -> mint 414
        _add(1, 1),                              # degenerate used -> mint reject
        _remove(1, 0, 0),                        # out floors to 0, min 0 -> ACCEPT (asymmetry)
    ]
    _assert_parity(rust_bin, txs, tmp_path)


def test_reserve_domain_exceeded_proportional(rust_bin, tmp_path):
    txs = [
        _create(amount0=1_000_000_000, amount1=1_000_000_000),  # big balanced pool
        _add(1_000_000_000, 1_000_000_000),  # adds, may approach reserve cap
        _add(1_000_000_000, 1_000_000_000),  # pushes reserve0+used > 3e9 -> reject
    ]
    _assert_parity(rust_bin, txs, tmp_path)


def test_domain_boundaries(rust_bin, tmp_path):
    txs = [
        _create(amount0=MAX_AMOUNT, amount1=2),          # amount0 = 1e9 (max, accept-shape)
        _create(amount0=MAX_AMOUNT + 1, amount1=2),      # amount0 out of domain
        _create(amount0=1_002_001, amount1=1, fee_bps=L.BPS_MAX),     # fee max (accept)
        _create(amount0=1_002_001, amount1=1, fee_bps=L.BPS_MAX + 1), # fee out of domain
    ]
    _assert_parity(rust_bin, txs, tmp_path)


def test_add_min_max_is_1e9(rust_bin, tmp_path):
    # add's *_min max is 1e9, NOT 3e9 (the remove asymmetry).
    txs = [
        _create(),
        _add(100_000, 100_000, m0=MAX_AMOUNT, m1=0),       # min = 1e9 in-domain -> below-min
        _add(100_000, 100_000, m0=MAX_AMOUNT + 1, m1=0),   # min = 1e9+1 -> min out of domain
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][1]["reject_reason"] == "amount0_used_below_min"
    assert out["results"][2]["reject_reason"] == "amount0_min_out_of_domain"


def test_remove_min_max_is_3e9(rust_bin, tmp_path):
    # remove's *_min max is 3e9, NOT 1e9.
    txs = [
        _create(),
        _remove(500_000, m0=MAX_RESERVE, m1=0),       # min 3e9 in-domain -> below-min
        _remove(500_000, m0=MAX_RESERVE + 1, m1=0),   # min 3e9+1 -> min out of domain
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][1]["reject_reason"] == "amount0_out_below_min"
    assert out["results"][2]["reject_reason"] == "amount0_min_out_of_domain"


def test_burn_full_and_over_supply(rust_bin, tmp_path):
    txs = [
        _create(),                # supply 1_000_000
        _remove(1_000_001),       # > supply -> burn_exceeds_supply
        _remove(1_000_000),       # == supply -> full burn (accept)
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][1]["reject_reason"] == "burn_exceeds_supply"
    assert out["results"][2]["accept"] is True


def test_created_at_u128_domain_and_precedence(rust_bin, tmp_path):
    txs = [
        _create(amount0=1_002_001, amount1=1, created_at=0),             # min
        _create(amount0=1_002_001, amount1=1, created_at=10**30),        # huge, still u128
        _create(amount0=1_002_001, amount1=1, created_at=U128_MAX),      # Rust max
        _create(amount0=1_002_001, amount1=1, created_at=U128_MAX + 1),  # fail-closed
        _create(amount0=1_002_001, amount1=1, created_at=-1),            # negative
        _create(
            amount0=1_002_001,
            amount1=1,
            fee_bps=L.BPS_MAX + 1,
            created_at=-1,
            curve_tag="CUBIC_SUM_V1",
        ),  # fee_bps precedes created_at, which precedes curve
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][3]["reject_reason"] == "created_at_out_of_domain"
    assert out["results"][4]["reject_reason"] == "created_at_out_of_domain"
    assert out["results"][5]["reject_reason"] == "fee_bps_out_of_domain"


def test_exotic_curve_rejects(rust_bin, tmp_path):
    txs = [
        _create(amount0=1_002_001, amount1=1, curve_tag="CUBIC_SUM_V1"),
        _create(amount0=1_002_001, amount1=1, curve_tag="cpmm"),  # lowercase CPMM accepted
        _create(amount0=1_002_001, amount1=1, curve_tag="CPMM", curve_params="{}"),  # params reject
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][0]["reject_reason"] == "unsupported_curve_tag"


def test_reject_precedence_pairs(rust_bin, tmp_path):
    """Inputs that trip TWO conditions at once; the earlier code must win on both
    sides (a wrong order is a fork)."""
    cases = [
        # add: pool not active beats everything (uninitialized threaded pool).
        ([_add(0, 0, 0, 0)], "pool_not_active"),
        # create: assets-not-canonical beats amount domain.
        ([_create(asset0="BBB", asset1="AAA", amount0=0)], "assets_not_canonical"),
        # create: amount0 out-of-domain beats fee out-of-domain.
        ([_create(amount0=0, fee_bps=L.BPS_MAX + 1)], "amount0_out_of_domain"),
    ]
    for setup, expected in cases:
        out = _assert_parity(rust_bin, setup, tmp_path)
        assert out["results"][-1]["reject_reason"] == expected, (
            f"expected {expected!r}, got {out['results'][-1]['reject_reason']!r}"
        )


def _hex32(byte_pair: str) -> str:
    """0x + a 32-byte (64-hex-char) body built by repeating ``byte_pair``."""
    assert len(byte_pair) == 2
    return "0x" + byte_pair * 32


def test_uppercase_hex_pool_id_normalization(rust_bin, tmp_path):
    """HEADLINE FIX-1 case. Real 32-byte hex asset ids in UPPERCASE must be
    canonicalized (lowercased) before the pool_id is derived and before the
    canonical ids are stored. This is an ACCEPTING input (so it actually reaches
    `compute_pool_id` - reject paths never do), and it locks Rust pool_id /
    state_root == Python authority. A passthrough of the raw uppercase id would
    fork the pool_id and the state root."""
    a0_upper = _hex32("AB")  # 0xABAB...AB
    a1_upper = _hex32("CD")  # 0xCDCD...CD (raw order AB < CD holds)
    # amount0*amount1 = 1_002_001 -> isqrt 1001 -> mint 1 (accept).
    txs = [_create(amount0=1_002_001, amount1=1, asset0=a0_upper, asset1=a1_upper)]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][0]["accept"] is True, out["results"][0]

    # Cross-check against the Python AUTHORITY directly (src/core/liquidity.py):
    # the stored asset0 and the pool_id must be the LOWERCASED canonical form.
    from src.core.liquidity import create_pool  # noqa: PLC0415
    from src.state.pools import compute_pool_id  # noqa: PLC0415

    pool_id, ps, _lp = create_pool(a0_upper, a1_upper, 1_002_001, 1, 30, "pk")
    assert ps.asset0 == a0_upper.lower()
    assert ps.asset1 == a1_upper.lower()
    assert pool_id == compute_pool_id(_hex32("ab"), _hex32("cd"), 30)
    # The accepting Rust step's receipt threads this pool_id; its post_state_root
    # must equal Python's (already asserted byte-identical by _assert_parity).
    assert out["results"][0]["receipt_hash"] is not None


def test_same_canonical_case_only_pair_rejects(rust_bin, tmp_path):
    """A pair that differs ONLY in case canonicalizes to the SAME id, so the
    canonical-order gate (c0 >= c1) must reject `assets_not_canonical` on BOTH
    sides. Note the RAW order check (uppercase < lowercase in ASCII) PASSES, so
    this reject can only come from the post-canonicalization order gate - exactly
    the new normalize step. Reject -> no-op state root."""
    a0 = _hex32("AB")  # raw '0xABAB..'  (< '0xabab..' in ASCII)
    a1 = _hex32("ab")  # same decoded bytes, lowercase
    txs = [_create(amount0=1_002_001, amount1=1, asset0=a0, asset1=a1)]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][0]["accept"] is False
    assert out["results"][0]["reject_reason"] == "assets_not_canonical"
    # reject is a no-op.
    assert out["results"][0]["pre_state_root"] == out["results"][0]["post_state_root"]


def test_malformed_hex_asset_rejects(rust_bin, tmp_path):
    """Right-length-but-non-hex and wrong-length 0x bodies must reject
    `invalid_asset_hex` on both sides (the new stable code), NOT fall through to
    a symbolic-id accept. malformed-hex precedes the mint (compute_pool_id @72
    before compute_lp_mint @75), so even a tiny-mint input surfaces the hex
    reject first."""
    bad_chars = _hex32("GG")           # 64 chars, non-hex body
    a1 = _hex32("cd")
    # Wrong length: 0x + 4 hex chars (not 64).
    short = "0xABCD"
    cases = [
        ([_create(amount0=1, amount1=1, asset0=bad_chars, asset1=a1)], "invalid_asset_hex"),
        ([_create(amount0=1_002_001, amount1=1, asset0=short, asset1=a1)], "invalid_asset_hex"),
    ]
    for setup, expected in cases:
        out = _assert_parity(rust_bin, setup, tmp_path)
        assert out["results"][-1]["accept"] is False
        assert out["results"][-1]["reject_reason"] == expected, out["results"][-1]
        assert out["results"][-1]["pre_state_root"] == out["results"][-1]["post_state_root"]


def test_uppercase_prefix_and_whitespace_hex_accept(rust_bin, tmp_path):
    """Faithful-port edge: Python detects hex via `asset.strip().lower()` so a
    `0X` prefix and surrounding whitespace are canonicalized (accept with the
    lowercased `0x` id), NOT treated as a symbolic id. A naive byte-decoding
    reuse would fork here: accept on both sides but with different pool_ids."""
    a0 = " 0X" + "AB" * 32 + " "   # 0X prefix + whitespace
    a1 = _hex32("cd")
    txs = [_create(amount0=1_002_001, amount1=1, asset0=a0, asset1=a1)]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][0]["accept"] is True, out["results"][0]

    from src.core.liquidity import create_pool  # noqa: PLC0415
    from src.state.pools import compute_pool_id  # noqa: PLC0415

    pool_id, ps, _lp = create_pool(a0, a1, 1_002_001, 1, 30, "pk")
    assert ps.asset0 == _hex32("ab")
    assert pool_id == compute_pool_id(_hex32("ab"), _hex32("cd"), 30)


def test_hex_nibble_boundary_order(rust_bin, tmp_path):
    """Locks the string-order == byte-order claim across the `9 -> a` nibble
    boundary: `0x09..` < `0x0a..` in both ASCII string order and decoded-byte
    order, so the canonical pair accepts on both sides with identical pool_id."""
    lo = _hex32("09")
    hi = _hex32("0a")
    txs = [_create(amount0=1_002_001, amount1=1, asset0=lo, asset1=hi)]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][0]["accept"] is True, out["results"][0]
    # Reversed order (0x0a.. , 0x09..) must reject assets_not_canonical (raw
    # order already catches it, but parity must hold).
    txs_rev = [_create(amount0=1_002_001, amount1=1, asset0=hi, asset1=lo)]
    out_rev = _assert_parity(rust_bin, txs_rev, tmp_path)
    assert out_rev["results"][0]["accept"] is False
    assert out_rev["results"][0]["reject_reason"] == "assets_not_canonical"


def test_liquidity_op_rejects_malformed_active_pool_snapshots(rust_bin, tmp_path):
    """Explicit active snapshots are verifier inputs, so their pool header must
    be canonical before add/remove arithmetic. This is the permanent regression
    for the review finding where Rust accepted malformed active snapshots that
    Python PoolState rejected."""
    base = {
        "initialized": True,
        "pool_id": "0xabc",
        "asset0": A0,
        "asset1": A1,
        "reserve0": 1_000_000,
        "reserve1": 1_000_000,
        "fee_bps": 30,
        "lp_supply": 1_000_000,
        "created_at": 0,
    }
    cases = [
        ({**base, "fee_bps": L.BPS_MAX + 1}, _add(100_000, 100_000), "fee_bps_out_of_domain"),
        ({**base, "fee_bps": L.BPS_MAX + 1}, _remove(1, 0, 0), "fee_bps_out_of_domain"),
        ({**base, "asset0": "BBB", "asset1": "AAA"}, _add(100_000, 100_000), "assets_not_canonical"),
        (
            {**base, "asset0": _hex32("GG"), "asset1": _hex32("cd")},
            _remove(1, 0, 0),
            "invalid_asset_hex",
        ),
        (
            {**base, "asset0": _hex32("AB"), "asset1": _hex32("CD")},
            _add(100_000, 100_000),
            "assets_not_canonical",
        ),
        (
            {**base, "pool_id": "forged-pool-id"},
            _add(100_000, 100_000),
            "pool_id_mismatch",
        ),
    ]

    for i, (pool, tx, expected) in enumerate(cases):
        py = L.apply_tx(L.LiquidityState(**pool), tx)
        assert isinstance(py, L.LiquidityRejected)
        assert py.reason == expected

        ru = _run_liquidity_op(rust_bin, pool, tx, tmp_path, f"bad_pool_{i}")
        assert ru["accept"] is False
        assert ru["reject_reason"] == expected
        assert ru["pre_state_root"] == ru["post_state_root"]


def test_liquidity_op_inactive_pool_precedes_bad_snapshot_header(rust_bin, tmp_path):
    """Inactive pools still reject as pool_not_active. This preserves the
    default empty-pool behavior while active snapshots get the stronger header
    validation above."""
    pool = {
        "initialized": False,
        "pool_id": "0xabc",
        "asset0": "BBB",
        "asset1": "AAA",
        "reserve0": L.DEX_POOL_RESERVE_MAX + 1,
        "reserve1": 0,
        "fee_bps": L.BPS_MAX + 1,
        "lp_supply": 0,
        "created_at": 0,
    }
    tx = _add(0, 0, 0, 0)

    py = L.apply_tx(L.LiquidityState(**pool), tx)
    assert isinstance(py, L.LiquidityRejected)
    assert py.reason == "pool_not_active"

    ru = _run_liquidity_op(rust_bin, pool, tx, tmp_path, "inactive_bad_pool")
    assert ru["accept"] is False
    assert ru["reject_reason"] == "pool_not_active"


def test_empty_pool_and_min_precedence(rust_bin, tmp_path):
    # After full removal the pool has reserve0=0,reserve1=0,lp_supply=0 -> add
    # should hit empty_pool (reserves==0) before amount-desired checks.
    txs = [
        _create(),
        _remove(1_000_000),       # full burn -> reserves 0, supply 0
        _add(100_000, 100_000),   # empty_pool
    ]
    out = _assert_parity(rust_bin, txs, tmp_path)
    assert out["results"][2]["reject_reason"] == "empty_pool"


def _random_tx(rng: random.Random, created: bool) -> dict:
    roll = rng.random()
    if not created or roll < 0.20:
        return _create(
            amount0=rng.choice([1_002_001, 1_000_000, 2_000_000, 1_000_000_000, 0, MAX_AMOUNT + 1]),
            amount1=rng.choice([1, 2, 1_000_000, 2_000_000, 500_000_000]),
            fee_bps=rng.choice([0, 30, L.BPS_MAX, L.BPS_MAX + 1]),
            created_at=rng.choice([0, 5, 10**30, U128_MAX, U128_MAX + 1, -1]),
            curve_tag=rng.choice(["CPMM", "cpmm", "CUBIC_SUM_V1"]),
        )
    if roll < 0.60:
        return _add(
            rng.choice([1, 100, 100_000, 500_000, 1_000_000_000, 0, MAX_AMOUNT + 1]),
            rng.choice([1, 100, 100_000, 500_000, 1_000_000_000, 2]),
            rng.choice([0, 100, 500_000, MAX_AMOUNT, MAX_AMOUNT + 1]),
            rng.choice([0, 100]),
        )
    return _remove(
        rng.choice([1, 100, 500_000, 1_000_000, 5_000_000, 0, MAX_SUPPLY + 1]),
        rng.choice([0, 100, MAX_RESERVE, MAX_RESERVE + 1]),
        rng.choice([0, 100]),
    )


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260605)
    txs: list[dict] = []
    created = False
    for _ in range(500):
        tx = _random_tx(rng, created)
        if tx["kind"] == "create_pool":
            created = True
        txs.append(tx)

    out = _assert_parity(rust_bin, txs, tmp_path)
    accepts = sum(1 for r in out["results"] if r["accept"])
    rejects = len(out["results"]) - accepts
    # Non-vacuity: both branches exercised.
    assert accepts > 0, "no accepts in randomized corpus"
    assert rejects > 0, "no rejects in randomized corpus"


def test_lp_supply_zero_single_op(rust_bin, tmp_path):
    """Single-op (`liquidity-op`) differential for the lp_supply==0 isqrt branch
    of add_liquidity - reachable only with an explicit pool state, which the
    trace path (state from the empty default) cannot construct directly."""
    pool = {
        "initialized": True,
        "pool_id": _pool_id(),
        "asset0": A0,
        "asset1": A1,
        "reserve0": 2_500_000_000,
        "reserve1": 2_500_000_000,
        "fee_bps": 30,
        "lp_supply": 0,
        "created_at": 0,
    }
    tx = _add(1_000_000_000, 1_000_000_000, 0, 0)
    # Python authority directly.
    state = L.LiquidityState(**pool)
    py = L.apply_tx(state, tx)
    assert isinstance(py, L.LiquidityAccepted), "lp_supply==0 isqrt branch must accept"

    # Rust single-op.
    request = {"version": 1, "pool": pool, "tx": tx}
    req_path = tmp_path / "lq_op.json"
    req_path.write_text(json.dumps(request), encoding="utf-8")
    import subprocess

    proc = subprocess.run(
        [str(rust_bin), "liquidity-op", str(req_path)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    ru = json.loads(proc.stdout)
    assert ru["accept"] is True
    # Reserves skip the >3e9 cap on the isqrt branch -> 3.5e9 reserve, parity.
    assert ru["post_pool"]["reserve0"] == "3500000000"
    assert ru["receipt"]["lp_delta"] == str(py.receipt.lp_delta)
    assert ru["receipt_hash"] == L.receipt_hash(py.receipt)


def test_lp_supply_zero_insufficient_initial_from_add(rust_bin, tmp_path):
    """The lp_supply==0 isqrt path is reachable from add (advisor point A). When
    the used amounts are too small (`sqrt(used0*used1) <= MIN_LP_LOCK`) it rejects
    with `insufficient_initial_liquidity` - the SAME code as the create path -
    NOT `lp_non_positive`. Drives the single-op path (explicit pool state)."""
    pool = {
        "initialized": True,
        "pool_id": _pool_id(),
        "asset0": A0,
        "asset1": A1,
        "reserve0": 1,
        "reserve1": 1,
        "fee_bps": 30,
        "lp_supply": 0,
        "created_at": 0,
    }
    tx = _add(1, 1, 0, 0)  # used == (1, 1) -> isqrt(1) = 1 <= MIN_LP_LOCK
    state = L.LiquidityState(**pool)
    py = L.apply_tx(state, tx)
    assert isinstance(py, L.LiquidityRejected)
    assert py.reason == "insufficient_initial_liquidity"

    request = {"version": 1, "pool": pool, "tx": tx}
    req_path = tmp_path / "lq_op_insuf.json"
    req_path.write_text(json.dumps(request), encoding="utf-8")
    import subprocess

    proc = subprocess.run(
        [str(rust_bin), "liquidity-op", str(req_path)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    ru = json.loads(proc.stdout)
    assert ru["accept"] is False
    assert ru["reject_reason"] == "insufficient_initial_liquidity"
    assert ru["pre_state_root"] == ru["post_state_root"]  # reject is no-op


def test_liquidity_op_rejects_unrepresentable_pool_created_at(rust_bin, tmp_path):
    """Explicit pool snapshots are Rust consensus state, so every scalar must be
    representable without saturation. This catches the parser boundary that the
    threaded trace path cannot reach."""
    pool = {
        "initialized": True,
        "pool_id": "0xabc",
        "asset0": A0,
        "asset1": A1,
        "reserve0": 1_000_000,
        "reserve1": 1_000_000,
        "fee_bps": 30,
        "lp_supply": 1_000_000,
        "created_at": U128_MAX + 1,
    }
    request = {"version": 1, "pool": pool, "tx": _add(1, 1, 0, 0)}
    req_path = tmp_path / "lq_bad_pool.json"
    req_path.write_text(json.dumps(request), encoding="utf-8")

    import subprocess

    proc = subprocess.run(
        [str(rust_bin), "liquidity-op", str(req_path)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 2
    assert "pool.created_at out_of_domain" in proc.stderr
