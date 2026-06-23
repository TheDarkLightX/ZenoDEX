"""Phase 3 acceptance: Python/Rust fee-router conformance (differential tests).

These assert the Rust shadow (``rust-runtime``) routes identical inputs to
identical receipts and state roots as the authoritative Python runtime. The
suite is skipped (not failed) when neither a prebuilt binary nor ``cargo`` is
available, so the pure-Python test run stays green in minimal environments.
"""

from __future__ import annotations

import json
import random
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
SMOKE = REPO / "tests" / "runtime" / "golden_traces" / "smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from golden_trace_lib import replay_txs  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {
        "version": 1,
        "kernel": "fee_router",
        "steps": [{"tx": tx} for tx in txs],
    }
    trace_path = tmp_path / "diff_trace.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, SMOKE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def test_rust_matches_python_full_output_on_smoke(rust_bin, tmp_path):
    # Compare the *entire* Rust output document to Python's, field for field.
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    txs = [step["tx"] for step in trace["steps"]]
    python_out = replay_txs(txs)
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)
    assert python_out == rust_out


def _random_split(rng: random.Random) -> dict:
    roll = rng.random()
    if roll < 0.45:
        # canonical-ish valid table for a domain
        table = rng.choice(
            [
                {"buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": 2000},
                {"buyburn_bps": 0, "stakers_bps": 6000, "reserve_bps": 2000, "hosts_bps": 2000},
                {"buyburn_bps": 0, "stakers_bps": 6000, "reserve_bps": 4000, "hosts_bps": 0},
                {"buyburn_bps": 10000, "stakers_bps": 0, "reserve_bps": 0, "hosts_bps": 0},
                {"buyburn_bps": 0, "stakers_bps": 0, "reserve_bps": 5000, "hosts_bps": 5000},
            ]
        )
        return dict(table)
    if roll < 0.85:
        # arbitrary bps (often invalid: out of range or not summing)
        return {
            "buyburn_bps": rng.randint(-2, 10001),
            "stakers_bps": rng.randint(-2, 10001),
            "reserve_bps": rng.randint(-2, 10001),
            "hosts_bps": rng.randint(-2, 10001),
        }
    # structurally odd split tables
    bad = rng.choice(
        [
            {"buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000},  # missing field
            {"buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": 2000, "x": 1},
            {"buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": "2000"},
        ]
    )
    return dict(bad)


def _random_amount(rng: random.Random):
    return rng.choice(
        [
            0,
            1,
            rng.randint(2, 10_000),
            rng.randint(10_001, 10_000_000),
            (1 << 112) - 1,  # MAX_FEE_AMOUNT
            (1 << 112),  # MAX_FEE_AMOUNT + 1 -> amount_too_large
            (1 << 120),  # huge -> amount_too_large
            -1,  # negative_amount
            "100",  # non-int -> malformed_tx
        ]
    )


def _random_tx(rng: random.Random) -> dict:
    source = rng.choice(["dex", "perps", "borrow", "redemption", "lending", "DEX", ""])
    asset = rng.choice(["zUSD", "zDEX", "BTC", "wormhole-USDC"])
    tx = {
        "kind": "route_fee",
        "source": source,
        "asset": asset,
        "amount": _random_amount(rng),
        "split_table": _random_split(rng),
    }
    # Occasionally inject structural corruption at the tx level.
    roll = rng.random()
    if roll < 0.05:
        tx["kind"] = "transfer"
    elif roll < 0.10:
        tx["unexpected"] = "field"
    elif roll < 0.13:
        del tx["asset"]
    return tx


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260528)  # fixed seed -> reproducible
    txs = [_random_tx(rng) for _ in range(400)]

    python_out = replay_txs([json.loads(json.dumps(tx)) for tx in txs])
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)

    # Whole-document equality is the strongest statement of conformance.
    if python_out != rust_out:
        # Produce a precise first-divergence report to aid debugging.
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
        assert python_out["initial_state_root"] == rust_out["initial_state_root"]
        assert python_out["final_state_root"] == rust_out["final_state_root"]
        raise AssertionError("documents differ but per-step results matched")

    # Sanity: the corpus actually exercised both accepts and rejects.
    accepts = sum(1 for r in rust_out["results"] if r["accept"])
    assert 0 < accepts < len(txs)


def test_shadow_replay_cli_exit_zero(rust_bin):
    proc = subprocess.run(
        [sys.executable, str(TOOLS_RUNTIME / "rust_shadow_replay.py"), str(SMOKE)],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert "SHADOW OK" in proc.stdout


def _route(source: str, asset: str, amount: int, table: dict) -> dict:
    return {
        "kind": "route_fee",
        "source": source,
        "asset": asset,
        "amount": amount,
        "split_table": dict(table),
    }


_DEX_SPLIT = {"buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": 2000}
_REDEEM_SPLIT = {"buyburn_bps": 0, "stakers_bps": 6000, "reserve_bps": 4000, "hosts_bps": 0}


def test_preseeded_accumulator_and_boundary_dust(rust_bin, tmp_path):
    """Deterministic differential over a dust-CARRYING stream + boundary amounts.

    The randomized differential routes from a fresh accumulator; this pins the
    pre-seeded path the round-1 review flagged as untested: routing repeated
    small / boundary fees to the SAME ``(source, asset)`` stream accumulates
    per-bucket rounding remainders across steps, so each later route reads a
    NON-empty carried-dust state. A second stream is interleaved to exercise
    per-stream dust isolation, and the sequence crosses whole-dust quanta and the
    ``MAX_FEE_AMOUNT`` boundary on an already-seeded stream. Python and the Rust
    CLI must agree on the full document (receipts, dust, accumulator roots) at
    every step.
    """
    max_fee = (1 << 112) - 1
    txs: list[dict] = []
    # Build carried dust on (dex, zUSD): amount=1 leaves remainders
    # (6000,0,2000,2000); repeated routes carry and periodically emit whole dust.
    txs += [_route("dex", "zUSD", 1, _DEX_SPLIT) for _ in range(12)]
    # Interleave a second stream — must not consume the dex stream's dust.
    txs.append(_route("perps", "zUSD", 3, _DEX_SPLIT))
    # Boundary-ish remainder on the seeded dex stream, then a different domain,
    # then the MAX_FEE boundary on the seeded stream, then one more tiny route.
    txs.append(_route("dex", "zUSD", 3333, _DEX_SPLIT))
    txs.append(_route("redemption", "zUSD", 7, _REDEEM_SPLIT))
    txs.append(_route("dex", "zUSD", max_fee, _DEX_SPLIT))
    txs.append(_route("dex", "zUSD", 1, _DEX_SPLIT))

    python_out = replay_txs([json.loads(json.dumps(tx)) for tx in txs])
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)

    if python_out != rust_out:
        for i, (p, r) in enumerate(
            zip(python_out["results"], rust_out["results"], strict=False)
        ):
            assert p == r, (
                f"pre-seeded dust-carry stream diverged at step {i}:\n"
                f"  tx     = {json.dumps(txs[i])}\n"
                f"  python = {json.dumps(p)}\n"
                f"  rust   = {json.dumps(r)}"
            )
        assert python_out["final_state_root"] == rust_out["final_state_root"]
        raise AssertionError("documents differ but per-step results matched")

    # Every canonical in-domain route accepts, so the dust-carry path (not just
    # rejects) was actually exercised across the seeded stream.
    assert all(r["accept"] for r in rust_out["results"])
