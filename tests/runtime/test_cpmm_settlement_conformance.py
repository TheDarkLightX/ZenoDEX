"""Phase 6 acceptance: Python/Rust CPMM-settlement conformance (differential)."""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "cpmm_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import cpmm_settlement_lib  # noqa: E402
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
    except ShadowError as exc:  # pragma: no cover
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust(rust_bin, txs, tmp_path):
    trace = {"version": 1, "kernel": "cpmm_settlement", "steps": [{"tx": t} for t in txs]}
    p = tmp_path / "cpmm_diff.json"
    p.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, p)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    assert diff_trace_against_rust(trace, rust) == []


def _amt(rng):
    return rng.choice([1, 100, rng.randint(1, 200_000), 0, -1, 3_000_000_000, 3_000_000_001, 1 << 40, "5"])


def _random_tx(rng):
    roll = rng.random()
    if roll < 0.15:
        return {
            "kind": "init_pool",
            "reserve0": _amt(rng),
            "reserve1": _amt(rng),
            "fee_bps": rng.choice([0, 30, 9999, 10000, -1, 10001]),
        }
    if roll < 0.2:
        return {"kind": "frobnicate"}
    zfo = rng.choice([True, False, "yes"])
    if rng.random() < 0.5:
        tx = {
            "kind": "swap_exact_in",
            "zero_for_one": zfo,
            "amount_in": _amt(rng),
            "min_amount_out": rng.choice([0, 1000, 1 << 40, -1]),
        }
    else:
        tx = {
            "kind": "swap_exact_out",
            "zero_for_one": zfo,
            "amount_out": _amt(rng),
            "max_amount_in": rng.choice([0, 10_000_000, 1 << 40, -1]),
        }
    if rng.random() < 0.05:
        tx["extra"] = 1
    return tx


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260529)
    txs = [{"kind": "init_pool", "reserve0": 1_000_000, "reserve1": 2_000_000, "fee_bps": 30}]
    txs += [_random_tx(rng) for _ in range(500)]

    python_out = cpmm_settlement_lib.replay_txs([json.loads(json.dumps(t)) for t in txs])
    rust_out = _run_rust(rust_bin, txs, tmp_path)

    if python_out != rust_out:
        for i, (p, r) in enumerate(zip(python_out["results"], rust_out["results"], strict=False)):
            if p != r:
                raise AssertionError(
                    f"mismatch at step {i}:\n  tx={json.dumps(txs[i])}\n  py={json.dumps(p)}\n  rs={json.dumps(r)}"
                )
        assert python_out["final_state_root"] == rust_out["final_state_root"]
        raise AssertionError("documents differ but per-step matched")

    accepts = sum(1 for r in rust_out["results"] if r["accept"])
    reasons = {r["reject_reason"] for r in rust_out["results"] if not r["accept"]}
    assert accepts > 0
    assert "slippage" in reasons or "invalid_amount" in reasons
    assert not any(r and r.startswith("unmapped:") for r in reasons)
