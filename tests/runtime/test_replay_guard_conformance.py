"""Phase 6 acceptance: Python/Rust replay-guard conformance (differential).

Asserts the Rust shadow admits/rejects identical (sender, nonce) inputs to
identical receipts and state roots as the Python authority. Skipped (not failed)
when neither a prebuilt binary nor ``cargo`` is available.

Per the lessons learned, this differential is paired with — never a substitute
for — the independent semantic invariants in
``test_replay_guard_semantic_invariants.py``.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "replay_guard_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import replay_guard_lib  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

VALID_SENDERS = ["0x" + f"{tag:02x}" * 48 for tag in (0x11, 0x22, 0x33)]


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {"version": 1, "kernel": "replay_guard", "steps": [{"tx": tx} for tx in txs]}
    trace_path = tmp_path / "rg_diff.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def _random_nonce(rng: random.Random):
    return rng.choice([1, 2, 3, 4, 5, 6, 0, -1, 1 << 40, "5", 1.5, True])


def _random_sender(rng: random.Random):
    return rng.choice(
        VALID_SENDERS + ["0xzz" + "11" * 47, "0x11", "", 12345, VALID_SENDERS[0].upper()]
    )


def _random_tx(rng: random.Random) -> dict:
    tx = {"kind": "admit", "sender": _random_sender(rng), "nonce": _random_nonce(rng)}
    roll = rng.random()
    if roll < 0.05:
        tx["kind"] = "transfer"
    elif roll < 0.10:
        tx["extra"] = 1
    elif roll < 0.13:
        del tx["nonce"]
    return tx


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260528)
    txs = [_random_tx(rng) for _ in range(400)]

    python_out = replay_guard_lib.replay_txs([json.loads(json.dumps(tx)) for tx in txs])
    rust_out = _run_rust_on_txs(rust_bin, txs, tmp_path)

    if python_out != rust_out:
        for i, (p, r) in enumerate(zip(python_out["results"], rust_out["results"], strict=False)):
            if p != r:
                raise AssertionError(
                    f"differential mismatch at step {i}:\n"
                    f"  tx     = {json.dumps(txs[i])}\n"
                    f"  python = {json.dumps(p)}\n"
                    f"  rust   = {json.dumps(r)}"
                )
        assert python_out["final_state_root"] == rust_out["final_state_root"]
        raise AssertionError("documents differ but per-step results matched")

    accepts = sum(1 for r in rust_out["results"] if r["accept"])
    assert 0 < accepts < len(txs)
