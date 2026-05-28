"""Phase 6 acceptance: Python/Rust burn-rail conformance (differential).

The Rust shadow (``zenodex-runtime-core::burn_receipts``) must agree with the
authoritative ``burn_receipts.py`` rails on every input. The randomized corpus
includes out-of-range and out-of-`i64` values to exercise the saturation path.
Skipped when no Rust toolchain/binary is available.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "burn_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import burn_receipts_lib  # noqa: E402
from rust_shadow_replay import (  # noqa: E402
    ShadowError,
    diff_trace_against_rust,
    locate_or_build_cli,
    run_rust_replay,
)

_FIELDS = burn_receipts_lib._FIELDS


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _run_rust_on_txs(rust_bin: Path, txs: list, tmp_path: Path) -> dict:
    trace = {"version": 1, "kernel": "burn_receipts", "steps": [{"tx": tx} for tx in txs]}
    trace_path = tmp_path / "burn_diff.json"
    trace_path.write_text(json.dumps(trace), encoding="utf-8")
    return run_rust_replay(rust_bin, trace_path)


def test_rust_matches_recorded_smoke_trace(rust_bin):
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    rust = run_rust_replay(rust_bin, TRACE)
    diffs = diff_trace_against_rust(trace, rust)
    assert diffs == [], "\n\n".join(diffs)


def _field_value(rng: random.Random):
    return rng.choice([0, 1, 2, rng.randint(0, 0x9000), -1, 0x8000, 0xFFFF, 1 << 40])


def _random_tx(rng: random.Random) -> dict:
    # Build mostly-well-formed burns/no-burns, then jitter individual fields.
    amount = rng.randint(0, 300)
    base = (
        burn_receipts_lib._burn(amount, supply=rng.randint(0, 0xFFFF), batch=rng.randint(0, 0x7000))
        if rng.random() < 0.5
        else burn_receipts_lib._no_burn(supply=rng.randint(0, 0xFFFF))
    )
    for key in _FIELDS:
        if rng.random() < 0.25:
            base[key] = _field_value(rng)
    if rng.random() < 0.05:
        del base[rng.choice(_FIELDS)]  # missing field -> bad_numeric_field
    return base


def test_randomized_differential(rust_bin, tmp_path):
    rng = random.Random(20260528)
    txs = [_random_tx(rng) for _ in range(600)]

    python_out = burn_receipts_lib.replay_txs([json.loads(json.dumps(tx)) for tx in txs])
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
        raise AssertionError("documents differ but per-step results matched")

    accepts = sum(1 for r in rust_out["results"] if r["accept"])
    reasons = {r["reject_reason"] for r in rust_out["results"] if not r["accept"]}
    assert accepts > 0
    assert {"replay_guard_failed", "amount_guard_failed"} <= reasons
