"""Phase 6 acceptance: burn-rail golden-trace determinism + integrity."""

from __future__ import annotations

import copy
import json
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
import export_golden_trace  # noqa: E402


def test_committed_trace_replays_cleanly():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    summary = burn_receipts_lib.replay_trace(trace)
    assert summary["steps"] == len(trace["steps"])
    assert summary["accepted"] > 0 and summary["rejected"] > 0


def test_committed_trace_is_up_to_date():
    on_disk = TRACE.read_text(encoding="utf-8")
    fresh = export_golden_trace.serialize(burn_receipts_lib.build_smoke_trace())
    assert on_disk == fresh, (
        "burn_smoke.json is stale; regenerate with:\n"
        "  python3 tools/runtime/export_golden_trace.py --scenario burn_smoke "
        "--out tests/runtime/golden_traces/burn_smoke.json"
    )


def test_trace_exercises_every_rail():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    reasons = {s["expected_reject_reason"] for s in trace["steps"] if not s["expected_accept"]}
    for required in (
        "replay_guard_failed",
        "amount_guard_failed",
        "supply_guard_failed",
        "batch_sum_guard_failed",
        "bad_numeric_field",
    ):
        assert required in reasons, required
    # Stateless verifier: every post_state_root equals the initial root.
    root = trace["initial_state_root"]
    assert all(s["post_state_root"] == root for s in trace["steps"])
    assert trace["final_state_root"] == root


def test_replay_detects_tampered_receipt_hash():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if step["expected_accept"]:
            step["receipt_hash"] = "0x" + "00" * 32
            break
    with pytest.raises(burn_receipts_lib.ReplayMismatch):
        burn_receipts_lib.replay_trace(tampered)
