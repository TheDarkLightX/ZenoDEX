"""Phase 6 acceptance: CPMM-settlement golden-trace determinism + integrity."""

from __future__ import annotations

import copy
import json
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
import export_golden_trace  # noqa: E402


def test_committed_trace_replays_cleanly():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    summary = cpmm_settlement_lib.replay_trace(trace)
    assert summary["steps"] == len(trace["steps"])
    assert summary["accepted"] > 0 and summary["rejected"] > 0


def test_committed_trace_is_up_to_date():
    on_disk = TRACE.read_text(encoding="utf-8")
    fresh = export_golden_trace.serialize(cpmm_settlement_lib.build_smoke_trace())
    assert on_disk == fresh, (
        "cpmm_smoke.json is stale; regenerate with:\n"
        "  python3 tools/runtime/export_golden_trace.py --scenario cpmm_smoke "
        "--out tests/runtime/golden_traces/cpmm_smoke.json"
    )


def test_trace_exercises_required_paths():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    reasons = {s["expected_reject_reason"] for s in trace["steps"] if not s["expected_accept"]}
    for required in (
        "pool_not_initialized",
        "already_initialized",
        "slippage",
        "invalid_amount",
        "reserve_domain_exceeded",
        "amount_out_ge_reserve",
        "unknown_tx_kind",
    ):
        assert required in reasons, required
    assert any(r and r.startswith("unknown_field:") for r in reasons)
    assert not any(r and r.startswith("unmapped:") for r in reasons)
    kinds = {s["tx"]["kind"] for s in trace["steps"] if s["expected_accept"]}
    assert {"swap_exact_in", "swap_exact_out"} <= kinds


def test_replay_detects_tampered_state_root():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if step["expected_accept"] and step["tx"]["kind"] != "init_pool":
            step["post_state_root"] = "0x" + "00" * 32
            break
    with pytest.raises(cpmm_settlement_lib.ReplayMismatch):
        cpmm_settlement_lib.replay_trace(tampered)
