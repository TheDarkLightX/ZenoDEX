"""Phase 1 acceptance: golden-trace export / replay determinism + integrity."""

from __future__ import annotations

import copy
import json
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

import export_golden_trace  # noqa: E402
from golden_trace_lib import (  # noqa: E402
    ReplayMismatch,
    build_smoke_trace,
    replay_trace,
)


def test_committed_smoke_trace_replays_cleanly():
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    summary = replay_trace(trace)
    assert summary["steps"] == len(trace["steps"])
    assert summary["accepted"] > 0 and summary["rejected"] > 0


def test_committed_smoke_trace_is_up_to_date():
    # If the router semantics change, the committed corpus must be regenerated.
    on_disk = SMOKE.read_text(encoding="utf-8")
    fresh = export_golden_trace.serialize(build_smoke_trace())
    assert on_disk == fresh, (
        "tests/runtime/golden_traces/smoke.json is stale; regenerate with:\n"
        "  python3 tools/runtime/export_golden_trace.py "
        "--out tests/runtime/golden_traces/smoke.json"
    )


def test_replay_is_deterministic_across_two_runs():
    a = build_smoke_trace()
    b = build_smoke_trace()
    assert a == b
    assert replay_trace(a)["final_state_root"] == replay_trace(b)["final_state_root"]


def test_smoke_trace_exercises_required_paths():
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    reasons = {s["expected_reject_reason"] for s in trace["steps"] if not s["expected_accept"]}
    # In-scope fee-router disaster paths must all be present.
    assert "split_does_not_sum_to_10000" in reasons
    assert "split_component_out_of_range" in reasons
    assert "negative_amount" in reasons
    assert "amount_too_large" in reasons
    assert "unknown_domain" in reasons
    assert "unknown_field:memo" in reasons
    assert "unknown_tx_kind" in reasons
    assert any(r and r.startswith("domain_constraint_violated:") for r in reasons)
    # And all four fee domains must appear among accepted steps.
    accepted_sources = {
        s["tx"]["source"] for s in trace["steps"] if s["expected_accept"]
    }
    assert {"dex", "perps", "borrow", "redemption"} <= accepted_sources


def test_replay_detects_tampered_state_root():
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    # Corrupt the first accepted step's recorded post_state_root.
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if step["expected_accept"]:
            step["post_state_root"] = "0x" + "00" * 32
            break
    with pytest.raises(ReplayMismatch):
        replay_trace(tampered)


def test_replay_detects_tampered_reject_reason():
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if not step["expected_accept"]:
            step["expected_reject_reason"] = "totally_wrong_reason"
            break
    with pytest.raises(ReplayMismatch):
        replay_trace(tampered)


def test_replay_detects_tampered_final_root():
    trace = json.loads(SMOKE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    tampered["final_state_root"] = "0x" + "11" * 32
    with pytest.raises(ReplayMismatch):
        replay_trace(tampered)


def test_cli_export_and_replay_roundtrip(tmp_path):
    out = tmp_path / "smoke.json"
    export_rc = subprocess.run(
        [sys.executable, str(TOOLS_RUNTIME / "export_golden_trace.py"), "--out", str(out)],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert export_rc.returncode == 0, export_rc.stderr
    assert out.is_file()

    replay_rc = subprocess.run(
        [sys.executable, str(TOOLS_RUNTIME / "replay_golden_trace.py"), str(out)],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert replay_rc.returncode == 0, replay_rc.stderr
    assert "replayed cleanly" in replay_rc.stdout

    # CLI output must byte-match the committed corpus.
    assert out.read_text(encoding="utf-8") == SMOKE.read_text(encoding="utf-8")
