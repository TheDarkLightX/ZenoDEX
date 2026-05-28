"""Phase 6 acceptance: replay-guard golden-trace determinism + integrity."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "replay_guard_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import export_golden_trace  # noqa: E402
import replay_guard_lib  # noqa: E402


def test_committed_trace_replays_cleanly():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    summary = replay_guard_lib.replay_trace(trace)
    assert summary["steps"] == len(trace["steps"])
    assert summary["accepted"] > 0 and summary["rejected"] > 0


def test_committed_trace_is_up_to_date():
    on_disk = TRACE.read_text(encoding="utf-8")
    fresh = export_golden_trace.serialize(replay_guard_lib.build_smoke_trace())
    assert on_disk == fresh, (
        "replay_guard_smoke.json is stale; regenerate with:\n"
        "  python3 tools/runtime/export_golden_trace.py --scenario replay_guard_smoke "
        "--out tests/runtime/golden_traces/replay_guard_smoke.json"
    )


def test_trace_exercises_required_paths():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    reasons = {s["expected_reject_reason"] for s in trace["steps"] if not s["expected_accept"]}
    for required in (
        "duplicate_nonce",
        "stale_nonce",
        "nonce_gap",
        "invalid_sender",
        "invalid_nonce",
        "unknown_tx_kind",
        "malformed_tx",
    ):
        assert required in reasons, required
    assert any(r and r.startswith("unknown_field:") for r in reasons)
    # Two distinct senders must appear among accepted steps (cross-sender case).
    accepted_senders = {s["tx"]["sender"] for s in trace["steps"] if s["expected_accept"]}
    assert len(accepted_senders) >= 2


def test_replay_detects_tampered_state_root():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if step["expected_accept"]:
            step["post_state_root"] = "0x" + "00" * 32
            break
    with pytest.raises(replay_guard_lib.ReplayMismatch):
        replay_guard_lib.replay_trace(tampered)


def test_replay_detects_tampered_reject_reason():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if not step["expected_accept"]:
            step["expected_reject_reason"] = "totally_wrong"
            break
    with pytest.raises(replay_guard_lib.ReplayMismatch):
        replay_guard_lib.replay_trace(tampered)


def test_cli_export_and_replay_roundtrip(tmp_path):
    out = tmp_path / "rg.json"
    rc = subprocess.run(
        [
            sys.executable,
            str(TOOLS_RUNTIME / "export_golden_trace.py"),
            "--scenario",
            "replay_guard_smoke",
            "--out",
            str(out),
        ],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert rc.returncode == 0, rc.stderr
    replay = subprocess.run(
        [sys.executable, str(TOOLS_RUNTIME / "replay_golden_trace.py"), str(out)],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert replay.returncode == 0, replay.stderr
    assert "replayed cleanly" in replay.stdout
    assert out.read_text(encoding="utf-8") == TRACE.read_text(encoding="utf-8")
