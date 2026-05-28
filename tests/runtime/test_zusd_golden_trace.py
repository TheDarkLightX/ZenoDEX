"""Phase 6 acceptance: zUSD golden-trace determinism + integrity."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
TRACE = REPO / "tests" / "runtime" / "golden_traces" / "zusd_smoke.json"

for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import export_golden_trace  # noqa: E402
import zusd_kernel_lib  # noqa: E402


def test_committed_trace_replays_cleanly():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    summary = zusd_kernel_lib.replay_trace(trace)
    assert summary["steps"] == len(trace["steps"])
    assert summary["accepted"] > 0 and summary["rejected"] > 0


def test_committed_trace_is_up_to_date():
    on_disk = TRACE.read_text(encoding="utf-8")
    fresh = export_golden_trace.serialize(zusd_kernel_lib.build_smoke_trace())
    assert on_disk == fresh, (
        "zusd_smoke.json is stale; regenerate with:\n"
        "  python3 tools/runtime/export_golden_trace.py --scenario zusd_smoke "
        "--out tests/runtime/golden_traces/zusd_smoke.json"
    )


def test_trace_exercises_required_paths():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    reasons = {s["expected_reject_reason"] for s in trace["steps"] if not s["expected_accept"]}
    for required in (
        "mint_blocked_oracle",
        "mint_violates_mcr",
        "mint_below_min_debt",
        "bootstrap_requires_auth",
        "oracle_already_bootstrapped",
        "not_positive_int",
        "unknown_action",
    ):
        assert required in reasons, required
    # No error string should be left unmapped.
    assert not any(r and r.startswith("unmapped:") for r in reasons)
    # The lifecycle must include accepted mint and redeem.
    tags = [s["tx"]["kind"] for s in trace["steps"] if s["expected_accept"]]
    assert "mint_zusd" in tags and "redeem_zusd" in tags


def test_replay_detects_tampered_state_root():
    trace = json.loads(TRACE.read_text(encoding="utf-8"))
    tampered = copy.deepcopy(trace)
    for step in tampered["steps"]:
        if step["expected_accept"]:
            step["post_state_root"] = "0x" + "00" * 32
            break
    with pytest.raises(zusd_kernel_lib.ReplayMismatch):
        zusd_kernel_lib.replay_trace(tampered)


def test_cli_roundtrip(tmp_path):
    out = tmp_path / "z.json"
    rc = subprocess.run(
        [
            sys.executable,
            str(TOOLS_RUNTIME / "export_golden_trace.py"),
            "--scenario",
            "zusd_smoke",
            "--out",
            str(out),
        ],
        cwd=str(REPO),
        capture_output=True,
        text=True,
    )
    assert rc.returncode == 0, rc.stderr
    assert out.read_text(encoding="utf-8") == TRACE.read_text(encoding="utf-8")
