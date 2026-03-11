from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "tools" / "permissionless_assurance.py"


def _run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def test_status_json_shape() -> None:
    proc = _run("status", "--format", "json")
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert isinstance(payload["branch"], str)
    assert isinstance(payload["lanes"], list)
    assert isinstance(payload["public_refs"], list)
    assert isinstance(payload["public_scope_paths"], list)


def test_stage_scope_includes_cli_when_modified() -> None:
    proc = _run("stage-scope", "--format", "json")
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert "tools/permissionless_assurance.py" in payload["paths"]


def test_leak_check_blocks_internal_markers() -> None:
    proc = _run("leak-check", "AGENTS.md", "internal/example.json", "--format", "json")
    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    blocked_paths = {finding["path"] for finding in payload["findings"]}
    assert "AGENTS.md" in blocked_paths
    assert "internal/example.json" in blocked_paths


def test_replay_plan_group_expansion() -> None:
    proc = _run("replay", "public", "--plan", "--format", "json")
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    lane_names = [lane["name"] for lane in payload["lanes"]]
    assert "kernel-assurance" in lane_names
    assert "spot-proof" in lane_names
    assert "spot-evidence" in lane_names
    assert "derivatives" in lane_names
