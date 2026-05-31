from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools import permissionless_assurance as assurance_cli


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
    assert isinstance(payload["assurance_snapshot"], dict)
    assert payload["assurance_snapshot"]["ok"] is True
    assert payload["assurance_snapshot"]["as_of_date"] == "2026-04-06"
    assert isinstance(payload["tla_claim_summary"], dict)
    assert payload["tla_claim_summary"]["ok"] is True
    assert payload["tla_claim_summary"]["path"] == "docs/TLA_CLAIM_SUMMARY.md"
    assert isinstance(payload["lanes"], list)
    assert payload["notes"][-1].startswith("public replay lanes may require external toolchains")
    kernel_lane = next(lane for lane in payload["lanes"] if lane["name"] == "kernel-assurance")
    assert kernel_lane["required_environment"] == ["external/ESSO"]
    assert kernel_lane["environment_hints"]["external/ESSO"] == "clone or update external/ESSO"
    assert isinstance(payload["public_refs"], list)
    assert isinstance(payload["public_scope_paths"], list)


def test_stage_scope_includes_cli_when_modified() -> None:
    paths = assurance_cli._public_scope_paths(["tools/permissionless_assurance.py"])
    assert paths == ["tools/permissionless_assurance.py"]


def test_stage_scope_includes_claims_registry_when_modified() -> None:
    paths = assurance_cli._public_scope_paths(["docs/claims_registry.yaml"])
    assert paths == ["docs/claims_registry.yaml"]


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
    assert "perps" in lane_names
    plan_lanes = {lane["name"]: lane for lane in payload["lanes"]}
    assert plan_lanes["kernel-assurance"]["required_environment"] == ["external/ESSO"]
    assert "zusd" not in plan_lanes


def test_replay_missing_environment_fails_closed(monkeypatch) -> None:
    lane = assurance_cli.LANES["kernel-assurance"]
    monkeypatch.setattr(assurance_cli, "_environment_requirement_ready", lambda name: False)
    result = assurance_cli._run_lane(lane)
    assert result["ok"] is False
    assert result["error"] == "missing required environment"
    assert result["missing_environment"] == [
        {"name": "external/ESSO", "hint": "clone or update external/ESSO"}
    ]
