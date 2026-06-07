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


def test_doctor_json_shape() -> None:
    proc = _run("doctor", "--format", "json")
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert isinstance(payload["ok"], bool)
    assert isinstance(payload["actions"], list)
    assert isinstance(payload["blocker_count"], int)
    assert isinstance(payload["warning_count"], int)
    assert payload["action_count"] == len(payload["actions"])
    assert payload["summary"]["lanes_total"] >= payload["summary"]["lanes_ready"]
    for action in payload["actions"]:
        assert isinstance(action["id"], str)
        assert action["severity"] in {"blocker", "warning"}
        assert isinstance(action["commands"], list)
        assert isinstance(action["hints"], list)


def test_doctor_require_ok_fails_when_blockers_remain(monkeypatch) -> None:
    status = assurance_cli._status_payload()
    lane = dict(status["lanes"][0])
    lane["missing_environment"] = ["external/ESSO"]
    lane["environment_hints"] = {"external/ESSO": "clone or update external/ESSO"}
    lane["ready"] = False
    status["lanes"] = [lane]
    monkeypatch.setattr(assurance_cli, "_status_payload", lambda: status)

    args = type("Args", (), {"format": "json", "require_ok": True})()
    assert assurance_cli.cmd_doctor(args) == 1


def test_doctor_payload_reports_actionable_remediation() -> None:
    status = {
        "branch": "test",
        "assurance_snapshot": {
            "ok": False,
            "error": None,
            "stale_paths": ["README.md"],
        },
        "tla_claim_summary": {
            "ok": False,
            "error": None,
            "path": "docs/TLA_CLAIM_SUMMARY.md",
        },
        "dirty_count": 2,
        "public_scope_count": 1,
        "public_scope_leaks": [
            {"path": "internal/example.json", "kind": "path", "detail": "blocked"}
        ],
        "lanes_ready": 0,
        "lanes_total": 1,
        "lanes": [
            {
                "name": "kernel-assurance",
                "missing_files": ["tools/missing.py"],
                "missing_environment": ["external/ESSO"],
                "environment_hints": {"external/ESSO": "clone or update external/ESSO"},
            }
        ],
        "public_refs_ready": 0,
        "public_refs_total": 1,
        "public_refs": [
            {
                "path": "generated/example.py",
                "ready": False,
            }
        ],
    }

    payload = assurance_cli._doctor_payload(status)
    action_ids = {action["id"] for action in payload["actions"]}
    assert payload["ok"] is False
    assert "assurance_snapshot.stale" in action_ids
    assert "tla_claim_summary.stale" in action_ids
    assert "public_scope.leaks" in action_ids
    assert "worktree.dirty" in action_ids
    assert "lane.kernel-assurance.prerequisites" in action_ids
    assert "public_refs.not_ready" in action_ids
    lane_action = next(
        action for action in payload["actions"] if action["id"] == "lane.kernel-assurance.prerequisites"
    )
    assert "clone or update external/ESSO" in lane_action["hints"]


def test_stage_scope_includes_cli_when_modified(monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        assurance_cli,
        "_git_status_paths",
        lambda: ["tools/permissionless_assurance.py", "internal/private_note.md"],
    )

    args = type("Args", (), {"format": "json"})()
    assert assurance_cli.cmd_stage_scope(args) == 0
    payload = json.loads(capsys.readouterr().out)
    assert "tools/permissionless_assurance.py" in payload["paths"]
    assert "internal/private_note.md" not in payload["paths"]


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
