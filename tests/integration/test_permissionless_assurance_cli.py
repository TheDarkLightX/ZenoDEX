from __future__ import annotations

import argparse
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
    assert kernel_lane["environment_hints"]["external/ESSO"] == (
        "clone/update the pinned ESSO checkout at external/ESSO"
    )
    spot_evidence_lane = next(lane for lane in payload["lanes"] if lane["name"] == "spot-evidence")
    assert spot_evidence_lane["required_environment"] == ["esso-toolchain"]
    assert spot_evidence_lane["environment_hints"]["esso-toolchain"] == (
        "clone/update external/ESSO or make the ESSO module importable"
    )
    assert isinstance(payload["public_refs"], list)
    assert isinstance(payload["public_scope_paths"], list)


def test_stage_scope_includes_cli_when_modified(monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        assurance_cli,
        "_git_status_paths",
        lambda: [
            "tools/permissionless_assurance.py",
            "tools/run_derivatives_evidence.sh",
            "tests/core/test_funding_rate_decomposed_parity.py",
            "internal/example.json",
        ],
    )

    rc = assurance_cli.cmd_stage_scope(argparse.Namespace(format="json"))

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert "tools/permissionless_assurance.py" in payload["paths"]
    assert "tools/run_derivatives_evidence.sh" in payload["paths"]
    assert "tests/core/test_funding_rate_decomposed_parity.py" in payload["paths"]
    assert "internal/example.json" not in payload["paths"]


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
    assert plan_lanes["spot-proof"]["required_environment"] == [
        "esso-toolchain",
        "lake",
        "external/mathlib4",
    ]
    assert plan_lanes["spot-evidence"]["required_environment"] == ["esso-toolchain"]
    assert plan_lanes["derivatives"]["required_environment"] == ["external/ESSO"]
    assert plan_lanes["perps"]["required_environment"] == [
        "esso-toolchain",
        "lake",
        "external/mathlib4",
    ]
    assert "tools/check_split_routing_staircase_runtime_evidence.py" in plan_lanes["spot-evidence"]["required_files"]
    assert "split-routing staircase evidence" in plan_lanes["spot-evidence"]["description"]
    assert "zusd" not in plan_lanes


def test_replay_missing_environment_fails_closed(monkeypatch) -> None:
    lane = assurance_cli.LANES["kernel-assurance"]
    monkeypatch.setattr(assurance_cli, "_environment_requirement_ready", lambda name: False)
    result = assurance_cli._run_lane(lane)
    assert result["ok"] is False
    assert result["error"] == "missing required environment"
    assert result["missing_environment"] == [
        {"name": "external/ESSO", "hint": "clone/update the pinned ESSO checkout at external/ESSO"}
    ]


def test_external_esso_requirement_requires_pinned_checkout(monkeypatch) -> None:
    monkeypatch.setattr(assurance_cli, "_python_module_importable", lambda name: name == "ESSO")
    monkeypatch.setattr(assurance_cli, "REPO_ROOT", Path("/tmp/zenodex-missing-pinned-esso-for-test"))
    assert assurance_cli._environment_requirement_ready("external/ESSO") is False


def test_esso_toolchain_requirement_accepts_importable_module(monkeypatch) -> None:
    monkeypatch.setattr(assurance_cli, "_python_module_importable", lambda name: name == "ESSO")
    assert assurance_cli._environment_requirement_ready("esso-toolchain") is True


def test_replay_json_suppresses_successful_lane_stdout(monkeypatch, capsys) -> None:
    lane = assurance_cli.Lane(
        name="fake-json-success",
        description="exercise JSON replay output purity",
        commands=((sys.executable, "-c", "print('lane noise')"),),
        required_files=(),
        required_environment=(),
        stars=0,
    )
    monkeypatch.setitem(assurance_cli.LANES, lane.name, lane)

    rc = assurance_cli.cmd_replay(
        argparse.Namespace(lanes=[lane.name], plan=False, keep_going=False, format="json")
    )

    captured = capsys.readouterr()
    assert rc == 0
    assert "lane noise" not in captured.out
    payload = json.loads(captured.out)
    assert payload["ok"] is True
    assert payload["results"][0]["name"] == lane.name
    assert "stdout_tail" not in payload["results"][0]


def test_replay_json_captures_failure_tails(monkeypatch, capsys) -> None:
    lane = assurance_cli.Lane(
        name="fake-json-failure",
        description="exercise JSON replay failure details",
        commands=(
            (
                sys.executable,
                "-c",
                "import sys; print('stdout detail'); print('stderr detail', file=sys.stderr); sys.exit(7)",
            ),
        ),
        required_files=(),
        required_environment=(),
        stars=0,
    )
    monkeypatch.setitem(assurance_cli.LANES, lane.name, lane)

    rc = assurance_cli.cmd_replay(
        argparse.Namespace(lanes=[lane.name], plan=False, keep_going=False, format="json")
    )

    payload = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert payload["ok"] is False
    result = payload["results"][0]
    assert result["error"] == "command failed"
    assert result["stdout_tail"].strip() == "stdout detail"
    assert result["stderr_tail"].strip() == "stderr detail"
