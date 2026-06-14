from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_split_routing_staircase_runtime_evidence import (
    SCHEMA,
    build_split_routing_staircase_runtime_evidence,
)


def test_staircase_runtime_evidence_builder_accepts_small_replay() -> None:
    report = build_split_routing_staircase_runtime_evidence(
        seed=20260612,
        samples_per_family=2,
        min_cases=10,
        min_staircase_selected_cases=1,
        min_output_improvement_cases=1,
    )

    assert report["schema"] == SCHEMA
    assert report["ok"] is True
    summary = report["summary"]
    assert summary["total_cases"] == 20
    assert summary["staircase_selected_cases"] >= 1
    assert summary["heuristic_fallback_cases"] >= 1
    assert summary["output_improvement_cases"] >= 1
    assert summary["output_regression_cases"] == 0
    assert summary["selected_staircase_mismatch_cases"] == 0
    assert summary["fallback_result_mismatch_cases"] == 0
    assert summary["selected_current_quote_calls"] < summary["selected_legacy_quote_calls"]


def test_staircase_runtime_evidence_cli_writes_json(tmp_path) -> None:
    output = tmp_path / "split-routing-staircase-evidence.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_split_routing_staircase_runtime_evidence.py",
            "--samples-per-family",
            "1",
            "--min-cases",
            "10",
            "--console-summary-only",
            "--output-json",
            str(output),
        ],
        check=True,
        cwd=".",
        text=True,
        capture_output=True,
    )

    console_payload = json.loads(proc.stdout)
    file_payload = json.loads(output.read_text(encoding="utf-8"))
    assert console_payload["schema"] == SCHEMA
    assert "cases" not in console_payload
    assert file_payload["schema"] == SCHEMA
    assert "cases" in file_payload
    assert file_payload["ok"] is True
    assert file_payload["summary"]["output_regression_cases"] == 0


def test_spot_evidence_runner_replays_staircase_evidence() -> None:
    text = Path("tools/run_spot_evidence.sh").read_text(encoding="utf-8")
    assert "check_split_routing_staircase_runtime_evidence.py" in text
    assert "tests/core/test_split_routing.py" in text
    assert "tests/core/test_split_routing_staircase.py" in text
    assert "tests/core/test_split_routing_dispatch.py" in text
