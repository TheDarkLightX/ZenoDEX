from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_source_diversity_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_source_diversity_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 16
    assert receipt["rejected_case_count"] == 16
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "source_set_hash_forgery_survives" in names
    assert "duplicate_source_id_survives" in names
    assert "too_few_sources_survives" in names
    assert "operator_correlation_survives" in names
    assert "venue_correlation_survives" in names
    assert "data_family_correlation_survives" in names
    assert "transport_correlation_survives" in names
    assert "jurisdiction_correlation_survives" in names
    assert "hidden_top_level_override_survives" in names
    assert "hidden_source_weight_survives" in names
    assert "wrong_schema_survives" in names
    assert "boolean_min_sources_survives" in names
    assert "zero_max_same_operator_survives" in names
    assert "bad_operator_token_survives" in names
    assert "sources_as_object_survives" in names
    assert "min_jurisdictions_unmet_survives" in names


def test_zenodex_oracle_source_diversity_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-source-diversity-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_source_diversity_chaos.py",
            "--output",
            str(output),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.source_diversity_chaos_replay.v1"
    assert receipt["ok"] is True
