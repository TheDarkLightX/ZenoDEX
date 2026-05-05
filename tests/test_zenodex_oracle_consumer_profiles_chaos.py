from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_consumer_profile_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_consumer_profiles_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 14
    assert receipt["rejected_case_count"] == 14
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "missing_required_profile_survives" in names
    assert "duplicate_profile_key_survives" in names
    assert "duplicate_profile_id_survives" in names
    assert "profile_hash_forgery_survives" in names
    assert "unsupported_profile_key_survives" in names
    assert "wrong_query_survives" in names
    assert "weak_evidence_floor_survives" in names
    assert "loose_freshness_survives" in names
    assert "noncritical_profile_survives" in names
    assert "hidden_profile_field_survives" in names
    assert "wrong_catalog_schema_survives" in names
    assert "wrong_profile_schema_survives" in names
    assert "boolean_freshness_survives" in names
    assert "hidden_catalog_field_survives" in names


def test_zenodex_oracle_consumer_profile_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-consumer-profile-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_consumer_profiles_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.consumer_profile_catalog_chaos_replay.v1"
    assert receipt["ok"] is True
