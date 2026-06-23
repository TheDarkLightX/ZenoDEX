from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_signed_report_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_signed_report_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 18
    assert receipt["rejected_case_count"] == 18
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "submission_hash_forgery_survives" in names
    assert "payload_mutation_survives_signature_check" in names
    assert "payload_hash_forgery_survives" in names
    assert "signature_mutation_survives" in names
    assert "report_id_forgery_survives" in names
    assert "sequence_gap_survives" in names
    assert "previous_report_chain_mismatch_survives" in names
    assert "first_previous_report_id_survives" in names
    assert "duplicate_report_id_survives" in names
    assert "hidden_submission_field_survives" in names
    assert "hidden_report_field_survives" in names
    assert "wrong_submission_schema_survives" in names
    assert "wrong_report_schema_survives" in names
    assert "bad_reporter_pubkey_survives" in names
    assert "bad_signature_length_survives" in names
    assert "boolean_value_survives" in names
    assert "reports_as_object_survives" in names
    assert "bad_source_token_survives" in names


def test_zenodex_oracle_signed_report_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-signed-report-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_signed_report_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.signed_report_chaos_replay.v1"
    assert receipt["ok"] is True
