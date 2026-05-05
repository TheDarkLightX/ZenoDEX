from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_signed_report import (  # noqa: E402
    payload_content_hash,
    report_content_hash,
    sample_hash,
    sample_submission,
    signing_payload,
    submission_content_hash,
)


def _refresh_payload_hash(submission: dict, index: int) -> None:
    report = submission["reports"][index]
    payload = signing_payload(
        chain_id=submission["chain_id"],
        reporter_id=submission["reporter_id"],
        reporter_pubkey=submission["reporter_pubkey"],
        report=report,
    )
    report["payload_hash"] = payload_content_hash(payload)


def _refresh_report_id(submission: dict, index: int) -> None:
    submission["reports"][index]["report_id"] = report_content_hash(submission["reports"][index])


def _refresh_submission_id(submission: dict) -> None:
    submission["submission_id"] = submission_content_hash(submission)


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "signed-report.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_signed_report.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_signed_report_accepts_sample_submission(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_submission())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["report_count"] == 2
    assert result["first_sequence"] == 0
    assert result["last_sequence"] == 1
    assert result["errors"] == []


def test_signed_report_rejects_payload_mutation_with_refreshed_hashes(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][1]["value_e8"] += 1
    _refresh_payload_hash(submission, 1)
    _refresh_report_id(submission, 1)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "invalid_signature:1" in result["errors"]


def test_signed_report_rejects_payload_hash_mismatch(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][0]["payload_hash"] = sample_hash("forged-payload")
    _refresh_report_id(submission, 0)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "payload_hash_mismatch:0" in result["errors"]


def test_signed_report_rejects_invalid_signature_with_refreshed_report_id(tmp_path: Path) -> None:
    submission = sample_submission()
    signature = submission["reports"][1]["signature"]
    replacement = "0" if signature[-1] != "0" else "1"
    submission["reports"][1]["signature"] = signature[:-1] + replacement
    _refresh_report_id(submission, 1)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "invalid_signature:1" in result["errors"]


def test_signed_report_rejects_report_id_forgery(tmp_path: Path) -> None:
    submission = sample_submission()
    forged = sample_hash("forged-report")
    submission["reports"][0]["report_id"] = forged
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "report_content_hash_mismatch:0" in result["errors"]


def test_signed_report_rejects_submission_id_forgery(tmp_path: Path) -> None:
    submission = sample_submission()
    forged = sample_hash("forged-submission")
    submission["submission_id"] = forged
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert f"submission_content_hash_mismatch:{forged}" in result["errors"]


def test_signed_report_rejects_sequence_gap(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][1]["sequence"] = 2
    _refresh_payload_hash(submission, 1)
    _refresh_report_id(submission, 1)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "sequence_not_contiguous:1" in result["errors"]
    assert "invalid_signature:1" in result["errors"]


def test_signed_report_rejects_previous_report_chain_mismatch(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][1]["previous_report_id"] = sample_hash("wrong-previous")
    _refresh_payload_hash(submission, 1)
    _refresh_report_id(submission, 1)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "previous_report_id_chain_mismatch:1" in result["errors"]


def test_signed_report_rejects_first_previous_report_id(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][0]["previous_report_id"] = sample_hash("unexpected-previous")
    _refresh_payload_hash(submission, 0)
    _refresh_report_id(submission, 0)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "first_report_previous_report_id_must_be_null" in result["errors"]
    assert "first_report_chain_mismatch" in result["errors"]


def test_signed_report_rejects_duplicate_report_id(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][1] = dict(submission["reports"][0])
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert any(error.startswith("duplicate_report_id:") for error in result["errors"])
    assert "duplicate_sequence:0" in result["errors"]


def test_signed_report_rejects_unknown_report_field(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][0]["debug_override"] = True
    _refresh_report_id(submission, 0)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "unknown_report_0_field:debug_override" in result["errors"]


def test_signed_report_rejects_bad_pubkey(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reporter_pubkey"] = "0x1234"
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "reporter_pubkey_must_be_48_bytes" in result["errors"]


def test_signed_report_rejects_bad_signature_length(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][0]["signature"] = "0x1234"
    _refresh_report_id(submission, 0)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "signature_must_be_96_bytes" in result["errors"]


def test_signed_report_rejects_boolean_value(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"][0]["value_e8"] = True
    _refresh_payload_hash(submission, 0)
    _refresh_report_id(submission, 0)
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "value_e8_must_be_int_between_1_and_1000000000000000000000000" in result["errors"]


def test_signed_report_rejects_reports_not_list(tmp_path: Path) -> None:
    submission = sample_submission()
    submission["reports"] = {"report_id": sample_hash("fake")}
    _refresh_submission_id(submission)
    code, result = _run_verify(tmp_path, submission)
    assert code == 2
    assert "reports_must_be_list" in result["errors"]


def test_signed_report_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-signed-report.json"
    path.write_text('{"padding":"' + ("x" * 500_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_signed_report.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("signed_report_load_failed:signed_report_file_too_large:") for error in result["errors"])


def test_signed_report_sample_cli_emits_verifiable_submission(tmp_path: Path) -> None:
    path = tmp_path / "signed-report.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_signed_report.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_signed_report.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["report_count"] == 2
