from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_report_admission import (  # noqa: E402
    admission_content_hash,
    sample_report_admission,
)
from zenodex_oracle_signed_report import (  # noqa: E402
    payload_content_hash,
    report_content_hash,
    sample_hash,
    signing_payload,
    submission_content_hash,
)
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


def _refresh_payload_hash(admission: dict, index: int) -> None:
    submission = admission["signed_submission"]
    report = submission["reports"][index]
    payload = signing_payload(
        chain_id=submission["chain_id"],
        reporter_id=submission["reporter_id"],
        reporter_pubkey=submission["reporter_pubkey"],
        report=report,
    )
    report["payload_hash"] = payload_content_hash(payload)


def _refresh_report_id(admission: dict, index: int) -> None:
    report = admission["signed_submission"]["reports"][index]
    report["report_id"] = report_content_hash(report)


def _refresh_submission_id(admission: dict) -> None:
    admission["signed_submission"]["submission_id"] = submission_content_hash(admission["signed_submission"])


def _refresh_source_diversity_id(admission: dict) -> None:
    admission["source_diversity"]["source_set_id"] = source_set_content_hash(admission["source_diversity"])


def _refresh_admission_id(admission: dict) -> None:
    admission["admission_id"] = admission_content_hash(admission)


def _lifecycle_submit(admission: dict, report_id: str) -> dict:
    for event in admission["reporter_lifecycle"]["events"]:
        if event.get("type") == "submit_report" and event.get("report_id") == report_id:
            return event
    raise AssertionError("submit event not found")


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "report-admission.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_report_admission.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_report_admission_accepts_sample(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_report_admission())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["admitted_report_count"] == 2
    assert result["reporter_id"] == "reporter.sample"
    assert result["evidence_class"] == "O3"
    assert result["errors"] == []


def test_report_admission_rejects_admission_id_forgery(tmp_path: Path) -> None:
    admission = sample_report_admission()
    forged = sample_hash("forged-admission")
    admission["admission_id"] = forged
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert f"admission_content_hash_mismatch:{forged}" in result["errors"]


def test_report_admission_rejects_signed_payload_mutation(tmp_path: Path) -> None:
    admission = sample_report_admission()
    report = admission["signed_submission"]["reports"][1]
    submit_event = _lifecycle_submit(admission, report["report_id"])
    report["value_e8"] += 1
    _refresh_payload_hash(admission, 1)
    _refresh_report_id(admission, 1)
    submit_event["report_id"] = report["report_id"]
    submit_event["value_hash"] = report["payload_hash"]
    _refresh_submission_id(admission)
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "signed_submission_rejected:invalid_signature:1" in result["errors"]


def test_report_admission_rejects_reporter_mismatch(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["reporter_lifecycle"]["reporter_id"] = "reporter.other"
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "reporter_lifecycle_reporter_id_mismatch" in result["errors"]


def test_report_admission_rejects_reporter_pubkey_mismatch(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["reporter_lifecycle"]["reporter_pubkey"] = "0x" + ("22" * 48)
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "reporter_lifecycle_reporter_pubkey_mismatch" in result["errors"]


def test_report_admission_rejects_missing_lifecycle_submit(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["reporter_lifecycle"]["events"] = admission["reporter_lifecycle"]["events"][:-1]
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "lifecycle_missing_submit_report:1" in result["errors"]


def test_report_admission_rejects_lifecycle_query_mismatch(tmp_path: Path) -> None:
    admission = sample_report_admission()
    report = admission["signed_submission"]["reports"][0]
    _lifecycle_submit(admission, report["report_id"])["query_id"] = sample_hash("wrong-query")
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "lifecycle_submit_query_mismatch:0" in result["errors"]


def test_report_admission_rejects_lifecycle_value_hash_mismatch(tmp_path: Path) -> None:
    admission = sample_report_admission()
    report = admission["signed_submission"]["reports"][0]
    _lifecycle_submit(admission, report["report_id"])["value_hash"] = sample_hash("wrong-value")
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "lifecycle_submit_value_hash_mismatch:0" in result["errors"]


def test_report_admission_rejects_extra_lifecycle_submit(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["reporter_lifecycle"]["events"].append(
        {
            "type": "submit_report",
            "epoch": 102,
            "report_id": sample_hash("extra-report"),
            "query_id": admission["signed_submission"]["reports"][0]["query_id"],
            "value_hash": sample_hash("extra-value"),
        }
    )
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert any(error.startswith("lifecycle_extra_submit_report:") for error in result["errors"])


def test_report_admission_rejects_source_not_in_diversity(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["source_diversity"]["sources"][0]["source_id"] = "source.unused.alt"
    _refresh_source_diversity_id(admission)
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "report_source_not_in_source_diversity:0" in result["errors"]
    assert "report_source_not_in_source_diversity:1" in result["errors"]


def test_report_admission_rejects_source_diversity_query_mismatch(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["source_diversity"]["query_id"] = sample_hash("other-source-diversity-query")
    _refresh_source_diversity_id(admission)
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "source_diversity_query_mismatch:0" in result["errors"]


def test_report_admission_rejects_future_report(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["current_epoch"] = 100
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "admitted_report_from_future:1" in result["errors"]


def test_report_admission_rejects_stale_report(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["max_staleness_epochs"] = 2
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "admitted_report_stale:0" in result["errors"]


def test_report_admission_rejects_below_o3_evidence_class(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["evidence_class"] = "O2"
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "evidence_class_below_critical_minimum" in result["errors"]


def test_report_admission_rejects_rejected_lifecycle_trace(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["reporter_lifecycle"]["events"][1]["amount"] = 0
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "reporter_lifecycle_rejected:report_submitted_under_required_bond" in result["errors"]


def test_report_admission_rejects_unknown_top_level_field(tmp_path: Path) -> None:
    admission = sample_report_admission()
    admission["trusted_override"] = True
    _refresh_admission_id(admission)
    code, result = _run_verify(tmp_path, admission)
    assert code == 2
    assert "unknown_admission_field:trusted_override" in result["errors"]


def test_report_admission_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-report-admission.json"
    path.write_text('{"padding":"' + ("x" * 1_000_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_report_admission.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("report_admission_load_failed:report_admission_file_too_large:") for error in result["errors"])


def test_report_admission_sample_cli_emits_verifiable_admission(tmp_path: Path) -> None:
    path = tmp_path / "report-admission.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_report_admission.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_report_admission.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["admitted_report_count"] == 2
