from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_admitted_median3 import (  # noqa: E402
    aggregate_content_hash,
    sample_admitted_median3_aggregate,
    sample_hash,
)
from zenodex_oracle_report_admission import admission_content_hash  # noqa: E402
from zenodex_oracle_signed_report import (  # noqa: E402
    payload_content_hash,
    report_content_hash,
    signing_payload,
    submission_content_hash,
)


def _refresh_aggregate_id(aggregate: dict) -> None:
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)


def _refresh_admission_id(aggregate: dict, index: int) -> None:
    admission = aggregate["report_admissions"][index]
    admission["admission_id"] = admission_content_hash(admission)


def _refresh_submission_id(aggregate: dict, index: int) -> None:
    submission = aggregate["report_admissions"][index]["signed_submission"]
    submission["submission_id"] = submission_content_hash(submission)


def _refresh_payload_hash(aggregate: dict, index: int) -> None:
    admission = aggregate["report_admissions"][index]
    submission = admission["signed_submission"]
    report = submission["reports"][0]
    payload = signing_payload(
        chain_id=submission["chain_id"],
        reporter_id=submission["reporter_id"],
        reporter_pubkey=submission["reporter_pubkey"],
        report=report,
    )
    report["payload_hash"] = payload_content_hash(payload)


def _refresh_report_id(aggregate: dict, index: int) -> None:
    report = aggregate["report_admissions"][index]["signed_submission"]["reports"][0]
    report["report_id"] = report_content_hash(report)


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "admitted-median3.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_admitted_median3.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_admitted_median3_accepts_sample(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_admitted_median3_aggregate())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["value_e8"] == 100_000_000
    assert result["confidence_e8"] == 1_000_000
    assert result["deviation_bps"] == 100
    assert result["report_count"] == 3
    assert result["admission_count"] == 3
    assert result["evidence_floor"] == "O3"
    assert result["evidence_class"] == "O3"
    assert result["distinct_reporter_count"] == 3
    assert result["distinct_source_count"] == 3
    assert result["errors"] == []


def test_admitted_median3_rebases_sample_to_low_runtime_epoch(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate(
        current_epoch=1,
        latest_observed_epoch=1,
    )

    code, result = _run_verify(tmp_path, aggregate)

    assert code == 0
    assert result["status"] == "accepted"
    assert aggregate["current_epoch"] == 1
    assert result["observed_epoch"] == 1


def test_admitted_median3_centers_signed_reports_on_runtime_value(tmp_path: Path) -> None:
    # Arrange / Act.
    aggregate = sample_admitted_median3_aggregate(
        current_epoch=5,
        latest_observed_epoch=5,
        center_value_e8=10_000_000_000,
    )
    code, result = _run_verify(tmp_path, aggregate)

    # Assert.
    assert code == 0
    assert result["status"] == "accepted"
    assert result["value_e8"] == 10_000_000_000
    assert result["confidence_e8"] == 100_000_000
    assert result["deviation_bps"] == 100


def test_admitted_median3_rejects_aggregate_hash_forgery(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    forged = sample_hash("forged-admitted-median3")
    aggregate["aggregate_id"] = forged
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert f"aggregate_content_hash_mismatch:{forged}" in result["errors"]


def test_admitted_median3_rejects_wrong_median(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["aggregate"]["value_e8"] += 1
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_value_not_median" in result["errors"]


def test_admitted_median3_rejects_too_few_admissions(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["report_admissions"] = aggregate["report_admissions"][:2]
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "admitted_median3_requires_exactly_3_admissions:2" in result["errors"]


def test_admitted_median3_rejects_rejected_admission(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    report = aggregate["report_admissions"][1]["signed_submission"]["reports"][0]
    report["value_e8"] += 1
    _refresh_payload_hash(aggregate, 1)
    _refresh_report_id(aggregate, 1)
    _refresh_submission_id(aggregate, 1)
    _refresh_admission_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "report_admission_1_rejected:signed_submission_rejected:invalid_signature:0" in result["errors"]


def test_admitted_median3_rejects_duplicate_admission(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["report_admissions"][1] = aggregate["report_admissions"][0]
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert any(error.startswith("duplicate_admission_id:") for error in result["errors"])
    assert any(error.startswith("duplicate_report_id:") for error in result["errors"])
    assert any(error.startswith("duplicate_reporter_id:") for error in result["errors"])
    assert any(error.startswith("duplicate_source_id:") for error in result["errors"])


def test_admitted_median3_rejects_admission_epoch_mismatch(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["report_admissions"][0]["current_epoch"] -= 1
    _refresh_admission_id(aggregate, 0)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "admission_current_epoch_mismatch:0" in result["errors"]


def test_admitted_median3_rejects_deviation_over_policy(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["max_deviation_bps"] = 99
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_deviation_exceeds_policy" in result["errors"]


def test_admitted_median3_rejects_admission_evidence_below_floor(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["report_admissions"][1]["evidence_class"] = "O2"
    _refresh_admission_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "report_admission_1_rejected:evidence_class_below_critical_minimum" in result["errors"]
    assert "admission_evidence_class_below_floor:1:O2<O3" in result["errors"]


def test_admitted_median3_rejects_aggregate_evidence_overclaim(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["evidence_class"] = "O4"
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_evidence_class_exceeds_admission_minimum" in result["errors"]


def test_admitted_median3_rejects_aggregate_evidence_below_floor(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["evidence_class"] = "O2"
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "evidence_class_below_critical_minimum" in result["errors"]
    assert "aggregate_evidence_class_below_floor" in result["errors"]


def test_admitted_median3_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-admitted-median3.json"
    path.write_text('{"padding":"' + ("x" * 2_000_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_admitted_median3.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("admitted_median3_load_failed:admitted_median3_file_too_large:") for error in result["errors"])


def test_admitted_median3_sample_cli_emits_verifiable_aggregate(tmp_path: Path) -> None:
    path = tmp_path / "admitted-median3.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_admitted_median3.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_admitted_median3.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
