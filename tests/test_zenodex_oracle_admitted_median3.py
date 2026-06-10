from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_admitted_median3 import (  # noqa: E402
    _canonical_pubkey,
    _single_report_admission,
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
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


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


def test_admitted_median3_accepts_distinct_reporter_pubkeys(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_admitted_median3_aggregate())
    assert code == 0
    assert result["status"] == "accepted"
    assert result["distinct_reporter_pubkey_count"] == 3


def test_admitted_median3_rejects_one_key_masquerading_as_two_reporters(tmp_path: Path) -> None:
    # A single signing key cannot supply two of the three median inputs even when
    # it labels itself with distinct reporter_ids and distinct sources. The
    # quorum's independence is a property of the signing key, not the self-chosen
    # reporter_id string.
    aggregate = sample_admitted_median3_aggregate()
    second = aggregate["report_admissions"][1]
    submission = second["signed_submission"]
    report = submission["reports"][0]
    aggregate["report_admissions"][1] = _single_report_admission(
        private_key=43,  # same key as report_admissions[0] (reporter.alpha)
        reporter_id=submission["reporter_id"],  # distinct reporter_id (reporter.beta)
        source_id=report["source_id"],  # distinct source
        query_id=aggregate["query_id"],
        value_e8=report["value_e8"],
        observed_epoch=report["observed_epoch"],
        source_diversity=second["source_diversity"],
        current_epoch=aggregate["current_epoch"],
        max_staleness_epochs=aggregate["max_staleness_epochs"],
    )
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert any(error.startswith("duplicate_reporter_pubkey:") for error in result["errors"])
    # The label-level distinctness still reads 3 — proving the pubkey check, not
    # the reporter_id check, is what closes the Sybil-via-shared-key gap.
    assert result["distinct_reporter_count"] == 3
    assert result["distinct_reporter_pubkey_count"] == 2


def test_canonical_pubkey_collapses_prefix_and_case() -> None:
    body = "ab12" * 24  # 96 hex chars
    assert _canonical_pubkey("0x" + body) == body
    assert _canonical_pubkey("0X" + body.upper()) == body
    assert _canonical_pubkey(body.upper()) == body
    assert _canonical_pubkey("0x" + body) == _canonical_pubkey(body.upper())


def test_admitted_median3_rejects_one_key_under_reencoded_pubkey(tmp_path: Path) -> None:
    # The shared-key masquerade must still be caught when the second admission
    # declares the same key in a different hex encoding (no 0x prefix, upper
    # case). The signature still verifies, so only canonical comparison closes it.
    from zenodex_oracle_report_admission import (  # noqa: E402
        admission_content_hash,
        sample_lifecycle_for_signed_submission,
    )
    from zenodex_oracle_signed_report import (  # noqa: E402
        G2Basic,
        SUBMISSION_SCHEMA,
        _build_report,
        submission_content_hash,
    )

    aggregate = sample_admitted_median3_aggregate()
    target = aggregate["report_admissions"][1]
    submission = target["signed_submission"]
    report = submission["reports"][0]
    chain_id = str(submission["chain_id"])
    reporter_id = str(submission["reporter_id"])
    reencoded = G2Basic.SkToPk(43).hex().upper()  # key 43, no 0x prefix, upper case
    new_report = _build_report(
        private_key=43,
        chain_id=chain_id,
        reporter_id=reporter_id,
        reporter_pubkey=reencoded,
        query_id=str(aggregate["query_id"]),
        source_id=str(report["source_id"]),
        value_e8=int(report["value_e8"]),
        observed_epoch=int(report["observed_epoch"]),
        sequence=0,
        previous_report_id=None,
    )
    new_submission = {
        "schema": SUBMISSION_SCHEMA,
        "chain_id": chain_id,
        "reporter_id": reporter_id,
        "reporter_pubkey": reencoded,
        "reports": [new_report],
    }
    new_submission["submission_id"] = submission_content_hash(new_submission)
    new_admission = {
        "schema": "zenodex.oracle.report_admission.v1",
        "current_epoch": int(aggregate["current_epoch"]),
        "max_staleness_epochs": int(aggregate["max_staleness_epochs"]),
        "evidence_class": "O3",
        "signed_submission": new_submission,
        "reporter_lifecycle": sample_lifecycle_for_signed_submission(new_submission),
        "source_diversity": target["source_diversity"],
    }
    new_admission["admission_id"] = admission_content_hash(new_admission)
    aggregate["report_admissions"][1] = new_admission
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)

    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert any(error.startswith("duplicate_reporter_pubkey:") for error in result["errors"])
    assert result["distinct_reporter_pubkey_count"] == 2


def test_admitted_median3_rejects_admission_epoch_mismatch(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    aggregate["report_admissions"][0]["current_epoch"] -= 1
    _refresh_admission_id(aggregate, 0)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "admission_current_epoch_mismatch:0" in result["errors"]


def test_admitted_median3_rejects_mismatched_source_set_ids(tmp_path: Path) -> None:
    aggregate = sample_admitted_median3_aggregate()
    receipt = aggregate["report_admissions"][2]["source_diversity"]
    receipt["min_distinct_operators"] = 1
    receipt["source_set_id"] = source_set_content_hash(receipt)
    _refresh_admission_id(aggregate, 2)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "admission_source_set_mismatch" in result["errors"]


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
