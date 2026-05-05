from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_median3 import content_hash, sample_aggregate, sample_hash  # noqa: E402
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


def _refresh_report_id(aggregate: dict, index: int) -> None:
    report = aggregate["reports"][index]
    report["report_id"] = content_hash(report, omit_key="report_id")


def _refresh_aggregate_id(aggregate: dict) -> None:
    aggregate["aggregate_id"] = content_hash(aggregate, omit_key="aggregate_id")


def _refresh_source_diversity_id(aggregate: dict) -> None:
    aggregate["source_diversity"]["source_set_id"] = source_set_content_hash(aggregate["source_diversity"])


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "aggregate.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_median3.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_median3_accepts_sample_aggregate(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_aggregate())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["value_e8"] == 100_000_000
    assert result["confidence_e8"] == 1_000_000
    assert result["deviation_bps"] == 100
    assert result["report_count"] == 3
    assert result["distinct_reporter_count"] == 3
    assert result["distinct_source_count"] == 3
    assert result["errors"] == []


def test_median3_rejects_wrong_aggregate_value(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["aggregate"]["value_e8"] += 1
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_value_not_median" in result["errors"]


def test_median3_rejects_wrong_confidence(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["aggregate"]["confidence_e8"] += 1
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_confidence_mismatch" in result["errors"]


def test_median3_rejects_wrong_deviation(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["aggregate"]["deviation_bps"] += 1
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_deviation_mismatch" in result["errors"]


def test_median3_rejects_deviation_over_policy(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["max_deviation_bps"] = 99
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "aggregate_deviation_exceeds_policy" in result["errors"]


def test_median3_rejects_report_query_mismatch(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["reports"][1]["query_id"] = sample_hash("other-query")
    _refresh_report_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "report_query_id_mismatch:1" in result["errors"]


def test_median3_rejects_future_report(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["reports"][0]["observed_epoch"] = 105
    _refresh_report_id(aggregate, 0)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "report_from_future:0" in result["errors"]


def test_median3_rejects_stale_report(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["reports"][0]["observed_epoch"] = 93
    _refresh_report_id(aggregate, 0)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "report_stale:0" in result["errors"]


def test_median3_rejects_duplicate_reporter_and_source(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["reports"][1]["reporter_id"] = aggregate["reports"][0]["reporter_id"]
    aggregate["reports"][1]["source_id"] = aggregate["reports"][0]["source_id"]
    _refresh_report_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert any(error.startswith("duplicate_reporter_id:") for error in result["errors"])
    assert any(error.startswith("duplicate_source_id:") for error in result["errors"])
    assert "not_enough_distinct_sources" in result["errors"]


def test_median3_rejects_forged_report_id(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    forged_report_id = sample_hash("forged-report")
    aggregate["reports"][0]["report_id"] = forged_report_id
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert f"report_content_hash_mismatch:{forged_report_id}" in result["errors"]


def test_median3_rejects_forged_aggregate_id(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    forged_aggregate_id = sample_hash("forged-aggregate")
    aggregate["aggregate_id"] = forged_aggregate_id
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert f"aggregate_content_hash_mismatch:{forged_aggregate_id}" in result["errors"]


def test_median3_rejects_wrong_report_count(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["reports"] = aggregate["reports"][:2]
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "median3_requires_exactly_3_reports:2" in result["errors"]


def test_median3_rejects_source_diversity_report_source_mismatch(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["source_diversity"]["sources"][0]["source_id"] = "source.unused.alt"
    _refresh_source_diversity_id(aggregate)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "source_diversity_report_source_set_mismatch" in result["errors"]


def test_median3_rejects_source_diversity_correlation(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["source_diversity"]["sources"][1]["operator_id"] = (
        aggregate["source_diversity"]["sources"][0]["operator_id"]
    )
    _refresh_source_diversity_id(aggregate)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "source_diversity_rejected:not_enough_distinct_operators" in result["errors"]
    assert "source_diversity_rejected:operator_concentration_exceeds_policy" in result["errors"]


def test_median3_rejects_source_diversity_query_mismatch(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["source_diversity"]["query_id"] = sample_hash("other-source-diversity-query")
    _refresh_source_diversity_id(aggregate)
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "source_diversity_query_id_mismatch" in result["errors"]


def test_median3_rejects_unknown_report_field(tmp_path: Path) -> None:
    aggregate = sample_aggregate()
    aggregate["reports"][0]["debug_override"] = True
    _refresh_aggregate_id(aggregate)
    code, result = _run_verify(tmp_path, aggregate)
    assert code == 2
    assert "unknown_report_0_field:debug_override" in result["errors"]


def test_median3_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-aggregate.json"
    path.write_text('{"padding":"' + ("x" * 500_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_median3.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("aggregate_load_failed:aggregate_file_too_large:") for error in result["errors"])


def test_median3_sample_cli_emits_verifiable_aggregate(tmp_path: Path) -> None:
    path = tmp_path / "sample-aggregate.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_median3.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_median3.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["deviation_bps"] == 100
