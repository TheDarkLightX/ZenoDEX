from __future__ import annotations

import json
from pathlib import Path
from typing import cast

import pytest

from tools import check_zkpf_benchmark_regression as checker

REPO_ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = (
    REPO_ROOT
    / "config/proof_profiles/zkpf_benchmark_development_policy_v1.json"
)


def _policy() -> checker.BenchmarkPolicy:
    return checker.parse_policy(POLICY_PATH.read_bytes())


def _record(*, implementation: int, multiplier_bps: int = 10_000) -> dict[str, object]:
    baseline = {
        "cycles_max": 1_000_000,
        "journal_bytes": 4096,
        "peak_rss_bytes_max": 1_000_000_000,
        "proof_bytes": 600_000,
        "prove_time_ns_p50": 100_000_000,
        "prove_time_ns_p95": 120_000_000,
        "segment_count_max": 8,
        "verify_time_ns_p50": 4_000_000,
        "verify_time_ns_p95": 5_000_000,
    }
    metrics = {
        key: max(1, value * multiplier_bps // 10_000)
        for key, value in baseline.items()
    }
    return {
        "schema": checker.RECORD_SCHEMA,
        "stage_id": "spot_settlement_v7",
        "program_id": f"0x{1:064x}",
        "proof_profile_id": f"0x{2:064x}",
        "verifier_id": f"0x{3:064x}",
        "workload_sha256": f"{4:064x}",
        "machine_profile_sha256": f"{5:064x}",
        "toolchain_sha256": f"{6:064x}",
        "implementation_sha256": f"{implementation:064x}",
        "sample_count": 7,
        "warmup_count": 2,
        "metrics": metrics,
        "authority": {
            "production_authority": False,
            "proof_authority": False,
            "release_authority": False,
            "settlement_authority": False,
        },
    }


def _parsed(value: dict[str, object]) -> checker.BenchmarkRecord:
    return checker.parse_record(checker.canonical_json_bytes(value), _policy())


def _metric_rows(report: dict[str, object]) -> list[dict[str, object]]:
    return cast(list[dict[str, object]], report["metrics"])


def test_repository_policy_is_canonical_and_sorted() -> None:
    policy = _policy()
    assert policy.raw == POLICY_PATH.read_bytes()
    assert [metric.id for metric in policy.metrics] == sorted(
        metric.id for metric in policy.metrics
    )


def test_exact_identity_improvement_passes() -> None:
    report, accepted = checker.compare_records(
        _policy(),
        _parsed(_record(implementation=10)),
        _parsed(_record(implementation=11, multiplier_bps=9500)),
    )
    assert accepted is True
    assert report["comparable"] is True
    assert report["identity_mismatches"] == []
    assert all(row["passed"] for row in _metric_rows(report))
    authority = cast(dict[str, bool], report["authority"])
    assert all(value is False for value in authority.values())


def test_identity_substitution_rejects_before_performance_claim() -> None:
    baseline = _record(implementation=10)
    candidate = _record(implementation=11, multiplier_bps=5000)
    candidate["machine_profile_sha256"] = f"{99:064x}"
    report, accepted = checker.compare_records(
        _policy(), _parsed(baseline), _parsed(candidate)
    )
    assert accepted is False
    assert report["comparable"] is False
    assert report["identity_mismatches"] == ["machine_profile_sha256"]


def test_threshold_boundary_and_one_unit_over() -> None:
    policy = _policy()
    baseline = _record(implementation=10)
    candidate = _record(implementation=11)
    metrics = cast(dict[str, int], candidate["metrics"])
    metrics["prove_time_ns_p50"] = 105_000_000
    report, accepted = checker.compare_records(
        policy, _parsed(baseline), _parsed(candidate)
    )
    assert accepted is True
    result = next(
        row
        for row in _metric_rows(report)
        if row["id"] == "prove_time_ns_p50"
    )
    assert result["regression_bps"] == 500

    metrics["prove_time_ns_p50"] += 1
    report, accepted = checker.compare_records(
        policy, _parsed(baseline), _parsed(candidate)
    )
    assert accepted is False
    result = next(
        row
        for row in _metric_rows(report)
        if row["id"] == "prove_time_ns_p50"
    )
    assert result["threshold_passed"] is False


def test_zero_regression_metrics_reject_growth() -> None:
    baseline = _record(implementation=10)
    candidate = _record(implementation=11)
    metrics = cast(dict[str, int], candidate["metrics"])
    metrics["proof_bytes"] += 1
    report, accepted = checker.compare_records(
        _policy(), _parsed(baseline), _parsed(candidate)
    )
    assert accepted is False
    result = next(
        row for row in _metric_rows(report) if row["id"] == "proof_bytes"
    )
    assert result["max_regression_bps"] == 0
    assert result["passed"] is False


def test_hard_maximum_rejects_even_when_relative_threshold_passes() -> None:
    policy_value = json.loads(POLICY_PATH.read_text(encoding="ascii"))
    policy_value["metrics"][2]["hard_maximum"] = 900_000_000
    policy = checker.parse_policy(checker.canonical_json_bytes(policy_value))
    report, accepted = checker.compare_records(
        policy,
        checker.parse_record(
            checker.canonical_json_bytes(_record(implementation=10)),
            policy,
        ),
        checker.parse_record(
            checker.canonical_json_bytes(
                _record(implementation=11, multiplier_bps=9500)
            ),
            policy,
        ),
    )
    assert accepted is False
    result = next(
        row
        for row in _metric_rows(report)
        if row["id"] == "peak_rss_bytes_max"
    )
    assert result["threshold_passed"] is True
    assert result["hard_maximum_passed"] is False


def test_sample_metric_and_authority_validation_rejects() -> None:
    policy = _policy()
    for mutation, expected in (
        (lambda value: value.update({"sample_count": 4}), "sample count"),
        (
            lambda value: cast(dict[str, int], value["metrics"]).pop("cycles_max"),
            "metric field set",
        ),
        (
            lambda value: cast(dict[str, bool], value["authority"]).update(
                {"production_authority": True}
            ),
            "promote authority",
        ),
    ):
        value = _record(implementation=10)
        mutation(value)
        with pytest.raises(checker.BenchmarkComparisonError, match=expected):
            checker.parse_record(checker.canonical_json_bytes(value), policy)


def test_duplicate_float_noncanonical_and_zero_digest_reject() -> None:
    with pytest.raises(checker.BenchmarkComparisonError, match="duplicate JSON key"):
        checker.parse_policy(b'{"schema":"a","schema":"b"}\n')
    with pytest.raises(checker.BenchmarkComparisonError, match="floating-point"):
        checker.parse_policy(
            POLICY_PATH.read_bytes().replace(
                b'"minimum_samples":5',
                b'"minimum_samples":5.0',
            )
        )
    with pytest.raises(checker.BenchmarkComparisonError, match="not canonical"):
        checker.parse_policy(
            json.dumps(
                json.loads(POLICY_PATH.read_text()),
                indent=2,
            ).encode("ascii")
        )
    value = _record(implementation=10)
    value["workload_sha256"] = "0" * 64
    with pytest.raises(checker.BenchmarkComparisonError, match="zero sentinel"):
        _parsed(value)


def test_record_metric_values_reject_booleans_and_zero() -> None:
    policy = _policy()
    for replacement in (False, 0):
        value = _record(implementation=10)
        cast(dict[str, object], value["metrics"])["cycles_max"] = replacement
        with pytest.raises(checker.BenchmarkComparisonError, match="cycles_max"):
            checker.parse_record(checker.canonical_json_bytes(value), policy)
