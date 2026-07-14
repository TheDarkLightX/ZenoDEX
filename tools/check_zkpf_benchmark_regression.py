#!/usr/bin/env python3
"""Compare exact-identity ZKPF benchmark records under an integer policy."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence

POLICY_SCHEMA = "zenodex/zkpf_benchmark_policy/v1"
RECORD_SCHEMA = "zenodex/zkpf_benchmark_record/v1"
REPORT_SCHEMA = "zenodex/zkpf_benchmark_comparison/v1"
MAX_JSON_BYTES = 256 * 1024
MAX_JSON_DEPTH = 128
MAX_METRICS = 64
_TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
_ROOT_RE = re.compile(r"^0x[0-9a-f]{64}$")
_POLICY_FIELDS = frozenset(
    {"schema", "minimum_samples", "minimum_warmups", "metrics"}
)
_METRIC_POLICY_FIELDS = frozenset(
    {"id", "max_regression_bps", "hard_maximum"}
)
_RECORD_FIELDS = frozenset(
    {
        "schema",
        "stage_id",
        "program_id",
        "proof_profile_id",
        "verifier_id",
        "workload_sha256",
        "machine_profile_sha256",
        "toolchain_sha256",
        "implementation_sha256",
        "sample_count",
        "warmup_count",
        "metrics",
        "authority",
    }
)
_FALSE_AUTHORITY = {
    "production_authority": False,
    "proof_authority": False,
    "release_authority": False,
    "settlement_authority": False,
}
_IDENTITY_FIELDS = (
    "stage_id",
    "program_id",
    "proof_profile_id",
    "verifier_id",
    "workload_sha256",
    "machine_profile_sha256",
    "toolchain_sha256",
)


class BenchmarkComparisonError(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class MetricPolicy:
    id: str
    max_regression_bps: int
    hard_maximum: int | None


@dataclass(frozen=True, slots=True)
class BenchmarkPolicy:
    minimum_samples: int
    minimum_warmups: int
    metrics: tuple[MetricPolicy, ...]
    raw: bytes

    @property
    def digest(self) -> str:
        return hashlib.sha256(self.raw).hexdigest()


@dataclass(frozen=True, slots=True)
class BenchmarkRecord:
    values: Mapping[str, object]
    metrics: Mapping[str, int]
    raw: bytes

    @property
    def digest(self) -> str:
        return hashlib.sha256(self.raw).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("ascii")


def _reject_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise BenchmarkComparisonError(f"duplicate JSON key: {key}")
        output[key] = value
    return output


def _reject_float(value: str) -> object:
    raise BenchmarkComparisonError(f"floating-point JSON number forbidden: {value}")


def _reject_constant(value: str) -> object:
    raise BenchmarkComparisonError(f"non-finite JSON number forbidden: {value}")


def _require_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in (0x5B, 0x7B):
            depth += 1
            if depth > MAX_JSON_DEPTH:
                raise BenchmarkComparisonError("JSON nesting exceeds limit")
        elif byte in (0x5D, 0x7D):
            depth -= 1
            if depth < 0:
                raise BenchmarkComparisonError("JSON nesting is malformed")
    if in_string or depth != 0:
        raise BenchmarkComparisonError("JSON structure is incomplete")


def strict_json_loads(raw: bytes) -> object:
    if type(raw) is not bytes or not raw or len(raw) > MAX_JSON_BYTES:
        raise BenchmarkComparisonError("JSON input must be nonempty bounded bytes")
    _require_depth(raw)
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_pairs,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
        )
    except BenchmarkComparisonError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise BenchmarkComparisonError("JSON input is invalid") from exc
    if canonical_json_bytes(value) != raw:
        raise BenchmarkComparisonError("JSON input is not canonical")
    return value


def _uint(
    value: object,
    *,
    label: str,
    minimum: int = 0,
    maximum: int = 2**63 - 1,
) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise BenchmarkComparisonError(
            f"{label} must be an integer in {minimum}..={maximum}"
        )
    return value


def _token(value: object, *, label: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise BenchmarkComparisonError(f"{label} is not a canonical token")
    return value


def _digest(value: object, *, label: str, root: bool = False) -> str:
    pattern = _ROOT_RE if root else _HEX64_RE
    if type(value) is not str or pattern.fullmatch(value) is None:
        raise BenchmarkComparisonError(f"{label} is not a canonical digest")
    if set(value.removeprefix("0x")) == {"0"}:
        raise BenchmarkComparisonError(f"{label} cannot be the zero sentinel")
    return value


def parse_policy(raw: bytes) -> BenchmarkPolicy:
    value = strict_json_loads(raw)
    if type(value) is not dict or frozenset(value) != _POLICY_FIELDS:
        raise BenchmarkComparisonError("benchmark policy field set mismatch")
    if value.get("schema") != POLICY_SCHEMA:
        raise BenchmarkComparisonError("benchmark policy schema mismatch")
    minimum_samples = _uint(
        value.get("minimum_samples"),
        label="minimum_samples",
        minimum=1,
        maximum=10_000,
    )
    minimum_warmups = _uint(
        value.get("minimum_warmups"),
        label="minimum_warmups",
        maximum=10_000,
    )
    rows = value.get("metrics")
    if not isinstance(rows, list) or not rows or len(rows) > MAX_METRICS:
        raise BenchmarkComparisonError("metric policy list is outside bounds")
    metrics: list[MetricPolicy] = []
    for index, row in enumerate(rows):
        if type(row) is not dict or frozenset(row) != _METRIC_POLICY_FIELDS:
            raise BenchmarkComparisonError(f"metric policy[{index}] field set mismatch")
        metric_id = _token(row.get("id"), label=f"metric policy[{index}].id")
        regression = _uint(
            row.get("max_regression_bps"),
            label=f"{metric_id}.max_regression_bps",
            maximum=100_000,
        )
        hard_raw = row.get("hard_maximum")
        hard_maximum = (
            None
            if hard_raw is None
            else _uint(hard_raw, label=f"{metric_id}.hard_maximum", minimum=1)
        )
        metrics.append(MetricPolicy(metric_id, regression, hard_maximum))
    if [metric.id for metric in metrics] != sorted(metric.id for metric in metrics):
        raise BenchmarkComparisonError("metric policies must be sorted by id")
    if len(metrics) != len({metric.id for metric in metrics}):
        raise BenchmarkComparisonError("metric policy ids must be unique")
    return BenchmarkPolicy(minimum_samples, minimum_warmups, tuple(metrics), raw)


def parse_record(raw: bytes, policy: BenchmarkPolicy) -> BenchmarkRecord:
    value = strict_json_loads(raw)
    if type(value) is not dict or frozenset(value) != _RECORD_FIELDS:
        raise BenchmarkComparisonError("benchmark record field set mismatch")
    if value.get("schema") != RECORD_SCHEMA:
        raise BenchmarkComparisonError("benchmark record schema mismatch")
    _token(value.get("stage_id"), label="stage_id")
    for field in ("program_id", "proof_profile_id", "verifier_id"):
        _digest(value.get(field), label=field, root=True)
    for field in (
        "workload_sha256",
        "machine_profile_sha256",
        "toolchain_sha256",
        "implementation_sha256",
    ):
        _digest(value.get(field), label=field)
    samples = _uint(value.get("sample_count"), label="sample_count", minimum=1)
    warmups = _uint(value.get("warmup_count"), label="warmup_count")
    if samples < policy.minimum_samples:
        raise BenchmarkComparisonError("benchmark sample count is below policy")
    if warmups < policy.minimum_warmups:
        raise BenchmarkComparisonError("benchmark warmup count is below policy")
    metric_values = value.get("metrics")
    expected = {metric.id for metric in policy.metrics}
    if type(metric_values) is not dict or set(metric_values) != expected:
        raise BenchmarkComparisonError("benchmark metric field set mismatch")
    parsed_metrics = {
        metric.id: _uint(metric_values.get(metric.id), label=metric.id, minimum=1)
        for metric in policy.metrics
    }
    if value.get("authority") != _FALSE_AUTHORITY:
        raise BenchmarkComparisonError("benchmark record attempted to promote authority")
    return BenchmarkRecord(value, parsed_metrics, raw)


def _ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def compare_records(
    policy: BenchmarkPolicy,
    baseline: BenchmarkRecord,
    candidate: BenchmarkRecord,
) -> tuple[dict[str, object], bool]:
    identity_mismatches = [
        field
        for field in _IDENTITY_FIELDS
        if baseline.values.get(field) != candidate.values.get(field)
    ]
    metric_results: list[dict[str, object]] = []
    metrics_pass = True
    for metric_policy in policy.metrics:
        baseline_value = baseline.metrics[metric_policy.id]
        candidate_value = candidate.metrics[metric_policy.id]
        allowed_numerator = baseline_value * (
            10_000 + metric_policy.max_regression_bps
        )
        threshold_passed = candidate_value * 10_000 <= allowed_numerator
        hard_passed = (
            metric_policy.hard_maximum is None
            or candidate_value <= metric_policy.hard_maximum
        )
        if candidate_value >= baseline_value:
            regression_bps = _ceil_div(
                (candidate_value - baseline_value) * 10_000,
                baseline_value,
            )
        else:
            regression_bps = -(
                ((baseline_value - candidate_value) * 10_000) // baseline_value
            )
        passed = threshold_passed and hard_passed
        metrics_pass = metrics_pass and passed
        metric_results.append(
            {
                "id": metric_policy.id,
                "baseline": baseline_value,
                "candidate": candidate_value,
                "regression_bps": regression_bps,
                "max_regression_bps": metric_policy.max_regression_bps,
                "hard_maximum": metric_policy.hard_maximum,
                "threshold_passed": threshold_passed,
                "hard_maximum_passed": hard_passed,
                "passed": passed,
            }
        )
    comparable = not identity_mismatches
    accepted = comparable and metrics_pass
    report = {
        "schema": REPORT_SCHEMA,
        "accepted": accepted,
        "comparable": comparable,
        "policy_sha256": policy.digest,
        "baseline_record_sha256": baseline.digest,
        "candidate_record_sha256": candidate.digest,
        "baseline_implementation_sha256": baseline.values[
            "implementation_sha256"
        ],
        "candidate_implementation_sha256": candidate.values[
            "implementation_sha256"
        ],
        "identity_mismatches": identity_mismatches,
        "metrics": metric_results,
        "authority": dict(_FALSE_AUTHORITY),
        "nonclaims": [
            "record bytes do not authenticate benchmark execution provenance",
            "passing relative budgets does not establish a production service-level objective",
            "this comparison grants no proof, release, settlement, or production authority",
        ],
    }
    return report, accepted


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--policy", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--require-pass", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        policy = parse_policy(arguments.policy.read_bytes())
        baseline = parse_record(arguments.baseline.read_bytes(), policy)
        candidate = parse_record(arguments.candidate.read_bytes(), policy)
        report, accepted = compare_records(policy, baseline, candidate)
        if arguments.pretty:
            print(json.dumps(report, indent=2, sort_keys=True))
        else:
            sys.stdout.buffer.write(canonical_json_bytes(report))
        return 0 if accepted or not arguments.require_pass else 1
    except (OSError, BenchmarkComparisonError) as exc:
        print(f"error: ZKPF benchmark comparison failed closed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
