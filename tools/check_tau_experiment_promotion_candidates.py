#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from experiments.tau_lang_optimizations.trace_cases import optimization_tau_trace_cases  # noqa: E402


SCHEMA = "zenodex/tau/experiment-promotion-candidates/v1"
DEFAULT_MANIFEST = REPO_ROOT / "experiments" / "tau_lang_optimizations" / "promotion_candidates.json"
DEFAULT_TRACE_REPORT = REPO_ROOT / "generated" / "tau_lang_optimization_traces" / "report.json"
EXPERIMENT_ROOT = REPO_ROOT / "experiments" / "tau_lang_optimizations"
REQUIRED_BEFORE_RUNTIME_ACTIVATION = {
    "formal_completeness_complete",
    "semantic_contract",
    "behavior_atlas",
    "tau_differential_traces",
    "host_binding_tests",
    "operator_documentation",
    "security_review",
}
ALLOWED_PROMOTION_STATUSES = {"experiment_only", "candidate", "rejected"}
ALLOWED_KINDS = {
    "combinational_guard",
    "proof_gate",
    "certificate_guard",
    "bundle_or_composition",
    "stateful_policy_guard",
}


@dataclass(frozen=True)
class TauExperimentPromotionResult:
    errors: list[str]
    checked_candidates: list[str]
    checked_trace_cases: list[str]
    trace_report_checked: bool


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise ValueError(f"{path}: file does not exist") from None
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path}: invalid JSON: {exc}") from exc
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: expected JSON object")
    return raw


def _repo_path(path_text: object, *, ctx: str) -> Path | None:
    if not isinstance(path_text, str) or not path_text.strip():
        return None
    rel = Path(path_text)
    if rel.is_absolute():
        raise ValueError(f"{ctx}: path must be repository-relative")
    resolved = (REPO_ROOT / rel).resolve()
    try:
        resolved.relative_to(REPO_ROOT.resolve())
    except ValueError:
        raise ValueError(f"{ctx}: path must not escape repository root") from None
    return resolved


def _string_list(value: object, *, ctx: str, min_items: int = 1) -> list[str]:
    if not isinstance(value, list):
        raise ValueError(f"{ctx}: expected list")
    out: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            raise ValueError(f"{ctx}[{idx}]: expected non-empty string")
        out.append(item.strip())
    if len(out) < min_items:
        raise ValueError(f"{ctx}: expected at least {min_items} item(s)")
    return out


def _trace_case_report_index(report: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    atomic = report.get("atomic_results")
    if not isinstance(atomic, list):
        raise ValueError("trace report: atomic_results must be a list")
    indexed: dict[str, Mapping[str, Any]] = {}
    for idx, row in enumerate(atomic):
        if not isinstance(row, Mapping):
            raise ValueError(f"trace report: atomic_results[{idx}] must be an object")
        case_id = str(row.get("case_id", "")).strip()
        if not case_id:
            raise ValueError(f"trace report: atomic_results[{idx}] missing case_id")
        if case_id in indexed:
            raise ValueError(f"trace report: duplicate case_id {case_id}")
        indexed[case_id] = row
    return indexed


def _report_outputs_match(row: Mapping[str, Any], expected: list[dict[str, int]]) -> list[str]:
    errors: list[str] = []
    outputs_by_step = row.get("outputs_by_step")
    if not isinstance(outputs_by_step, Mapping):
        return ["outputs_by_step must be an object"]
    for step_idx, expected_outputs in enumerate(expected):
        got_step_raw = outputs_by_step.get(str(step_idx), outputs_by_step.get(step_idx))
        if not isinstance(got_step_raw, Mapping):
            errors.append(f"missing outputs for step {step_idx}")
            continue
        for output_name, expected_value in expected_outputs.items():
            got = got_step_raw.get(output_name)
            if got != expected_value:
                errors.append(f"{output_name}[{step_idx}] expected {expected_value} got {got!r}")
    return errors


def validate_tau_experiment_promotion_candidates(
    *,
    manifest_path: Path = DEFAULT_MANIFEST,
    trace_report_path: Path | None = None,
    require_trace_report: bool = False,
    strict_case_coverage: bool = True,
) -> TauExperimentPromotionResult:
    errors: list[str] = []
    checked_candidates: list[str] = []
    checked_trace_cases: list[str] = []

    try:
        manifest = _load_json_object(manifest_path)
    except ValueError as exc:
        return TauExperimentPromotionResult(
            errors=[str(exc)],
            checked_candidates=[],
            checked_trace_cases=[],
            trace_report_checked=False,
        )

    if manifest.get("schema") != SCHEMA:
        errors.append(f"{manifest_path}: schema must be {SCHEMA!r}")
    if manifest.get("status") != "experiment_only":
        errors.append(f"{manifest_path}: status must be 'experiment_only'")

    try:
        required = set(_string_list(manifest.get("required_before_runtime_activation"), ctx="required_before_runtime_activation"))
    except ValueError as exc:
        errors.append(str(exc))
        required = set()
    missing_required = REQUIRED_BEFORE_RUNTIME_ACTIVATION - required
    if missing_required:
        errors.append(f"{manifest_path}: missing required activation gates: {sorted(missing_required)}")

    generated_report_path: Path = DEFAULT_TRACE_REPORT
    try:
        manifest_report_path = _repo_path(manifest.get("generated_trace_report"), ctx="generated_trace_report")
    except ValueError as exc:
        errors.append(str(exc))
        manifest_report_path = None
    if manifest_report_path is not None:
        generated_report_path = manifest_report_path

    report_index: dict[str, Mapping[str, Any]] = {}
    trace_report_checked = False
    if require_trace_report:
        selected_report_path = trace_report_path or generated_report_path
        try:
            report = _load_json_object(selected_report_path)
            if report.get("ok") is not True:
                errors.append(f"{selected_report_path}: ok must be true")
            report_index = _trace_case_report_index(report)
            trace_report_checked = True
        except ValueError as exc:
            errors.append(str(exc))

    cases = optimization_tau_trace_cases()
    cases_by_id = {case.case_id: case for case in cases}
    case_ids_by_spec_path: dict[Path, set[str]] = {}
    for case in cases:
        case_ids_by_spec_path.setdefault(case.spec_path.resolve(), set()).add(case.case_id)

    candidates = manifest.get("candidates")
    if not isinstance(candidates, list) or not candidates:
        errors.append(f"{manifest_path}: candidates must be a non-empty list")
        candidates = []

    seen_specs: set[str] = set()
    for idx, candidate in enumerate(candidates):
        ctx = f"candidates[{idx}]"
        if not isinstance(candidate, Mapping):
            errors.append(f"{ctx}: expected object")
            continue

        scoped_error_count = len(errors)
        spec_id = str(candidate.get("spec_id", "")).strip()
        if not spec_id:
            errors.append(f"{ctx}: missing spec_id")
            continue
        if spec_id in seen_specs:
            errors.append(f"{ctx}: duplicate spec_id {spec_id}")
            continue
        seen_specs.add(spec_id)

        try:
            spec_path = _repo_path(candidate.get("spec_path"), ctx=f"{ctx}.spec_path")
        except ValueError as exc:
            errors.append(str(exc))
            continue
        if spec_path is None:
            errors.append(f"{ctx}.spec_path: missing path")
            continue
        if not spec_path.exists():
            errors.append(f"{ctx}.spec_path: {spec_path.relative_to(REPO_ROOT)} does not exist")
            continue
        if spec_path.suffix != ".tau":
            errors.append(f"{ctx}.spec_path: expected .tau file")
        try:
            spec_path.relative_to(EXPERIMENT_ROOT.resolve())
        except ValueError:
            errors.append(f"{ctx}.spec_path: experiment candidates must stay under {EXPERIMENT_ROOT.relative_to(REPO_ROOT)}")
        if spec_path.stem != spec_id:
            errors.append(f"{ctx}: spec_id must match spec file stem {spec_path.stem!r}")

        promotion_status = str(candidate.get("promotion_status", "")).strip()
        if promotion_status not in ALLOWED_PROMOTION_STATUSES:
            errors.append(f"{ctx}.promotion_status: must be one of {sorted(ALLOWED_PROMOTION_STATUSES)}")

        kind = str(candidate.get("kind", "")).strip()
        if kind not in ALLOWED_KINDS:
            errors.append(f"{ctx}.kind: must be one of {sorted(ALLOWED_KINDS)}")

        minimum_timeout_raw = candidate.get("minimum_trace_timeout_s")
        if not isinstance(minimum_timeout_raw, (int, float)) or float(minimum_timeout_raw) <= 0:
            errors.append(f"{ctx}.minimum_trace_timeout_s: expected positive number")
            minimum_timeout_s = 0.0
        else:
            minimum_timeout_s = float(minimum_timeout_raw)

        expected_cmd = f"python3 tests/tau/check_formal_completeness.py --analyze {spec_path.relative_to(REPO_ROOT).as_posix()}"
        if candidate.get("formal_completeness_cmd") != expected_cmd:
            errors.append(f"{ctx}.formal_completeness_cmd: expected {expected_cmd!r}")

        try:
            trace_case_ids = _string_list(candidate.get("trace_case_ids"), ctx=f"{ctx}.trace_case_ids", min_items=2)
        except ValueError as exc:
            errors.append(str(exc))
            trace_case_ids = []
        if len(trace_case_ids) != len(set(trace_case_ids)):
            errors.append(f"{ctx}.trace_case_ids: duplicate case id")

        actual_case_ids = case_ids_by_spec_path.get(spec_path.resolve(), set())
        if strict_case_coverage and set(trace_case_ids) != actual_case_ids:
            errors.append(
                f"{ctx}.trace_case_ids: must exactly match trace cases for {spec_id}; "
                f"expected {sorted(actual_case_ids)} got {sorted(trace_case_ids)}"
            )

        for case_id in trace_case_ids:
            case = cases_by_id.get(case_id)
            if case is None:
                errors.append(f"{ctx}.trace_case_ids: unknown case {case_id}")
                continue
            if case.spec_path.resolve() != spec_path.resolve():
                errors.append(f"{ctx}.trace_case_ids: {case_id} points at {case.spec_path.relative_to(REPO_ROOT)}, expected {spec_path.relative_to(REPO_ROOT)}")
            if float(case.timeout_s) < minimum_timeout_s:
                errors.append(f"{ctx}.trace_case_ids: {case_id} timeout {case.timeout_s}s is below minimum {minimum_timeout_s}s")
            if not case.expected:
                errors.append(f"{ctx}.trace_case_ids: {case_id} has no expected outputs")
            if require_trace_report and report_index:
                report_row = report_index.get(case_id)
                if report_row is None:
                    errors.append(f"{ctx}.trace_case_ids: trace report missing {case_id}")
                else:
                    if report_row.get("status") != "PASS":
                        errors.append(f"{ctx}.trace_case_ids: trace report status for {case_id} is {report_row.get('status')!r}")
                    for mismatch in _report_outputs_match(report_row, case.expected):
                        errors.append(f"{ctx}.trace_case_ids: trace report {case_id}: {mismatch}")
                    checked_trace_cases.append(case_id)

        for key, min_items in (
            ("host_assumptions", 2),
            ("non_claims", 2),
            ("runtime_activation_blockers", 2),
        ):
            try:
                _string_list(candidate.get(key), ctx=f"{ctx}.{key}", min_items=min_items)
            except ValueError as exc:
                errors.append(str(exc))

        if len(errors) == scoped_error_count:
            checked_candidates.append(spec_id)

    return TauExperimentPromotionResult(
        errors=errors,
        checked_candidates=checked_candidates,
        checked_trace_cases=checked_trace_cases,
        trace_report_checked=trace_report_checked,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate experimental Tau promotion-candidate metadata and optional exact trace artifacts."
    )
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Path to promotion_candidates.json.")
    parser.add_argument("--trace-report", default="", help="Optional generated trace report path.")
    parser.add_argument(
        "--require-trace-report",
        action="store_true",
        help="Require generated/tau_lang_optimization_traces/report.json and validate expected outputs against it.",
    )
    parser.add_argument(
        "--no-strict-case-coverage",
        action="store_true",
        help="Allow manifest trace_case_ids to be a subset instead of the exact trace cases for each candidate spec.",
    )
    args = parser.parse_args()

    result = validate_tau_experiment_promotion_candidates(
        manifest_path=Path(args.manifest),
        trace_report_path=Path(args.trace_report) if args.trace_report else None,
        require_trace_report=args.require_trace_report,
        strict_case_coverage=not args.no_strict_case_coverage,
    )
    if result.errors:
        for error in result.errors:
            print(f"ERROR: {error}")
        return 1

    print(f"checked Tau experiment promotion candidates: {len(result.checked_candidates)}")
    for spec_id in result.checked_candidates:
        print(f"  {spec_id}")
    if result.trace_report_checked:
        print(f"checked trace report cases: {len(result.checked_trace_cases)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
