#!/usr/bin/env python3
"""Exact-rational checker for approximation-plus-defect research receipts.

The checker validates canonical shape, exact rational budget arithmetic, finite
interval coverage, adjacent overlap agreement, and a SHA-256 binding over the
receipt body. Certificate identifiers are opaque references. This module does
not validate the analytic proofs named by those identifiers and has no runtime
or settlement authority.

An accepted region satisfies the arithmetic obligation

    allocated_defect + allocated_interaction + allocated_reconstruction
        <= certified_model_margin.

Every allocated component must also dominate the bound stated by its upstream
certificate. Missing or malformed evidence yields ``UNKNOWN``.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

SCHEMA = "zenodex-approximation-defect-receipt/v1"
REPORT_SCHEMA = "zenodex-approximation-defect-check-report/v1"
THEOREM = "ApproximationDefectCertificates.finiteCover_target_nonneg"
MAX_CANONICAL_BYTES = 1_000_000
MAX_INPUT_BYTES = 1_000_000
MAX_NAMED_RECEIPTS = 512
MAX_RATIONAL_CHARS = 128
MAX_REGIONS = 256

_TOP_FIELDS = {
    "schema",
    "claim_id",
    "domain",
    "regions",
    "overlaps",
    "coverage_root",
}
_BOUND_BODY_FIELDS = _TOP_FIELDS - {"coverage_root"}
_INTERVAL_FIELDS = {"lo", "hi"}
_REGION_FIELDS = {"region_id", "interval", "model", "errors"}
_MODEL_FIELDS = {"model_id", "certificate_id", "certified_margin"}
_ERROR_TYPES = ("defect", "interaction", "reconstruction")
_ERROR_FIELDS = set(_ERROR_TYPES)
_COMPONENT_FIELDS = {"certificate_id", "certified_bound", "allocated_bound"}
_OVERLAP_FIELDS = {
    "left_region_id",
    "right_region_id",
    "interval",
    "left_contract_id",
    "right_contract_id",
}
_IDENTIFIER_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:-]{0,127}\Z")
_RATIONAL_RE = re.compile(r"(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")


class CheckFailure(ValueError):
    """Stable fail-closed rejection with a machine-readable reason code."""

    def __init__(self, reason_code: str, message: str) -> None:
        super().__init__(message)
        self.reason_code = reason_code
        self.message = message


@dataclass(frozen=True)
class CheckResult:
    status: str
    reason_code: str | None
    theorem: str | None
    detail: dict[str, Any]

    def to_json(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "reason_code": self.reason_code,
            "theorem": self.theorem,
            "detail": self.detail,
        }


@dataclass(frozen=True)
class ParsedRegion:
    region_id: str
    lo: Fraction
    hi: Fraction
    model_id: str
    model_margin: Fraction
    total_allocated_error: Fraction


def _fail(reason_code: str, message: str) -> None:
    raise CheckFailure(reason_code, message)


def _object(
    value: object,
    expected_fields: set[str],
    context: str,
) -> dict[str, Any]:
    if not isinstance(value, dict):
        _fail("TYPE_MISMATCH", f"{context} must be an object")
    if set(value) != expected_fields:
        missing = sorted(expected_fields - set(value))
        extra = sorted(set(value) - expected_fields)
        _fail(
            "FIELD_SET_MISMATCH",
            f"{context} fields differ; missing={missing}, extra={extra}",
        )
    return value


def _list(value: object, context: str) -> list[Any]:
    if not isinstance(value, list):
        _fail("TYPE_MISMATCH", f"{context} must be a list")
    return value


def _identifier(value: object, context: str) -> str:
    if not isinstance(value, str) or _IDENTIFIER_RE.fullmatch(value) is None:
        _fail("INVALID_IDENTIFIER", f"{context} is not a canonical identifier")
    return value


def _rational(value: object, context: str) -> Fraction:
    if not isinstance(value, str):
        _fail("INVALID_RATIONAL", f"{context} is not a canonical rational string")
    if len(value) > MAX_RATIONAL_CHARS:
        _fail(
            "RESOURCE_LIMIT_EXCEEDED",
            f"{context} exceeds the {MAX_RATIONAL_CHARS}-character rational limit",
        )
    if _RATIONAL_RE.fullmatch(value) is None:
        _fail("INVALID_RATIONAL", f"{context} is not a canonical rational string")
    parsed = Fraction(value)
    if ratstr(parsed) != value:
        _fail("INVALID_RATIONAL", f"{context} is not reduced canonically")
    return parsed


def ratstr(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _canonical_json(value: object) -> bytes:
    try:
        encoded = json.dumps(
            value,
            allow_nan=False,
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
    except (RecursionError, TypeError, ValueError) as exc:
        _fail("NONCANONICAL_JSON", f"receipt is not canonical JSON: {exc}")
    raw = encoded.encode("ascii")
    if len(raw) > MAX_CANONICAL_BYTES:
        _fail(
            "RESOURCE_LIMIT_EXCEEDED",
            f"canonical receipt exceeds {MAX_CANONICAL_BYTES} bytes",
        )
    return raw


def coverage_root(receipt_body: dict[str, object]) -> str:
    """Return the canonical SHA-256 binding for a body without its root."""

    body = _object(receipt_body, _BOUND_BODY_FIELDS, "receipt body")
    return "sha256:" + hashlib.sha256(_canonical_json(body)).hexdigest()


def seal_receipt(receipt_body: dict[str, object]) -> dict[str, object]:
    """Deep-copy and bind a receipt body with its canonical coverage root."""

    body = copy.deepcopy(receipt_body)
    root = coverage_root(body)
    return {**body, "coverage_root": root}


def _parse_interval(value: object, context: str) -> tuple[Fraction, Fraction]:
    interval = _object(value, _INTERVAL_FIELDS, context)
    lo = _rational(interval["lo"], f"{context}.lo")
    hi = _rational(interval["hi"], f"{context}.hi")
    return lo, hi


def _require_valid_domain(lo: Fraction, hi: Fraction) -> None:
    if hi < lo:
        _fail("INVALID_DOMAIN", "domain has hi < lo")


def _parse_component(
    value: object,
    context: str,
) -> Fraction:
    component = _object(value, _COMPONENT_FIELDS, context)
    _identifier(component["certificate_id"], f"{context}.certificate_id")
    certified = _rational(component["certified_bound"], f"{context}.certified_bound")
    allocated = _rational(component["allocated_bound"], f"{context}.allocated_bound")
    if certified < 0:
        _fail("NEGATIVE_CERTIFIED_BOUND", f"{context} has a negative certified bound")
    if allocated < 0:
        _fail("NEGATIVE_ALLOCATED_BOUND", f"{context} has a negative allocated bound")
    if allocated < certified:
        _fail(
            "ALLOCATED_BOUND_UNDERESTATES_CERTIFIED_BOUND",
            f"{context} allocated bound is below its certified bound",
        )
    return allocated


def _parse_region(value: object, index: int) -> ParsedRegion:
    context = f"regions[{index}]"
    region = _object(value, _REGION_FIELDS, context)
    region_id = _identifier(region["region_id"], f"{context}.region_id")
    lo, hi = _parse_interval(region["interval"], f"{context}.interval")
    if hi < lo:
        _fail("INVALID_REGION_INTERVAL", f"{context} has hi < lo")

    model = _object(region["model"], _MODEL_FIELDS, f"{context}.model")
    model_id = _identifier(model["model_id"], f"{context}.model.model_id")
    _identifier(model["certificate_id"], f"{context}.model.certificate_id")
    margin = _rational(model["certified_margin"], f"{context}.model.certified_margin")
    if margin < 0:
        _fail("NEGATIVE_MODEL_MARGIN", f"{context} has a negative model margin")

    errors = _object(region["errors"], _ERROR_FIELDS, f"{context}.errors")
    allocated = [
        _parse_component(errors[error_type], f"{context}.errors.{error_type}")
        for error_type in _ERROR_TYPES
    ]
    total = sum(allocated, Fraction(0))
    if margin < total:
        _fail(
            "MODEL_MARGIN_EXCEEDED",
            f"{context} total allocated error exceeds the model margin",
        )
    return ParsedRegion(region_id, lo, hi, model_id, margin, total)


def _check_region_cover(
    domain_lo: Fraction,
    domain_hi: Fraction,
    regions: list[ParsedRegion],
) -> None:
    if not regions:
        _fail("EMPTY_REGION_SET", "regions must contain at least one region")

    ids = [region.region_id for region in regions]
    if len(set(ids)) != len(ids):
        _fail("DUPLICATE_REGION_ID", "region identifiers must be unique")

    order = [(region.lo, region.hi, region.region_id) for region in regions]
    if order != sorted(order):
        _fail("REGION_ORDER_NONCANONICAL", "regions are not in canonical order")

    for region in regions:
        if region.lo < domain_lo or domain_hi < region.hi:
            _fail(
                "REGION_OUTSIDE_DOMAIN",
                f"region {region.region_id} is not contained in the domain",
            )
    if regions[0].lo != domain_lo or regions[-1].hi != domain_hi:
        _fail("COVERAGE_GAP", "region endpoints do not cover the domain endpoints")

    for left, right in zip(regions[:-1], regions[1:], strict=True):
        if left.hi < right.lo:
            _fail(
                "COVERAGE_GAP",
                f"gap between regions {left.region_id} and {right.region_id}",
            )


def _check_overlap_contracts(
    regions: list[ParsedRegion],
    overlap_values: object,
) -> None:
    overlaps = _list(overlap_values, "overlaps")
    if len(overlaps) != len(regions) - 1:
        _fail(
            "OVERLAP_COUNT_MISMATCH",
            "overlaps must contain one contract for each adjacent region pair",
        )

    for index, (value, left, right) in enumerate(
        zip(overlaps, regions[:-1], regions[1:], strict=True)
    ):
        context = f"overlaps[{index}]"
        overlap = _object(value, _OVERLAP_FIELDS, context)
        left_id = _identifier(overlap["left_region_id"], f"{context}.left_region_id")
        right_id = _identifier(overlap["right_region_id"], f"{context}.right_region_id")
        if (left_id, right_id) != (left.region_id, right.region_id):
            _fail(
                "OVERLAP_PAIR_MISMATCH",
                f"{context} does not bind the adjacent region pair",
            )
        overlap_lo, overlap_hi = _parse_interval(
            overlap["interval"], f"{context}.interval"
        )
        expected = (max(left.lo, right.lo), min(left.hi, right.hi))
        if (overlap_lo, overlap_hi) != expected:
            _fail(
                "OVERLAP_INTERVAL_MISMATCH",
                f"{context} is not the exact adjacent-region intersection",
            )
        left_contract = _identifier(
            overlap["left_contract_id"], f"{context}.left_contract_id"
        )
        right_contract = _identifier(
            overlap["right_contract_id"], f"{context}.right_contract_id"
        )
        if left_contract != right_contract:
            _fail(
                "OVERLAP_CONTRACT_MISMATCH",
                f"{context} has disagreeing local overlap contracts",
            )


def check_receipt(value: object) -> CheckResult:
    """Check one untrusted receipt and return ``ACCEPT`` or ``UNKNOWN``."""

    try:
        receipt = _object(value, _TOP_FIELDS, "receipt")
        if receipt["schema"] != SCHEMA:
            _fail("SCHEMA_MISMATCH", f"schema must equal {SCHEMA}")
        _identifier(receipt["claim_id"], "claim_id")
        if not isinstance(receipt["coverage_root"], str):
            _fail("COVERAGE_ROOT_MISMATCH", "coverage_root must be a string")
        body = {key: receipt[key] for key in sorted(_BOUND_BODY_FIELDS)}
        expected_root = coverage_root(body)
        if receipt["coverage_root"] != expected_root:
            _fail("COVERAGE_ROOT_MISMATCH", "coverage_root does not bind the receipt body")

        domain_lo, domain_hi = _parse_interval(receipt["domain"], "domain")
        _require_valid_domain(domain_lo, domain_hi)

        region_values = _list(receipt["regions"], "regions")
        if len(region_values) > MAX_REGIONS:
            _fail(
                "RESOURCE_LIMIT_EXCEEDED",
                f"receipt exceeds the {MAX_REGIONS}-region limit",
            )
        regions = [_parse_region(region, index) for index, region in enumerate(region_values)]
        _check_region_cover(domain_lo, domain_hi, regions)
        _check_overlap_contracts(regions, receipt["overlaps"])

        region_details = [
            {
                "region_id": region.region_id,
                "model_margin": ratstr(region.model_margin),
                "total_allocated_error": ratstr(region.total_allocated_error),
                "remaining_margin": ratstr(
                    region.model_margin - region.total_allocated_error
                ),
            }
            for region in regions
        ]
        return CheckResult(
            status="ACCEPT",
            reason_code=None,
            theorem=THEOREM,
            detail={
                "claim_id": receipt["claim_id"],
                "coverage_root": receipt["coverage_root"],
                "evidence_scope": "arithmetic_and_cover_binding_only",
                "external_assumption": (
                    "every opaque certificate_id denotes a valid model or error bound"
                ),
                "regions": region_details,
            },
        )
    except CheckFailure as exc:
        return CheckResult(
            status="UNKNOWN",
            reason_code=exc.reason_code,
            theorem=None,
            detail={"reason": exc.message},
        )


def check_named_receipts(rows: object) -> dict[str, Any]:
    values = _list(rows, "receipts")
    if len(values) > MAX_NAMED_RECEIPTS:
        _fail(
            "RESOURCE_LIMIT_EXCEEDED",
            f"input exceeds the {MAX_NAMED_RECEIPTS}-receipt limit",
        )
    results: list[dict[str, Any]] = []
    for index, value in enumerate(values):
        row = _object(value, {"name", "receipt"}, f"receipts[{index}]")
        name = _identifier(row["name"], f"receipts[{index}].name")
        result = check_receipt(row["receipt"]).to_json()
        results.append({"name": name, **result})
    accepted = sum(row["status"] == "ACCEPT" for row in results)
    return {
        "schema": REPORT_SCHEMA,
        "summary": {
            "accepted": accepted,
            "unknown": len(results) - accepted,
            "total": len(results),
        },
        "results": results,
    }


def _load_named_receipts(path: Path) -> object:
    try:
        if path.stat().st_size > MAX_INPUT_BYTES:
            _fail(
                "RESOURCE_LIMIT_EXCEEDED",
                f"input exceeds the {MAX_INPUT_BYTES}-byte limit",
            )
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, RecursionError, UnicodeError, json.JSONDecodeError) as exc:
        _fail("INPUT_PARSE_ERROR", f"cannot read receipt file: {exc}")
    if isinstance(value, dict) and set(value) == {"receipts"}:
        return value["receipts"]
    return [{"name": "input-receipt", "receipt": value}]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--demo", action="store_true")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    if args.demo == (args.input is not None):
        parser.error("choose exactly one of --demo or an input path")

    try:
        if args.demo:
            from approximation_defect_demo import builtin_demo

            rows = builtin_demo()
        else:
            rows = _load_named_receipts(args.input)
        report = check_named_receipts(rows)
    except CheckFailure as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "summary": {"accepted": 0, "unknown": 1, "total": 1},
            "results": [
                {
                    "name": "input-envelope",
                    "status": "UNKNOWN",
                    "reason_code": exc.reason_code,
                    "theorem": None,
                    "detail": {"reason": exc.message},
                }
            ],
        }

    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
