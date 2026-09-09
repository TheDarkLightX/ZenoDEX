#!/usr/bin/env python3
"""Recompute a frozen, advisory-only ZenoDEX V3 progress assessment.

The tool validates the pinned denominator and row layout, then recomputes
consistency scores. It does not read the assessed repository, execute source,
follow evidence paths, or grant a completion, release, or value-movement authority.

Usage: python3 tools/v3_progress_assessment_calc.py assessment.json
"""

from __future__ import annotations

import hashlib
import json
import math
import sys
from pathlib import Path
from typing import NoReturn, cast

DENOMINATORS_SHA256 = "f7aff34725465a1c8d5cef7aabb950610b8324c0f6aa5090d79a353d150f46d0"
ASSESSMENT_SCHEMA = "zenodex/v3-progress-independent-assessment/v1"
ADVISORY = (
    "Judgment/coverage estimate only; grants no completion, release or value-movement authority."
)
BANDS = {"V": (0.05, 0.05), "H": (0.10, 0.08), "U": (None, 0.15)}
FORMAL_WEIGHTS = (0.3, 0.4, 0.3)
BASELINE, DISABLED_CAP, DOCS_ONLY_CAP = 0.03, 0.15, 0.20
ROW_SCORE_TOLERANCE = 0.00005
PERCENT_TOLERANCE = 0.05
VERIFIED = "VERIFIED_SOURCE_INSPECTION"
UNVERIFIED = {"HISTORICAL_RECORDED", "UNKNOWN", "MISSING", "ABSENT", "STALE"}
EVIDENCE_CLASSES = UNVERIFIED | {VERIFIED}
WORKSTREAMS = tuple(f"W{number:02d}" for number in range(14))
LANES = tuple(
    """ASSET_TRANSFER SPOT_LIQUIDITY FARM_INCENTIVES ZDEX_TOKENOMICS ZUSD_MONETARY
    PERPS_MARKET ORACLE_MARKET SEALED_AUCTION STRATEGY_ESCROW PROOF_REWARDS
    EXTERNAL_CUSTODY GOVERNANCE_MIGRATION""".split()
)
ROUTES = tuple(
    """fee_funded_zdex_purchase_and_burn zusd_liquidation_settlement
    perps_epoch_settlement strategy_triggered_spot_swap""".split()
)
EXCLUSIONS = tuple(
    """zusd_emergency_shutdown unregistered_external_destination
    autonomous_governance_publication_authority caller_selected_route_or_proof_profile""".split()
)
FORMAL_CROSS = (
    ("F-INIT", 6.0),
    ("F-GLOBAL", 6.0),
    ("F-ALLOC", 4.0),
    ("F-REFINE", 6.0),
    ("F-TOOLS", 3.0),
)
AUTHORITY_BOOL_FIELDS = (
    "formal_core_complete",
    "whole_value_movement_safe",
    "production_promotion",
    "whole_product_complete",
    "release_ready",
)
AUTHORITY_FIELDS = frozenset((*AUTHORITY_BOOL_FIELDS, "closed_value_movement_gate_count"))


def _reject(code: str) -> NoReturn:
    raise ValueError(code)


def _mapping(value: object, code: str) -> dict[str, object]:
    if type(value) is not dict:
        _reject(code)
    return cast(dict[str, object], value)


def _items(value: object, code: str) -> list[object]:
    if type(value) is not list:
        _reject(code)
    return cast(list[object], value)


def _text(value: object, code: str) -> str:
    if type(value) is not str or not value:
        _reject(code)
    return value


def _number(value: object, code: str) -> float:
    if type(value) not in (int, float):
        _reject(code)
    try:
        number = float(cast(int | float, value))
    except OverflowError:
        _reject(code)
    if not math.isfinite(number):
        _reject(code)
    return number


def _fraction(value: object, code: str) -> float:
    number = _number(value, code)
    if not 0.0 <= number <= 1.0:
        _reject(code)
    return number


def _positive(value: object, code: str) -> float:
    number = _number(value, code)
    if number <= 0.0:
        _reject(code)
    return number


def _flag(mapping: dict[str, object], key: str, code: str) -> bool:
    if key not in mapping:
        return False
    if type(mapping[key]) is not bool:
        _reject(code)
    return cast(bool, mapping[key])


def _pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            _reject("DUPLICATE_JSON_KEY")
        result[key] = value
    return result


def _finite(value: object) -> None:
    if type(value) is float and not math.isfinite(value):
        _reject("NONFINITE_JSON")
    if type(value) is dict:
        for item in value.values():
            _finite(item)
    elif type(value) is list:
        for item in value:
            _finite(item)


def load_assessment(path: Path) -> dict[str, object]:
    """Load one JSON document while rejecting duplicate and nonfinite values."""
    try:
        text = path.read_bytes().decode("utf-8")
    except OSError:
        _reject("INPUT_READ")
    except UnicodeDecodeError:
        _reject("MALFORMED_JSON")
    try:
        value = json.loads(
            text, object_pairs_hook=_pairs, parse_constant=lambda _: _reject("NONFINITE_JSON")
        )
    except (json.JSONDecodeError, RecursionError):
        _reject("MALFORMED_JSON")
    try:
        _finite(value)
    except RecursionError:
        _reject("MALFORMED_JSON")
    return _mapping(value, "TOP_LEVEL")


def _layouts(
    denominators: dict[str, object],
) -> tuple[
    dict[str, tuple[str, ...]],
    list[tuple[str, str, float]],
    list[tuple[str, str, float]],
    float,
    float,
]:
    # A matching hash fixes every denominator value, order, and type below.
    registry_raw = cast(dict[str, list[str]], denominators["capability_registry"])
    registry = {lane: tuple(registry_raw[lane]) for lane in LANES}
    full = cast(dict[str, object], denominators["full_v3"])
    weights = cast(dict[str, float], full["workstream_weights"])
    full_layout = [
        (workstream, "workstream", weights[workstream]) for workstream in WORKSTREAMS[:7]
    ]
    full_layout += [
        (
            f"W07:{lane}",
            "lane",
            round(weights["W07"] * len(registry[lane]) / 103.0, 4),
        )
        for lane in LANES
    ]
    full_layout += [(f"W08:{route}", "route", weights["W08"] / len(ROUTES)) for route in ROUTES]
    full_layout += [
        (workstream, "workstream", weights[workstream]) for workstream in WORKSTREAMS[9:]
    ]
    full_layout += [
        (f"EXCL:{item}", "exclusion", weights["EXCLUSIONS"] / len(EXCLUSIONS))
        for item in EXCLUSIONS
    ]
    formal = cast(dict[str, float], denominators["formal_core"])
    formal_layout = [(f"FC:{lane}", "lane", float(len(registry[lane]))) for lane in LANES]
    formal_layout += [
        (f"FC:ROUTE:{route}", "route", formal["route_units"] / len(ROUTES)) for route in ROUTES
    ]
    formal_layout += [(identifier, "cross", weight) for identifier, weight in FORMAL_CROSS]
    return (
        registry,
        full_layout,
        formal_layout,
        cast(float, full["weight_points"]),
        formal["weight_units"],
    )


def _validate_layout(
    rows: list[object], expected: list[tuple[str, str, float]]
) -> list[dict[str, object]]:
    if len(rows) != len(expected):
        _reject("ROW_LAYOUT")
    checked = []
    for raw_row, (identifier, kind, weight) in zip(rows, expected, strict=True):
        row = _mapping(raw_row, "ROW_SHAPE")
        if (
            _text(row.get("id"), "ROW_SHAPE") != identifier
            or _text(row.get("kind"), "ROW_SHAPE") != kind
        ):
            _reject("ROW_LAYOUT")
        actual_weight = _positive(row.get("weight"), "NUMERIC")
        if actual_weight != weight:
            _reject("ROW_WEIGHT")
        checked.append(row)
    return checked


def _row_scores(row: dict[str, object]) -> tuple[float, float, float, bool]:
    if any(field not in row for field in ("low", "central", "high", "evidence")):
        _reject("ROW_SHAPE")
    low, central, high = (_fraction(row[field], "NUMERIC") for field in ("low", "central", "high"))
    if not low <= central <= high:
        _reject("ROW_ORDER")
    evidence = _items(row["evidence"], "EVIDENCE_SHAPE")
    if not evidence:
        _reject("EVIDENCE_SHAPE")
    verified_code, unverified = False, True
    for raw_item in evidence:
        item = _mapping(raw_item, "EVIDENCE_SHAPE")
        path, evidence_class = (
            _text(item.get("path"), "EVIDENCE_SHAPE"),
            _text(item.get("class"), "EVIDENCE_SHAPE"),
        )
        if evidence_class not in EVIDENCE_CLASSES:
            _reject("EVIDENCE_CLASS")
        verified_code |= evidence_class == VERIFIED and not path.startswith("docs/")
        unverified &= evidence_class in UNVERIFIED
    if (
        central > DOCS_ONLY_CAP
        and not verified_code
        and not _flag(row, "docs_only_allowed", "ROW_SHAPE")
    ):
        _reject("DOCS_ONLY_CAP")
    if central >= 0.95 and not _flag(row, "external_review_accepted", "ROW_SHAPE"):
        _reject("REVIEW_CAP")
    return low, central, high, unverified


def _lane_scores(
    row: dict[str, object], expected: tuple[str, ...], formal: bool
) -> tuple[float, float, float, float]:
    capabilities = _items(row.get("capabilities"), "CAPABILITY_SHAPE")
    if len(capabilities) != len(expected):
        _reject("CAPABILITY_IDS")
    lows, centrals, highs, legacy, identifiers = [], [], [], [], []
    for raw_capability in capabilities:
        capability = _mapping(raw_capability, "CAPABILITY_SHAPE")
        identifiers.append(_text(capability.get("id"), "CAPABILITY_SHAPE"))
        uncertainty = _text(capability.get("unc"), "UNCERTAINTY")
        if uncertainty not in BANDS:
            _reject("UNCERTAINTY")
        central = (
            sum(
                weight * _fraction(capability.get(field), "NUMERIC")
                for weight, field in zip(FORMAL_WEIGHTS, ("sem", "prf", "ref"), strict=True)
            )
            if formal
            else _fraction(capability.get("c"), "NUMERIC")
        )
        if _flag(capability, "disabled_or_blocked", "CAPABILITY_SHAPE") and central > DISABLED_CAP:
            _reject("DISABLED_CAP")
        low_delta, high_delta = BANDS[uncertainty]
        lows.append(max(0.0, central / 2.0 if low_delta is None else central - low_delta))
        centrals.append(central)
        highs.append(min(1.0, central + high_delta))
        legacy.append(BASELINE if _flag(capability, "legacy_only", "CAPABILITY_SHAPE") else central)
    if tuple(identifiers) != expected:
        _reject("CAPABILITY_IDS")
    count = len(capabilities)
    return tuple(sum(values) / count for values in (lows, centrals, highs, legacy))  # type: ignore[return-value]


def _section(
    section: dict[str, object],
    layout: list[tuple[str, str, float]],
    registry: dict[str, tuple[str, ...]],
    formal: bool,
    denominator: float,
) -> dict[str, object]:
    if any(
        field not in section
        for field in (
            "rows",
            "lower_percent",
            "central_percent",
            "upper_percent",
            "denominator_weight",
        )
    ):
        _reject("SECTION_SHAPE")
    if _positive(section["denominator_weight"], "NUMERIC") != denominator:
        _reject("SECTION_WEIGHT")
    rows = _validate_layout(_items(section["rows"], "SECTION_SHAPE"), layout)
    totals = {label: 0.0 for label in ("low", "central", "high", "unknown_as_low", "legacy_zero")}
    kinds: dict[str, int] = {}
    unverified_weight = 0.0
    for row, (identifier, kind, _) in zip(rows, layout, strict=True):
        low, central, high, unverified = _row_scores(row)
        legacy_central = central
        if kind == "lane":
            derived = _lane_scores(row, registry[identifier.split(":")[-1]], formal)
            if any(
                abs(stated - value) > ROW_SCORE_TOLERANCE
                for stated, value in zip((low, central, high), derived[:3], strict=True)
            ):
                _reject("LANE_SCORE")
            legacy_central = derived[3]
        weight = _positive(row["weight"], "NUMERIC")
        kinds[kind] = kinds.get(kind, 0) + 1
        for label, score in (
            ("low", low),
            ("central", central),
            ("high", high),
            ("legacy_zero", legacy_central),
        ):
            totals[label] += weight * score
        totals["unknown_as_low"] += weight * (low if unverified else central)
        unverified_weight += weight if unverified else 0.0
    total_weight = sum(_positive(row["weight"], "NUMERIC") for row in rows)
    result: dict[str, object] = {
        "total_weight": total_weight,
        "row_count": len(rows),
        "kinds": kinds,
    }
    for label, value in totals.items():
        result[f"{label}_percent"] = round(100.0 * value / total_weight, 3)
    result["unverified_only_weight_share_percent"] = round(
        100.0 * unverified_weight / total_weight, 3
    )
    for stated, computed in (
        ("lower_percent", "low_percent"),
        ("central_percent", "central_percent"),
        ("upper_percent", "high_percent"),
    ):
        if (
            abs(_number(section[stated], "NUMERIC") - _number(result[computed], "NUMERIC"))
            > PERCENT_TOLERANCE
        ):
            _reject("SECTION_SCORE")
    return result


def _authority(data: dict[str, object]) -> dict[str, object]:
    authority = _mapping(data.get("release_authority"), "AUTHORITY_SHAPE")
    if set(authority) != AUTHORITY_FIELDS:
        _reject("AUTHORITY_SHAPE")
    if any(authority[field] is not False for field in AUTHORITY_BOOL_FIELDS):
        _reject("AUTHORITY_VALUE")
    if (
        type(authority["closed_value_movement_gate_count"]) is not int
        or authority["closed_value_movement_gate_count"] != 0
    ):
        _reject("AUTHORITY_VALUE")
    return authority


def assess(data: object) -> dict[str, object]:
    """Return a consistency report; named evidence remains unverified advisory input."""
    data = _mapping(data, "TOP_LEVEL")
    if data.get("schema") != ASSESSMENT_SCHEMA or data.get("advisory_only") is not True:
        _reject("ASSESSMENT_SCHEMA")
    method = _mapping(data.get("method"), "METHOD_SHAPE")
    denominators = _mapping(method.get("denominators"), "METHOD_SHAPE")
    if (
        hashlib.sha256(
            json.dumps(
                denominators,
                allow_nan=False,
                ensure_ascii=True,
                separators=(",", ":"),
                sort_keys=True,
            ).encode("ascii")
        ).hexdigest()
        != DENOMINATORS_SHA256
    ):
        _reject("METHOD_DRIFT")
    registry, full_layout, formal_layout, full_weight, formal_weight = _layouts(denominators)
    full, formal = (
        _mapping(data.get("full_v3"), "SECTION_SHAPE"),
        _mapping(data.get("formal_core"), "SECTION_SHAPE"),
    )
    if (
        tuple(
            _text(value, "WORKSTREAM_COVERAGE")
            for value in _items(full.get("covers_workstreams"), "WORKSTREAM_COVERAGE")
        )
        != WORKSTREAMS
    ):
        _reject("WORKSTREAM_COVERAGE")
    return {
        "advisory": ADVISORY,
        "findings": [],
        "ok": True,
        "release_authority": _authority(data),
        "sections": {
            "full_v3": _section(full, full_layout, registry, False, full_weight),
            "formal_core": _section(formal, formal_layout, registry, True, formal_weight),
        },
        "subject": _text(data.get("subject"), "ASSESSMENT_SHAPE"),
    }


def _emit(value: dict[str, object]) -> None:
    print(json.dumps(value, indent=2, sort_keys=True, allow_nan=False))


def main(argv: list[str] | None = None) -> int:
    """Write one deterministic JSON report and return nonzero for every rejection."""
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 1:
        _emit({"advisory": ADVISORY, "findings": [{"code": "USAGE"}], "ok": False})
        return 2
    try:
        report = assess(load_assessment(Path(arguments[0])))
    except ValueError as error:
        _emit({"advisory": ADVISORY, "findings": [{"code": str(error)}], "ok": False})
        return 2
    _emit(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
