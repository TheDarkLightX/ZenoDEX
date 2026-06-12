#!/usr/bin/env python3
"""Validate the ZenoDEX trust-minimization target artifact."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zeno_ledger_proof_coverage_matrix import (  # noqa: E402
    DEFAULT_MATRIX,
    validate_proof_coverage_matrix_v0,
)

TARGET_SCHEMA = "zenodex.trust_minimization_target.v0"
REPORT_SCHEMA = "zenodex.trust_minimization_target_report.v0"
DEFAULT_TARGET = ROOT / "docs" / "ZENODEX_TRUST_MINIMIZATION_TARGET_V0.json"

OPEN_STATUSES = {"open_gap", "blocked", "replay_supported_with_gap"}
SUPPORTED_STATUSES = {"zk_supported_scoped", "replay_supported", "replay_supported_with_gap"}
SURFACE_STATUSES = OPEN_STATUSES | SUPPORTED_STATUSES

REQUIRED_ACCEPTANCE_RULES = frozenset(
    {
        "deterministic_replay_or_valid_zk_receipt",
        "allowed_guest_image_or_replay_profile",
        "journal_binds_pre_state_post_state_and_tx_commitment",
        "proof_metadata_and_verification_report_replay",
        "unsupported_surfaces_fail_closed",
    }
)

REQUIRED_NON_CLAIMS = frozenset(
    {
        "does_not_claim_lower_than_uniswap_trust_until_required_surfaces_closed",
        "does_not_claim_host_independence_for_uncovered_surfaces",
        "does_not_claim_docker_is_a_correctness_boundary",
    }
)


def validate_trust_minimization_target_v0(
    target: Any,
    *,
    matrix: Any | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(target, "target", errors)
    if obj.get("schema") != TARGET_SCHEMA:
        errors.append("schema mismatch")

    matrix_obj = _load_default_matrix(errors) if matrix is None else matrix
    matrix_report = validate_proof_coverage_matrix_v0(matrix_obj)
    if not matrix_report.get("ok"):
        errors.append("proof coverage matrix rejected")
        errors.extend(f"matrix:{err}" for err in matrix_report.get("errors", []))

    supported_ids = _surface_ids(matrix_obj, "supported_surfaces")
    gap_ids = _surface_ids(matrix_obj, "gap_surfaces")
    matrix_non_claims = set(
        _str_list(
            _mapping(matrix_obj, "matrix", errors).get("non_claims"),
            "matrix.non_claims",
            [],
        )
    )

    target_id = _str(obj.get("target_id"), "target_id", errors)
    target_status = _str(obj.get("target_status"), "target_status", errors)
    if target_status not in {"frontier_open", "achieved"}:
        errors.append("target_status must be frontier_open or achieved")
    lower_than_uniswap_claim = obj.get("lower_than_uniswap_claim")
    if not isinstance(lower_than_uniswap_claim, bool):
        errors.append("lower_than_uniswap_claim must be bool")

    baseline = _mapping(obj.get("baseline"), "baseline", errors)
    if baseline.get("baseline_id") != "ethereum_uniswap_style_smart_contract":
        errors.append("baseline.baseline_id mismatch")
    _str(baseline.get("comparison_scope"), "baseline.comparison_scope", errors)
    _str(baseline.get("baseline_summary"), "baseline.baseline_summary", errors)

    adversary = _mapping(obj.get("host_adversary_model"), "host_adversary_model", errors)
    for key in (
        "host_is_adversary",
        "host_may_lie_about_execution",
        "host_may_omit_data",
        "host_may_emit_malformed_metadata",
    ):
        if adversary.get(key) is not True:
            errors.append(f"host_adversary_model.{key} must be true")
    if adversary.get("docker_is_correctness_boundary") is not False:
        errors.append("host_adversary_model.docker_is_correctness_boundary must be false")
    _str(adversary.get("required_response"), "host_adversary_model.required_response", errors)

    acceptance_rules = set(_str_list(obj.get("acceptance_rule"), "acceptance_rule", errors))
    missing_rules = sorted(REQUIRED_ACCEPTANCE_RULES - acceptance_rules)
    if missing_rules:
        errors.append(f"missing required acceptance rules: {','.join(missing_rules)}")

    non_claims = set(_str_list(obj.get("non_claims"), "non_claims", errors))
    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - non_claims)
    if missing_non_claims:
        errors.append(f"missing required non-claims: {','.join(missing_non_claims)}")

    required_surfaces = _list(obj.get("required_surfaces"), "required_surfaces", errors)
    seen_surface_ids: set[str] = set()
    open_surface_ids: list[str] = []
    supported_surface_count = 0
    for index, raw in enumerate(required_surfaces):
        item_errors: list[str] = []
        item = _mapping(raw, f"required_surfaces[{index}]", item_errors)
        surface_id = _str(item.get("id"), f"required_surfaces[{index}].id", item_errors)
        status = _str(item.get("current_status"), f"required_surfaces[{index}].current_status", item_errors)
        if surface_id is not None:
            if surface_id in seen_surface_ids:
                item_errors.append("id must be unique")
            seen_surface_ids.add(surface_id)
        if status not in SURFACE_STATUSES:
            item_errors.append("current_status is unsupported")
        if status in OPEN_STATUSES and surface_id is not None:
            open_surface_ids.append(surface_id)

        supported_surface_id = item.get("supported_surface_id")
        if status in SUPPORTED_STATUSES:
            parsed_supported = _str(
                supported_surface_id,
                f"required_surfaces[{index}].supported_surface_id",
                item_errors,
            )
            if parsed_supported is not None and parsed_supported not in supported_ids:
                item_errors.append(f"supported_surface_id unknown:{parsed_supported}")
            elif parsed_supported is not None:
                supported_surface_count += 1

        gap_surface_id = item.get("gap_surface_id")
        if status in OPEN_STATUSES:
            parsed_gap = _str(gap_surface_id, f"required_surfaces[{index}].gap_surface_id", item_errors)
            if parsed_gap is not None and parsed_gap not in gap_ids:
                item_errors.append(f"gap_surface_id unknown:{parsed_gap}")
        elif gap_surface_id is not None:
            item_errors.append("closed surface must not carry gap_surface_id")

        non_claim = item.get("non_claim")
        if status in {"open_gap", "blocked"}:
            parsed_non_claim = _str(non_claim, f"required_surfaces[{index}].non_claim", item_errors)
            if parsed_non_claim is not None:
                if parsed_non_claim not in non_claims:
                    item_errors.append(f"non_claim missing from target non_claims:{parsed_non_claim}")
                if parsed_non_claim not in matrix_non_claims:
                    item_errors.append(f"non_claim missing from proof matrix:{parsed_non_claim}")

        errors.extend(f"required_surfaces[{index}]: {err}" for err in item_errors)

    if not required_surfaces:
        errors.append("required_surfaces must be non-empty")
    if supported_surface_count == 0:
        errors.append("at least one supported surface is required")

    promotion_gates = _str_list(obj.get("promotion_gates"), "promotion_gates", errors)
    if len(promotion_gates) < 4:
        errors.append("promotion_gates must contain at least four gates")
    if not any("unsupported" in gate.lower() and "fail" in gate.lower() for gate in promotion_gates):
        errors.append("promotion_gates must include unsupported-surface fail-closed gate")
    if not any("verifier" in gate.lower() and "guest image" in gate.lower() for gate in promotion_gates):
        errors.append("promotion_gates must include verifier and guest-image admission gate")

    if target_status == "achieved":
        if lower_than_uniswap_claim is not True:
            errors.append("achieved target must set lower_than_uniswap_claim=true")
        if open_surface_ids:
            errors.append(f"achieved target cannot have open surfaces: {','.join(sorted(open_surface_ids))}")
    elif target_status == "frontier_open":
        if lower_than_uniswap_claim is not False:
            errors.append("frontier_open target must set lower_than_uniswap_claim=false")
        if "does_not_claim_lower_than_uniswap_trust_until_required_surfaces_closed" not in non_claims:
            errors.append("frontier_open target must include lower-than-Uniswap non-claim")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "target_id": target_id,
        "target_status": target_status,
        "lower_than_uniswap_claim": lower_than_uniswap_claim,
        "open_surface_count": len(open_surface_ids),
        "open_surfaces": sorted(open_surface_ids),
        "supported_surface_count": supported_surface_count,
        "errors": errors,
    }


def _load_default_matrix(errors: list[str]) -> Any:
    try:
        return json.loads(DEFAULT_MATRIX.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"proof coverage matrix load failed: {exc}")
        return {}


def _surface_ids(matrix: Any, key: str) -> set[str]:
    if not isinstance(matrix, Mapping):
        return set()
    values = matrix.get(key)
    if not isinstance(values, list):
        return set()
    out: set[str] = set()
    for item in values:
        if isinstance(item, Mapping) and isinstance(item.get("id"), str):
            out.add(str(item["id"]))
    return out


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    items = _list(value, name, errors)
    out: list[str] = []
    for index, item in enumerate(items):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed is not None:
            out.append(parsed)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", type=Path, default=DEFAULT_TARGET)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    target = json.loads(args.target.read_text(encoding="utf-8"))
    matrix = json.loads(args.matrix.read_text(encoding="utf-8"))
    report = validate_trust_minimization_target_v0(target, matrix=matrix)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
