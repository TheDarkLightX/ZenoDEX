#!/usr/bin/env python3
"""Validate the public ZenoLedger proof-coverage matrix."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

import yaml

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

MATRIX_SCHEMA = "zenodex.zeno_ledger.proof_coverage_matrix.v0"
REPORT_SCHEMA = "zenodex.zeno_ledger.proof_coverage_matrix_report.v0"
DEFAULT_MATRIX = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"
CLAIMS_REGISTRY = ROOT / "docs" / "claims_registry.yaml"

REQUIRED_SUPPORTED_IDS = frozenset(
    {
        "zk_tee_metadata_composition",
        "risc0_spot_transition_metadata_adapter",
        "risc0_spot_fixture_equivalence",
        "risc0_supported_transition_real_proof_smoke",
        "proof_required_range_replay",
        "proof_verification_report_replay",
        "light_client_checkpoint_quorum",
        "recursive_lifecycle_asset_delta_rows",
        "recursive_lifecycle_admission_packet_checker",
    }
)

REQUIRED_GAP_IDS = frozenset(
    {
        "spot_complete_block_real_proof",
        "uniform_batch_upba_v2_v3_real_proof",
        "oracle_critical_action_real_proof",
        "zusd_lifecycle_real_proof",
        "perps_settlement_real_proof",
        "proof_market_reward_real_proof",
        "light_client_production_finality",
        "recursive_epoch_real_proof",
        "recursive_oracle_leaf_real_proof",
        "recursive_production_admission",
        "zusd_non_deposit_mint_lifecycle_rows",
    }
)

REQUIRED_VALUE_MOVING_SURFACE_IDS = frozenset(
    {
        "spot_v1_complete_block_execution",
        "uniform_batch_upba_execution",
        "oracle_critical_action_execution",
        "zusd_lifecycle_execution",
        "perps_settlement_execution",
        "proof_market_reward_execution",
        "recursive_epoch_and_production_admission",
        "production_light_client_finality_for_value_moving_admission",
    }
)

REQUIRED_NON_CLAIMS = frozenset(
    {
        "does_not_claim_complete_spot_block_zk_proof",
        "does_not_claim_upba_zk_execution",
        "does_not_claim_oracle_truth_or_governance",
        "does_not_claim_zusd_or_perps_zk_execution",
        "does_not_claim_proof_market_zk_execution",
        "does_not_claim_light_client_finality",
        "does_not_claim_recursive_epoch_proof_soundness",
        "does_not_claim_recursive_oracle_leaf_coverage",
        "does_not_claim_recursive_production_admission",
        "does_not_claim_full_zusd_lifecycle_rows",
    }
)

VALUE_MOVING_COVERAGE_STATUSES = frozenset({"covered", "covered_scoped", "open"})


def validate_proof_coverage_matrix_v0(
    matrix: Any,
    *,
    claims_registry: Path = CLAIMS_REGISTRY,
    require_full_zk: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(matrix, "matrix", errors)
    if obj.get("schema") != MATRIX_SCHEMA:
        errors.append("schema mismatch")

    claim_status_by_id = _load_claim_status_by_id(claims_registry, errors)
    supported = _list(obj.get("supported_surfaces"), "supported_surfaces", errors)
    gaps = _list(obj.get("gap_surfaces"), "gap_surfaces", errors)
    non_claims = _str_set(obj.get("non_claims"), "non_claims", errors)
    value_moving = _list(
        obj.get("full_zk_value_moving_surfaces"),
        "full_zk_value_moving_surfaces",
        errors,
    )

    supported_ids: set[str] = set()
    supported_claim_ids: set[str] = set()
    supported_reports: list[dict[str, Any]] = []
    for index, raw in enumerate(supported):
        item_errors: list[str] = []
        item = _mapping(raw, f"supported_surfaces[{index}]", item_errors)
        surface_id = _str(item.get("id"), f"supported_surfaces[{index}].id", item_errors)
        claim_id = _str(item.get("claim_id"), f"supported_surfaces[{index}].claim_id", item_errors)
        _str(item.get("coverage"), f"supported_surfaces[{index}].coverage", item_errors)
        _str(item.get("proof_kind"), f"supported_surfaces[{index}].proof_kind", item_errors)
        if surface_id is not None:
            if surface_id in supported_ids:
                item_errors.append("supported surface id must be unique")
            supported_ids.add(surface_id)
        claim_status = None
        if claim_id is not None:
            if claim_id in supported_claim_ids:
                item_errors.append("supported claim_id must be unique")
            supported_claim_ids.add(claim_id)
            claim_status = claim_status_by_id.get(claim_id)
            if claim_status is None:
                item_errors.append("claim_id missing from claims registry")
            elif claim_status not in {"proved", "supported"}:
                item_errors.append("claim_id must be proved or supported")
        supported_reports.append(
            {
                "id": surface_id,
                "claim_id": claim_id,
                "claim_status": claim_status,
                "ok": not item_errors,
                "errors": item_errors,
            }
        )
        errors.extend(f"supported_surfaces[{index}]: {err}" for err in item_errors)

    gap_ids: set[str] = set()
    for index, raw in enumerate(gaps):
        item_errors: list[str] = []
        item = _mapping(raw, f"gap_surfaces[{index}]", item_errors)
        gap_id = _str(item.get("id"), f"gap_surfaces[{index}].id", item_errors)
        _str(item.get("required_for"), f"gap_surfaces[{index}].required_for", item_errors)
        _str(item.get("gap"), f"gap_surfaces[{index}].gap", item_errors)
        if "claim_id" in item:
            item_errors.append("gap surface must not carry claim_id")
        if gap_id is not None:
            if gap_id in gap_ids:
                item_errors.append("gap surface id must be unique")
            gap_ids.add(gap_id)
        errors.extend(f"gap_surfaces[{index}]: {err}" for err in item_errors)

    missing_supported = sorted(REQUIRED_SUPPORTED_IDS - supported_ids)
    missing_gaps = sorted(REQUIRED_GAP_IDS - gap_ids)
    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - non_claims)
    if missing_supported:
        errors.append(f"missing required supported surfaces: {','.join(missing_supported)}")
    if missing_gaps and not require_full_zk:
        errors.append(f"missing required gap surfaces: {','.join(missing_gaps)}")
    if missing_non_claims and not require_full_zk:
        errors.append(f"missing required non-claims: {','.join(missing_non_claims)}")

    value_moving_report = _validate_value_moving_surfaces(
        value_moving,
        supported_ids=supported_ids,
        gap_ids=gap_ids,
        non_claims=non_claims,
        errors=errors,
        require_required_gap_refs=not require_full_zk,
    )
    if require_full_zk and not value_moving_report["full_zk_execution_ready"]:
        errors.append(
            "full zk execution is not ready; open value-moving surfaces: "
            + ",".join(value_moving_report["succinct_open_value_moving_surfaces"])
        )

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "supported_surface_count": len(supported),
        "gap_surface_count": len(gaps),
        "non_claim_count": len(non_claims),
        "value_moving_surface_count": value_moving_report["value_moving_surface_count"],
        "value_moving_full_zk_ready_count": value_moving_report["value_moving_full_zk_ready_count"],
        "full_zk_execution_ready": value_moving_report["full_zk_execution_ready"],
        "succinct_open_value_moving_surfaces": value_moving_report["succinct_open_value_moving_surfaces"],
        "succinct_open_gap_ids": value_moving_report["succinct_open_gap_ids"],
        "supported_surfaces": supported_reports,
        "full_zk_value_moving_surfaces": value_moving_report["surfaces"],
    }


def _validate_value_moving_surfaces(
    value_moving: list[Any],
    *,
    supported_ids: set[str],
    gap_ids: set[str],
    non_claims: set[str],
    errors: list[str],
    require_required_gap_refs: bool,
) -> dict[str, Any]:
    seen: set[str] = set()
    referenced_gap_ids: set[str] = set()
    open_surface_ids: set[str] = set()
    open_gap_ids: set[str] = set()
    ready_count = 0
    reports: list[dict[str, Any]] = []

    for index, raw in enumerate(value_moving):
        item_errors: list[str] = []
        item = _mapping(raw, f"full_zk_value_moving_surfaces[{index}]", item_errors)
        surface_id = _str(item.get("id"), f"full_zk_value_moving_surfaces[{index}].id", item_errors)
        _str(
            item.get("description"),
            f"full_zk_value_moving_surfaces[{index}].description",
            item_errors,
        )
        coverage_status = _str(
            item.get("coverage_status"),
            f"full_zk_value_moving_surfaces[{index}].coverage_status",
            item_errors,
        )
        proof_surface_ids = _str_list(
            item.get("proof_surface_ids"),
            f"full_zk_value_moving_surfaces[{index}].proof_surface_ids",
            item_errors,
            allow_missing=True,
        )
        gap_surface_ids = _str_list(
            item.get("gap_surface_ids"),
            f"full_zk_value_moving_surfaces[{index}].gap_surface_ids",
            item_errors,
            allow_missing=True,
        )
        required_non_claims = _str_list(
            item.get("required_non_claims"),
            f"full_zk_value_moving_surfaces[{index}].required_non_claims",
            item_errors,
            allow_missing=True,
        )
        external_check_commands = _str_list(
            item.get("external_check_commands"),
            f"full_zk_value_moving_surfaces[{index}].external_check_commands",
            item_errors,
            allow_missing=True,
        )
        limits = _str_list(
            item.get("limits"),
            f"full_zk_value_moving_surfaces[{index}].limits",
            item_errors,
            allow_missing=True,
        )

        if surface_id is not None:
            if surface_id in seen:
                item_errors.append("value-moving surface id must be unique")
            seen.add(surface_id)
        if coverage_status and coverage_status not in VALUE_MOVING_COVERAGE_STATUSES:
            item_errors.append(f"coverage_status has unsupported value: {coverage_status}")
        if _duplicates(proof_surface_ids):
            item_errors.append("proof_surface_ids must be unique")
        if _duplicates(gap_surface_ids):
            item_errors.append("gap_surface_ids must be unique")
        if _duplicates(required_non_claims):
            item_errors.append("required_non_claims must be unique")

        missing_proof_ids = sorted(set(proof_surface_ids) - supported_ids)
        missing_gap_ids = sorted(set(gap_surface_ids) - gap_ids)
        missing_non_claims = sorted(set(required_non_claims) - non_claims)
        if missing_proof_ids:
            item_errors.append("proof_surface_ids missing from supported_surfaces: " + ",".join(missing_proof_ids))
        if missing_gap_ids:
            item_errors.append("gap_surface_ids missing from gap_surfaces: " + ",".join(missing_gap_ids))
        if missing_non_claims:
            item_errors.append("required_non_claims missing from non_claims: " + ",".join(missing_non_claims))

        if coverage_status in {"covered", "covered_scoped"} and not proof_surface_ids:
            item_errors.append("covered value-moving surface needs proof_surface_ids")
        if coverage_status == "open" and proof_surface_ids:
            item_errors.append("open value-moving surface must not carry proof_surface_ids")
        if coverage_status == "covered" and gap_surface_ids:
            item_errors.append("covered value-moving surface must not carry gap_surface_ids")
        if coverage_status == "covered" and required_non_claims:
            item_errors.append("covered value-moving surface must not require non-claims")
        if coverage_status in {"covered_scoped", "open"} and not gap_surface_ids:
            item_errors.append("open or scoped value-moving surface needs gap_surface_ids")
        if coverage_status in {"covered_scoped", "open"} and not required_non_claims:
            item_errors.append("open or scoped value-moving surface needs required_non_claims")
        if not external_check_commands:
            item_errors.append("value-moving surface needs external_check_commands")
        if not limits:
            item_errors.append("value-moving surface needs limits")

        if surface_id and (coverage_status != "covered" or gap_surface_ids or required_non_claims):
            open_surface_ids.add(surface_id)
        if coverage_status == "covered" and not gap_surface_ids and not required_non_claims:
            ready_count += 1
        referenced_gap_ids.update(gap_surface_ids)
        open_gap_ids.update(gap_surface_ids)
        reports.append(
            {
                "id": surface_id,
                "coverage_status": coverage_status,
                "ok": not item_errors,
                "errors": item_errors,
                "proof_surface_ids": proof_surface_ids,
                "gap_surface_ids": gap_surface_ids,
                "required_non_claims": required_non_claims,
            }
        )
        errors.extend(f"full_zk_value_moving_surfaces[{index}]: {err}" for err in item_errors)

    missing_value_moving = sorted(REQUIRED_VALUE_MOVING_SURFACE_IDS - seen)
    missing_gap_refs = sorted(REQUIRED_GAP_IDS - referenced_gap_ids) if require_required_gap_refs else []
    if missing_value_moving:
        errors.append("missing required value-moving surfaces: " + ",".join(missing_value_moving))
    if missing_gap_refs:
        errors.append("value-moving coverage missing required gap refs: " + ",".join(missing_gap_refs))

    return {
        "value_moving_surface_count": len(value_moving),
        "value_moving_full_zk_ready_count": ready_count,
        "full_zk_execution_ready": (
            not open_surface_ids and not open_gap_ids and not missing_value_moving and not missing_gap_refs
        ),
        "succinct_open_value_moving_surfaces": sorted(open_surface_ids),
        "succinct_open_gap_ids": sorted(open_gap_ids),
        "surfaces": reports,
    }


def _load_claim_status_by_id(path: Path, errors: list[str]) -> dict[str, str]:
    try:
        raw = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, yaml.YAMLError) as exc:
        errors.append(f"claims registry load failed: {exc}")
        return {}
    if not isinstance(raw, Mapping):
        errors.append("claims registry must be an object")
        return {}
    claims = raw.get("claims")
    if not isinstance(claims, list):
        errors.append("claims registry claims must be a list")
        return {}
    out: dict[str, str] = {}
    for claim in claims:
        if not isinstance(claim, Mapping):
            continue
        claim_id = claim.get("id")
        status = claim.get("status")
        if isinstance(claim_id, str) and isinstance(status, str):
            out[claim_id] = status
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


def _str_set(value: Any, name: str, errors: list[str]) -> set[str]:
    items = _str_list(value, name, errors)
    return set(items)


def _str_list(value: Any, name: str, errors: list[str], *, allow_missing: bool = False) -> list[str]:
    if value is None and allow_missing:
        return []
    items = _list(value, name, errors)
    parsed_items: list[str] = []
    for index, item in enumerate(items):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed is not None:
            parsed_items.append(parsed)
    return parsed_items


def _duplicates(items: list[str]) -> set[str]:
    seen: set[str] = set()
    duplicates: set[str] = set()
    for item in items:
        if item in seen:
            duplicates.add(item)
        seen.add(item)
    return duplicates


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
    parser.add_argument("--claims-registry", type=Path, default=CLAIMS_REGISTRY)
    parser.add_argument("--require-full-zk", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    matrix = json.loads(args.matrix.read_text(encoding="utf-8"))
    report = validate_proof_coverage_matrix_v0(
        matrix,
        claims_registry=args.claims_registry,
        require_full_zk=args.require_full_zk,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
