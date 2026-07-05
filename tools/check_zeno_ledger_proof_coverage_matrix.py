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


def validate_proof_coverage_matrix_v0(matrix: Any, *, claims_registry: Path = CLAIMS_REGISTRY) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(matrix, "matrix", errors)
    if obj.get("schema") != MATRIX_SCHEMA:
        errors.append("schema mismatch")

    claim_status_by_id = _load_claim_status_by_id(claims_registry, errors)
    supported = _list(obj.get("supported_surfaces"), "supported_surfaces", errors)
    gaps = _list(obj.get("gap_surfaces"), "gap_surfaces", errors)
    non_claims = _str_set(obj.get("non_claims"), "non_claims", errors)

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
    if missing_gaps:
        errors.append(f"missing required gap surfaces: {','.join(missing_gaps)}")
    if missing_non_claims:
        errors.append(f"missing required non-claims: {','.join(missing_non_claims)}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "supported_surface_count": len(supported),
        "gap_surface_count": len(gaps),
        "non_claim_count": len(non_claims),
        "supported_surfaces": supported_reports,
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
    items = _list(value, name, errors)
    out: set[str] = set()
    for index, item in enumerate(items):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed is not None:
            out.add(parsed)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
    parser.add_argument("--claims-registry", type=Path, default=CLAIMS_REGISTRY)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    matrix = json.loads(args.matrix.read_text(encoding="utf-8"))
    report = validate_proof_coverage_matrix_v0(matrix, claims_registry=args.claims_registry)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
