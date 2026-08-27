#!/usr/bin/env python3
"""Fail closed on an incomplete or vacuously reduced M6 capability contract."""

from __future__ import annotations

import argparse
import importlib
import json
import sys
from pathlib import Path
from typing import Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

_global_types = importlib.import_module("src.core.global_settlement_types_v1")
LaneIdV1 = _global_types.LaneIdV1
hash_global_v1 = _global_types.hash_global_v1
_capability_binding = importlib.import_module(
    "src.core.global_economic_capability_profile_binding_v1"
)
M6_CAPABILITY_MANIFEST_ROOT_V1 = _capability_binding.M6_CAPABILITY_MANIFEST_ROOT_V1

DEFAULT_MANIFEST = Path("docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json")
SCHEMA = "zenodex/m6-capability-manifest/v1"
REQUIRED_DISPOSITION = "REQUIRED_UNRESOLVED"
EXTERNAL_DISPOSITION = "DISABLED_PENDING_COMPLETE_PROFILE"
EXPECTED_CROSS_LANE_ROUTES = (
    "fee_funded_zdex_purchase_and_burn",
    "zusd_liquidation_settlement",
    "perps_epoch_settlement",
    "strategy_triggered_spot_swap",
)
EXPECTED_EXCLUSIONS = {
    "autonomous_governance_publication_authority": (
        "FORBIDDEN_COMMAND_SUBMISSION_ONLY"
    ),
    "caller_selected_route_or_proof_profile": "FORBIDDEN_GOVERNED_SELECTION_ONLY",
    "unregistered_external_destination": "REJECT_WITHOUT_MUTATION",
    "zusd_emergency_shutdown": "EXCLUDED_DAY_ONE_PROVE_NO_WRITER",
}
MANDATORY_CAPABILITIES = {
    "ASSET_TRANSFER": {"managed_issue", "managed_burn", "tau_originated_asset_registration"},
    "SPOT_LIQUIDITY": {"exact_in_swap", "exact_out_swap", "pool_close"},
    "FARM_INCENTIVES": {"lp_stake", "emission_claim", "farm_terminal_drain"},
    "ZDEX_TOKENOMICS": {
        "host_compensation_claim",
        "atomic_purchase_and_burn",
        "retained_supply_hyperdeflation",
    },
    "ZUSD_MONETARY": {"vault_owner_close", "multi_vault_redemption", "recovery_mode"},
    "PERPS_MARKET": {"funding_accrual", "auto_deleveraging", "bankruptcy_resolution"},
    "ORACLE_MARKET": {"reporter_bond", "report_dispute", "reporter_slash"},
    "SEALED_AUCTION": {"bid_commitment", "deterministic_clearing", "auction_expiry"},
    "STRATEGY_ESCROW": {"value_reservation", "strategy_trigger", "strategy_recovery"},
    "PROOF_REWARDS": {"verified_result_binding", "claim_nullifier", "task_terminal_state"},
    "EXTERNAL_CUSTODY": {"external_finality", "external_refund", "destination_idempotency"},
    "GOVERNANCE_MIGRATION": {
        "release_activation",
        "writer_epoch_rotation",
        "autonomous_governance_command_submission",
    },
}


def _without_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_m6_capability_manifest_v1(path: Path) -> Mapping[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_without_duplicate_keys,
    )
    if type(value) is not dict:
        raise TypeError("M6 capability manifest root must be an object")
    return value


def check_m6_capability_manifest_v1(
    root: Path = REPO_ROOT,
    manifest_path: Path | None = None,
) -> dict[str, object]:
    findings: list[str] = []
    source = manifest_path or root / DEFAULT_MANIFEST
    try:
        manifest = load_m6_capability_manifest_v1(source)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        return {
            "schema": "zenodex/m6-capability-manifest-check/v1",
            "ok": False,
            "production_authority": "NONE",
            "findings": [f"manifest cannot be loaded: {type(exc).__name__}: {exc}"],
        }

    if manifest.get("schema") != SCHEMA:
        findings.append("M6 capability schema mismatch")
    for field in ("production_promotion", "manifest_complete", "release_eligible"):
        if manifest.get(field) is not False:
            findings.append(f"{field} must remain false while capabilities are unresolved")

    lanes = manifest.get("lanes")
    expected_lane_ids = tuple(lane.value for lane in LaneIdV1)
    observed_lane_ids: tuple[object, ...] = ()
    open_capability_count = 0
    if type(lanes) is not list or any(type(lane) is not dict for lane in lanes):
        findings.append("lanes must be a list of objects")
    else:
        observed_lane_ids = tuple(lane.get("lane_id") for lane in lanes)
        if observed_lane_ids != expected_lane_ids:
            findings.append("lane IDs must exactly match GlobalSettlementABI V1 order")
        for lane in lanes:
            lane_id = lane.get("lane_id")
            expected_disposition = (
                EXTERNAL_DISPOSITION
                if lane_id == "EXTERNAL_CUSTODY"
                else REQUIRED_DISPOSITION
            )
            if lane.get("disposition") != expected_disposition:
                findings.append(f"lane disposition drift: {lane_id}")
            capabilities = lane.get("capabilities")
            if (
                type(capabilities) is not list
                or not capabilities
                or any(type(capability) is not str for capability in capabilities)
                or len(capabilities) != len(set(capabilities))
            ):
                findings.append(f"lane capabilities invalid: {lane_id}")
                continue
            missing = sorted(MANDATORY_CAPABILITIES.get(str(lane_id), set()) - set(capabilities))
            if missing:
                findings.append(f"mandatory capabilities missing for {lane_id}: {missing}")
            open_capability_count += len(capabilities)

    routes = manifest.get("required_cross_lane_routes")
    if routes != list(EXPECTED_CROSS_LANE_ROUTES):
        findings.append("required cross-lane routes are incomplete or unordered")

    exclusions = manifest.get("explicit_exclusions")
    if type(exclusions) is not list or any(type(row) is not dict for row in exclusions):
        findings.append("explicit exclusions must be a list of objects")
    else:
        observed_exclusions = {
            row.get("capability"): row.get("disposition") for row in exclusions
        }
        if observed_exclusions != EXPECTED_EXCLUSIONS:
            findings.append("explicit exclusion semantics drift")

    history = manifest.get("historical_requirements")
    expected_history = {
        "workflow_count": 18,
        "scenario_count": 81,
        "required_spec_expansion_count": 11,
        "status": "REQUIRED_BUT_NOT_CAPABILITY_COMPLETE",
    }
    if history != expected_history:
        findings.append("historical requirement counts or claim ceiling drift")

    manifest_root = hash_global_v1("m6-capability-manifest-v1", manifest)
    if manifest_root != M6_CAPABILITY_MANIFEST_ROOT_V1:
        findings.append("exact M6 capability manifest root drift")

    return {
        "schema": "zenodex/m6-capability-manifest-check/v1",
        "ok": not findings,
        "lane_count": len(lanes) if type(lanes) is list else 0,
        "open_capability_count": open_capability_count,
        "manifest_root": manifest_root,
        "manifest_complete": False,
        "release_eligible": False,
        "production_authority": "NONE",
        "findings": findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args(argv)
    report = check_m6_capability_manifest_v1(args.root, args.manifest)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
