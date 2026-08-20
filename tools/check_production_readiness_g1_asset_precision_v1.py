#!/usr/bin/env python3
"""Build and check the selected G1 asset-precision research decision.

This record supersedes the E18 denomination fields in the historical partial
policy while retaining its whole-token modeling envelope and open launch gates.
It grants no issue, burn, settlement, migration, governance, or writer authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from collections.abc import Mapping
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_ASSET_PRECISION_V1.json"
SCHEMA = "zenodex/production-readiness-g1-asset-precision/v1"
PREDECESSOR_PATH = "docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json"
RUST_KERNEL_PATH = "zk/global_settlement_abi_v1/src/asset_precision.rs"
RUST_EXPORT_PATH = "zk/global_settlement_abi_v1/src/lib.rs"
RUST_TEST_PATH = "zk/global_settlement_abi_v1/tests/asset_precision.rs"
CHECKER_PATH = "tools/check_production_readiness_g1_asset_precision_v1.py"
CHECKER_TEST_PATH = "tests/test_check_production_readiness_g1_asset_precision_v1.py"

TARGET_DECIMALS = 8
CURRENT_TAU_TESTNET_DECIMALS = 4
MAX_REGISTERED_DECIMALS = 18
CURRENT_TAU_TESTNET_AMOUNT_BITS = 24
TARGET_TAU_AMOUNT_BITS = 64
WHOLE_ZDEX_SUPPLY = 2_000_000_000
LAUNCH_ACTIVE_FLOOR_WHOLE = 200_000_000
UNIT_SCALE = 10**TARGET_DECIMALS
MAX_SETTLEMENT_DELTA_ATOMS = (1 << 127) - 1

HISTORICAL_E18_DEPENDENTS = (
    "docs/research/PRODUCTION_READINESS_G1_BUYBURN_AUCTION_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_CLBF_MODEL_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json",
    "docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json",
    "docs/research/ZDEX_VOLUME_HOLDING_HYPERDEFLATION_MECHANISM_REPORT_V1.md",
    "tools/check_production_readiness_g1_buyburn_auction_v1.py",
    "tools/production_readiness_g1_buyburn_auction_contract_v1.py",
    "tools/production_readiness_g1_clbf_contract_v1.py",
    "tools/production_readiness_g1_service_funding_contract_v1.py",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    with path.open(encoding="utf-8") as stream:
        result = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(result, dict):
        raise ValueError("asset-precision artifact root must be an object")
    return result


def _source_pin(repo_root: Path, relative_path: str) -> dict[str, str]:
    path = repo_root / relative_path
    return {"path": relative_path, "sha256": _sha256(path)}


def _asset_profiles() -> list[dict[str, Any]]:
    return [
        {
            "asset_class": "TAU_ORIGINATED_TOKEN",
            "asset_id": "TAU",
            "current_testnet_adapter": {
                "amount_width_bits": CURRENT_TAU_TESTNET_AMOUNT_BITS,
                "source_decimals": CURRENT_TAU_TESTNET_DECIMALS,
                "ledger_decimals": TARGET_DECIMALS,
                "conversion": "EXACT_MULTIPLY_ON_ENTRY_EXACT_DIVIDE_OR_REJECT_ON_EXIT",
                "status": "TESTNET_COMPATIBILITY_PROFILE_ONLY",
            },
            "target_profile": {
                "amount_width_bits": TARGET_TAU_AMOUNT_BITS,
                "source_decimals": TARGET_DECIMALS,
                "ledger_decimals": TARGET_DECIMALS,
                "status": "CONDITIONAL_ON_TAU_BV64_PROFILE_AND_REPLAY_EVIDENCE",
            },
        },
        {
            "asset_class": "ZDEX_PROTOCOL_TOKEN",
            "asset_id": "ZDEX",
            "ledger_decimals": TARGET_DECIMALS,
            "tau_amount_width_bits": TARGET_TAU_AMOUNT_BITS,
            "status": "SELECTED_FOR_G1_SPECIFICATION_ONLY",
        },
        {
            "asset_class": "CANONICAL_ZUSD",
            "asset_id": "zUSD",
            "ledger_decimals": TARGET_DECIMALS,
            "tau_amount_width_bits": TARGET_TAU_AMOUNT_BITS,
            "status": "SELECTED_FOR_G1_SPECIFICATION_ONLY",
        },
        {
            "asset_class": "LP_SHARE",
            "asset_id": "LP_SHARE_RELEASE_DEFINED",
            "ledger_decimals": TARGET_DECIMALS,
            "tau_amount_width_bits": TARGET_TAU_AMOUNT_BITS,
            "status": "SELECTED_FOR_G1_SPECIFICATION_ONLY",
        },
    ]


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    predecessor = repo_root / PREDECESSOR_PATH
    predecessor_document = _load(predecessor)
    predecessor_selected = predecessor_document.get("selected_parameters")
    if not isinstance(predecessor_selected, Mapping):
        raise ValueError("historical V2 selected parameters are missing")
    if predecessor_selected.get("decimals") != 18:
        raise ValueError("historical V2 no longer contains the superseded E18 decision")

    missing_dependents = [
        path for path in HISTORICAL_E18_DEPENDENTS if not (repo_root / path).is_file()
    ]
    if missing_dependents:
        raise ValueError(f"historical E18 dependent paths are missing: {missing_dependents}")

    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "SELECTED_FOR_G1_SPECIFICATION_ONLY",
        "production_authority": "NONE",
        "decision_provenance": {
            "channel": "INTERACTIVE_USER_INSTRUCTION",
            "recorded_date": "2026-08-20",
            "accepted_recommendation": (
                "E8 target amounts with a BV64 Tau target profile, an exact four-decimal "
                "current-testnet adapter, Rust settlement arithmetic, and Tau policy checks"
            ),
            "cryptographic_user_signature": None,
            "release_activation": "UNSELECTED",
        },
        "predecessor_binding": {
            "artifact": PREDECESSOR_PATH,
            "sha256": _sha256(predecessor),
            "retained_fields": [
                "whole_token_supply",
                "genesis_only_issue_model",
                "post_genesis_mint_forbidden",
                "one_atom_absolute_floor",
                "launch_active_floor_whole_tokens",
                "liability_first_waterfall",
                "all_open_participant_and_launch_gates",
            ],
            "superseded_fields": [
                "decimals",
                "unit_scale",
                "genesis_supply_atoms",
                "supply_ceiling_atoms",
                "launch_active_floor_atoms",
                "E18_redenomination_language",
            ],
            "precedence_rule": "THIS_RECORD_CONTROLS_ASSET_SCALE_FOR_SUCCESSOR_G1_WORK",
        },
        "selected_precision": {
            "target_common_decimals": TARGET_DECIMALS,
            "target_unit_scale": UNIT_SCALE,
            "allowed_registry_decimals": {"minimum": 0, "maximum": MAX_REGISTERED_DECIMALS},
            "whole_zdex_supply": WHOLE_ZDEX_SUPPLY,
            "zdex_genesis_supply_atoms": WHOLE_ZDEX_SUPPLY * UNIT_SCALE,
            "zdex_supply_ceiling_atoms": WHOLE_ZDEX_SUPPLY * UNIT_SCALE,
            "launch_active_floor_whole_tokens": LAUNCH_ACTIVE_FLOOR_WHOLE,
            "launch_active_floor_atoms": LAUNCH_ACTIVE_FLOOR_WHOLE * UNIT_SCALE,
            "maximum_settlement_delta_atoms": MAX_SETTLEMENT_DELTA_ATOMS,
            "scale_change_rule": "NEW_ASSET_IDENTITY_OR_PROVED_FORWARD_MIGRATION_ONLY",
            "canonical_amount_encoding": "NONNEGATIVE_INTEGER_ATOMS_NO_FLOATS",
        },
        "managed_asset_profiles": _asset_profiles(),
        "automatic_governance_boundary": {
            "classification": "TYPED_COMMAND_ORIGINATOR_NOT_AN_ASSET",
            "may_propose": "REGISTERED_GOVERNANCE_COMMANDS_WITHIN_RELEASE_BOUND_ENVELOPES",
            "may_not_hold": [
                "SETTLEMENT_PUBLICATION_AUTHORITY",
                "UNBOUNDED_ISSUE_AUTHORITY",
                "UNBOUNDED_BURN_AUTHORITY",
                "IN_PLACE_SCALE_REINTERPRETATION_AUTHORITY",
                "PROFILE_ACTIVATION_AUTHORITY_WITHOUT_GOVERNED_APPROVAL",
            ],
            "status": "OPEN_SEMANTICS_REQUIRED_BEFORE_MOUNTING",
        },
        "arithmetic_contract": {
            "tau_policy_domain": "FIXED_WIDTH_INTEGER_BITVECTORS",
            "rust_core_domain": "CHECKED_U128_STATE_AND_I128_BOUNDED_EFFECT_DELTAS",
            "upscale": "CHECKED_MULTIPLICATION_BY_POWER_OF_TEN",
            "downscale": "EXACT_DIVISION_OR_TYPED_REJECTION_ON_NONZERO_REMAINDER",
            "price_and_ratio_precision": "SEPARATELY_VERSIONED_FROM_TOKEN_AMOUNT_DECIMALS",
            "tau_current_transfer_max_atoms": (1 << CURRENT_TAU_TESTNET_AMOUNT_BITS) - 1,
            "tau_target_transfer_max_atoms": (1 << TARGET_TAU_AMOUNT_BITS) - 1,
        },
        "burn_contract": {
            "minimum_burn_atoms": 1,
            "percentage_rounding": "FLOOR",
            "fractional_residue": "EXPLICIT_NUMERATOR_OVER_10000",
            "zero_atom_quote": "NO_BURN_WITH_RECORDED_RESIDUE",
            "final_atom": "REQUIRES_EXPLICIT_ASSET_RETIREMENT_COMMAND",
            "conservation": [
                "source_allocation_post = source_allocation_pre - burn_atoms",
                "supply_post = supply_pre - burn_atoms",
            ],
        },
        "implementation_binding": {
            "status": "IMPLEMENTED_RESEARCH_KERNEL_UNMOUNTED",
            "source_pins": [
                _source_pin(repo_root, RUST_KERNEL_PATH),
                _source_pin(repo_root, RUST_EXPORT_PATH),
                _source_pin(repo_root, RUST_TEST_PATH),
                _source_pin(repo_root, CHECKER_PATH),
                _source_pin(repo_root, CHECKER_TEST_PATH),
            ],
            "rust_contracts": [
                "AssetPrecisionRegistryV1",
                "exact_rescale_atoms_v1",
                "admit_tau_amount_v1",
                "quote_floor_bps_burn_v1",
                "admit_burn_v1",
            ],
            "proof_guest_binding": "ABSENT",
            "tau_runtime_parity": "ABSENT",
            "python_rust_parity": "ABSENT",
            "mounted_transition_binding": "ABSENT",
        },
        "historical_e18_dependents": {
            "status": "HISTORICAL_E18_NOT_APPLICABLE_TO_CURRENT_E8_PROFILE",
            "paths": list(HISTORICAL_E18_DEPENDENTS),
            "required_before_reuse": (
                "Regenerate and re-review every atom-denominated constant, source pin, vector, "
                "root, and rounding boundary against this E8 decision"
            ),
        },
        "open_semantic_decisions": [
            "exact Tau-originated mainnet asset identifiers and native source scales",
            "issue and burn authorities for every managed asset",
            "LP-share namespace, maximum supply, and terminal pool disposition",
            "zUSD collateral and liability lifecycle parameters",
            "automatic-governance proposal, approval, delay, revocation, and emergency boundaries",
            "composite policy-registry binding from this precision root into an active profile",
            "migration from historical E18 research fixtures and any preexisting state",
        ],
        "release_gate": {
            "g1_complete": False,
            "production_ready": False,
            "launch_allowed": False,
            "activation_eligible": False,
        },
        "nonclaims": [
            "This decision does not establish the future Tau mainnet token ABI or native decimal scale.",
            "The Rust kernel is not mounted by a transition, profile, Tau policy, proof guest, or writer.",
            "No Python/Rust/Tau/RISC0 refinement evidence exists for this precision kernel yet.",
            "Historical E18 research remains valid only for its historical profile and is not successor E8 release evidence.",
            "No issue, burn, migration, settlement, governance, release, or production authority is granted.",
        ],
    }


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(_encoded(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if path.read_bytes() != _encoded(observed):
            errors.append("asset-precision artifact is not canonically encoded JSON")
        if observed != expected:
            errors.append("artifact differs from the exact selected asset-precision record")
    except (OSError, TypeError, ValueError, KeyError) as exc:
        errors.append(str(exc))
    return {
        "schema": "zenodex/production-readiness-g1-asset-precision-check/v1",
        "ok": not errors,
        "target_common_decimals": observed.get("selected_precision", {}).get(
            "target_common_decimals"
        )
        if isinstance(observed.get("selected_precision"), Mapping)
        else None,
        "production_authority": "NONE",
        "g1_complete": False,
        "production_ready": False,
        "activation_eligible": False,
        "errors": errors,
        "nonclaim": (
            "PASS confirms the exact unmounted E8 research decision and its source pins; "
            "it grants no value-moving or governance authority."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    args = parser.parse_args()

    if args.check:
        report = check_artifact(args.output, args.repo_root)
        if args.json:
            print(json.dumps(report, indent=2, sort_keys=True))
        elif report["ok"]:
            print("PASS: exact G1 asset-precision research decision")
        else:
            print("FAIL: " + "; ".join(report["errors"]))
        return 0 if report["ok"] else 1

    _write_atomic(args.output, build_document(args.repo_root))
    if args.json:
        print(json.dumps({"ok": True, "output": str(args.output)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
