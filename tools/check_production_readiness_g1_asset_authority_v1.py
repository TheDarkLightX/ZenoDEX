#!/usr/bin/env python3
"""Build and check the inactive G1 four-asset authority candidate.

The record turns the recommended TAU, ZDEX, zUSD, LP-share, and AutoGov
boundaries into one exact review candidate. It remains unselected and cannot
authorize a transition, profile activation, proof admission, or publication.
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
DEFAULT_OUTPUT = (
    REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_ASSET_AUTHORITY_V1.json"
)
SCHEMA = "zenodex/production-readiness-g1-asset-authority/v1"
RUST_CANDIDATE_SCHEMA = "zenodex/g1-asset-authority-candidate/v1"
RUST_CANDIDATE_HASH_DOMAIN = "g1-asset-authority-candidate-v1"
PRECISION_ARTIFACT_PATH = (
    "docs/research/PRODUCTION_READINESS_G1_ASSET_PRECISION_V1.json"
)
RUST_KERNEL_PATH = "zk/global_settlement_abi_v1/src/asset_authority_profile.rs"
RUST_EXPORT_PATH = "zk/global_settlement_abi_v1/src/lib.rs"
RUST_TEST_PATH = "zk/global_settlement_abi_v1/tests/asset_authority_profile.rs"
CHECKER_PATH = "tools/check_production_readiness_g1_asset_authority_v1.py"
CHECKER_TEST_PATH = "tests/test_check_production_readiness_g1_asset_authority_v1.py"
BOUND_PATHS = (
    PRECISION_ARTIFACT_PATH,
    RUST_KERNEL_PATH,
    RUST_EXPORT_PATH,
    RUST_TEST_PATH,
    CHECKER_PATH,
    CHECKER_TEST_PATH,
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
        raise ValueError("asset-authority artifact root must be an object")
    return result


def _source_pin(repo_root: Path, relative_path: str) -> dict[str, str]:
    path = repo_root / relative_path
    if not path.is_file():
        raise ValueError(f"bound asset-authority path is missing: {relative_path}")
    return {"path": relative_path, "sha256": _sha256(path)}


def _asset_policies() -> list[dict[str, Any]]:
    policies = [
        {
            "asset_id": "TAU",
            "asset_class": "TAU_ORIGINATED_TOKEN",
            "ledger_decimals": 8,
            "local_issue_authority": "NO_LOCAL_AUTHORITY",
            "local_burn_authority": "NO_LOCAL_AUTHORITY",
            "entry_rule": "VERIFIED_TAU_OCCURRENCE_ADAPTER_REQUIRED",
            "local_supply_semantics": "MIRROR_ONLY_NO_LOCAL_ISSUE_OR_BURN",
            "terminal_rule": "RETURN_ALL_TAU_CLAIMS_BEFORE_DISABLE",
            "availability": "TAU_INTEGRATION_HOLD",
        },
        {
            "asset_id": "ZDEX",
            "asset_class": "ZDEX_PROTOCOL_TOKEN",
            "ledger_decimals": 8,
            "local_issue_authority": "GOVERNANCE_MIGRATION_GENESIS_ONLY",
            "local_burn_authority": "ZDEX_TOKENOMICS_EXACT_SOURCE",
            "entry_rule": "GENESIS_DISTRIBUTION_ROOT_AND_RELEASE_REQUIRED",
            "local_supply_semantics": "POST_GENESIS_ISSUE_FORBIDDEN",
            "terminal_rule": "EXPLICIT_ASSET_RETIREMENT",
            "availability": "CANDIDATE_UNSELECTED",
        },
        {
            "asset_id": "zUSD",
            "asset_class": "CANONICAL_ZUSD",
            "ledger_decimals": 8,
            "local_issue_authority": "ZUSD_MONETARY_KERNEL",
            "local_burn_authority": "ZUSD_MONETARY_KERNEL",
            "entry_rule": "MATCHED_DEBT_AND_COLLATERAL_TRANSITION_REQUIRED",
            "local_supply_semantics": "SUPPLY_EQUALS_CURRENT_MONETARY_LIABILITY",
            "terminal_rule": "ZERO_AFTER_LIABILITIES_AND_CLAIMS_DRAIN",
            "availability": "CANDIDATE_UNSELECTED",
        },
        {
            "asset_id": "LP_SHARE_RELEASE_DEFINED",
            "asset_class": "LP_SHARE",
            "ledger_decimals": 8,
            "local_issue_authority": "SPOT_LIQUIDITY_POOL_KERNEL",
            "local_burn_authority": "SPOT_LIQUIDITY_POOL_KERNEL",
            "entry_rule": "POOL_RELEASE_AND_EXACT_RESERVE_STATE_REQUIRED",
            "local_supply_semantics": "POOL_SCOPED_PROPORTIONAL_CLAIM",
            "terminal_rule": "POOL_CLOSE_DRAINS_ALL_RESERVES_FEES_AND_RESIDUE",
            "availability": "CANDIDATE_UNSELECTED",
        },
    ]
    return sorted(policies, key=lambda policy: str(policy["asset_id"]))


def _automatic_governance_boundary() -> dict[str, str]:
    return {
        "role": "REGISTERED_PROPOSAL_ORIGINATOR",
        "direct_issue_authority": "ABSENT_BY_CONSTRUCTION",
        "direct_burn_authority": "ABSENT_BY_CONSTRUCTION",
        "profile_activation_authority": "ABSENT_BY_CONSTRUCTION",
        "settlement_publication_authority": "ABSENT_BY_CONSTRUCTION",
        "proposal_effect": (
            "NO_VALUE_MOVEMENT_UNTIL_SEPARATE_GOVERNED_APPROVAL_AND_ACTIVATION"
        ),
    }


def _canonical_rust_binding(precision_artifact_sha256: str) -> dict[str, str]:
    precision_registry_root = f"0x{precision_artifact_sha256}"
    rust_policies = [
        {
            "asset": policy["asset_id"],
            "asset_class": policy["asset_class"],
            "ledger_decimals": policy["ledger_decimals"],
            "issue_authority": policy["local_issue_authority"],
            "burn_authority": policy["local_burn_authority"],
            "terminal_rule": policy["terminal_rule"],
            "availability": policy["availability"],
        }
        for policy in _asset_policies()
    ]
    candidate = {
        "schema": RUST_CANDIDATE_SCHEMA,
        "precision_registry_root": precision_registry_root,
        "policies": rust_policies,
        "automatic_governance_role": "REGISTERED_PROPOSAL_ORIGINATOR",
        "selection": "CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED",
    }
    canonical_bytes = json.dumps(
        candidate,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    profile_hasher = hashlib.sha256()
    profile_hasher.update(b"zenodex:")
    profile_hasher.update(RUST_CANDIDATE_HASH_DOMAIN.encode("ascii"))
    profile_hasher.update(b":v1\0")
    profile_hasher.update(canonical_bytes)
    return {
        "status": "ONE_EXACT_PYTHON_RUST_GOLDEN_VECTOR",
        "precision_registry_root": precision_registry_root,
        "canonical_bytes_sha256": f"sha256:{hashlib.sha256(canonical_bytes).hexdigest()}",
        "candidate_profile_root": f"0x{profile_hasher.hexdigest()}",
    }


def _implementation_binding(repo_root: Path) -> dict[str, Any]:
    return {
        "status": "IMPLEMENTED_RUST_VALUE_MODEL_UNMOUNTED",
        "source_pins": [_source_pin(repo_root, path) for path in BOUND_PATHS],
        "rust_contracts": [
            "AssetAuthorityPolicyV1",
            "G1AssetAuthorityCandidateV1",
            "g1_testnet_asset_authority_candidate_v1",
        ],
        "python_rust_canonical_parity": "ONE_EXACT_GOLDEN_VECTOR",
        "mounted_transition_binding": "ABSENT",
        "proof_guest_binding": "ABSENT",
        "tau_runtime_binding": "ABSENT",
        "writer_binding": "ABSENT",
    }


def _profile_decision_effect() -> dict[str, Any]:
    return {
        "closed_profile_decisions": [],
        "narrowed_profile_decisions": ["asset_issue_burn_policy"],
        "remaining_before_selection": [
            "user confirmation of this exact authority matrix",
            "exact ZDEX genesis distribution root and activation occurrence",
            "verified Tau occurrence and replay adapter",
            "LP-share namespace and arithmetic profile",
            "zUSD monetary lifecycle profile",
            "runtime, proof, migration, and writer refinement evidence",
        ],
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    precision_path = repo_root / PRECISION_ARTIFACT_PATH
    precision = _load(precision_path)
    selected_precision = precision.get("selected_precision")
    if not isinstance(selected_precision, Mapping):
        raise ValueError("selected E8 precision record is missing")
    if selected_precision.get("target_common_decimals") != 8:
        raise ValueError("asset-authority candidate requires the selected E8 profile")
    if precision.get("production_authority") != "NONE":
        raise ValueError("precision predecessor unexpectedly grants authority")

    precision_sha256 = _sha256(precision_path)
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_ASSET_AUTHORITY_CANDIDATE_RESEARCH_ONLY",
        "decision_id": "asset_issue_burn_policy",
        "decision_status": "PROPOSED_UNSELECTED_USER_CONFIRMATION_REQUIRED",
        "production_authority": "NONE",
        "precision_binding": {
            "artifact": PRECISION_ARTIFACT_PATH,
            "sha256": precision_sha256,
            "target_common_decimals": 8,
        },
        "asset_policies": _asset_policies(),
        "automatic_governance_boundary": _automatic_governance_boundary(),
        "canonical_rust_binding": _canonical_rust_binding(precision_sha256),
        "implementation_binding": _implementation_binding(repo_root),
        "profile_decision_effect": _profile_decision_effect(),
        "release_gate": {
            "candidate_profile_count": 1,
            "selected_profile_count": 0,
            "activation_eligible": False,
            "g1_complete": False,
            "production_ready": False,
            "launch_allowed": False,
        },
        "nonclaims": [
            "This candidate records a proposed module-ownership matrix and is not selected policy.",
            "TAU remains on an integration hold until a verified occurrence and replay adapter exists.",
            "No local component receives authority to issue or destroy TAU.",
            "AutoGov can originate registered proposals and receives no direct value-moving, activation, or publication authority.",
            "Rust validation establishes exact candidate structure only; runtime, Tau, RISC0, migration, and writer refinement remain absent.",
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
            errors.append("asset-authority artifact is not canonically encoded JSON")
        if observed != expected:
            errors.append("artifact differs from the exact asset-authority candidate")
    except (OSError, TypeError, ValueError, KeyError) as exc:
        errors.append(str(exc))

    release_gate = observed.get("release_gate")
    gate = release_gate if isinstance(release_gate, Mapping) else {}
    selected_profile_count = gate.get("selected_profile_count", 0)
    if observed.get("decision_status") == "SELECTED" or gate.get(
        "activation_eligible"
    ) is True:
        selected_profile_count = max(
            selected_profile_count if type(selected_profile_count) is int else 0,
            1,
        )
    return {
        "schema": "zenodex/production-readiness-g1-asset-authority-check/v1",
        "ok": not errors,
        "candidate_profile_count": gate.get("candidate_profile_count", 0),
        "selected_profile_count": selected_profile_count,
        "production_authority": "NONE",
        "g1_complete": False,
        "production_ready": False,
        "activation_eligible": False,
        "errors": errors,
        "nonclaim": (
            "PASS confirms one exact inactive authority candidate and source pins; "
            "it grants no value-moving, activation, proof, or publication authority."
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
            print("PASS: exact inactive G1 asset-authority candidate")
        else:
            print("FAIL: " + "; ".join(report["errors"]))
        return 0 if report["ok"] else 1

    _write_atomic(args.output, build_document(args.repo_root))
    if args.json:
        print(json.dumps({"ok": True, "output": str(args.output)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
