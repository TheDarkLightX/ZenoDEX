#!/usr/bin/env python3
"""Build and check the inactive G1 Spot/LP policy candidate."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
import re
import tempfile
from collections.abc import Mapping
from pathlib import Path
from typing import Any

_REFERENCE_MODULE = (
    "tools.production_readiness_g1_spot_lp_reference"
    if __package__
    else "production_readiness_g1_spot_lp_reference"
)
_reference = importlib.import_module(_REFERENCE_MODULE)
_ASSET_CHECKER_MODULE = (
    "tools.check_production_readiness_g1_asset_authority_v1"
    if __package__
    else "check_production_readiness_g1_asset_authority_v1"
)
_asset_checker = importlib.import_module(_ASSET_CHECKER_MODULE)
MAX_POOL_ATOMS: int = _reference.MAX_POOL_ATOMS
PROTOCOL_FEE_SHARE_BPS: int = _reference.PROTOCOL_FEE_SHARE_BPS
SWAP_FEE_BPS: int = _reference.SWAP_FEE_BPS
build_differential_vectors = _reference.build_differential_vectors

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_SPOT_LP_POLICY_V1.json"
SCHEMA = "zenodex/production-readiness-g1-spot-lp-policy/v1"
RUST_CANDIDATE_SCHEMA = "zenodex/g1-spot-lp-candidate/v1"
RUST_CANDIDATE_HASH_DOMAIN = "g1-spot-lp-candidate-v1"
ASSET_AUTHORITY_ARTIFACT_PATH = "docs/research/PRODUCTION_READINESS_G1_ASSET_AUTHORITY_V1.json"
RUST_POLICY_PATH = "zk/global_settlement_abi_v1/src/spot_liquidity_policy.rs"
RUST_KERNEL_PATH = RUST_POLICY_PATH
RUST_MATH_PATH = "zk/global_settlement_abi_v1/src/spot_liquidity_math.rs"
RUST_EXPORT_PATH = "zk/global_settlement_abi_v1/src/lib.rs"
CANONICAL_PATH = "zk/global_settlement_abi_v1/src/canonical.rs"
CARGO_MANIFEST_PATH = "zk/global_settlement_abi_v1/Cargo.toml"
CARGO_LOCK_PATH = "zk/global_settlement_abi_v1/Cargo.lock"
RUST_TEST_PATH = "zk/global_settlement_abi_v1/tests/spot_liquidity_policy.rs"
RUST_STATEFUL_TEST_PATH = "zk/global_settlement_abi_v1/tests/spot_liquidity_stateful.rs"
RUST_PROPERTY_TEST_PATH = "zk/global_settlement_abi_v1/tests/spot_liquidity_properties.rs"
REFERENCE_PATH = "tools/production_readiness_g1_spot_lp_reference.py"
CHECKER_PATH = "tools/check_production_readiness_g1_spot_lp_policy_v1.py"
CHECKER_TEST_PATH = "tests/test_check_production_readiness_g1_spot_lp_policy_v1.py"
ASSET_AUTHORITY_BOUND_PATHS: tuple[str, ...] = tuple(_asset_checker.BOUND_PATHS)
BOUND_PATHS = (
    RUST_POLICY_PATH,
    RUST_MATH_PATH,
    RUST_EXPORT_PATH,
    CANONICAL_PATH,
    CARGO_MANIFEST_PATH,
    CARGO_LOCK_PATH,
    RUST_TEST_PATH,
    RUST_STATEFUL_TEST_PATH,
    RUST_PROPERTY_TEST_PATH,
    REFERENCE_PATH,
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
        raise ValueError("Spot/LP artifact root must be an object")
    return result


def _source_pin(repo_root: Path, relative_path: str) -> dict[str, str]:
    path = repo_root / relative_path
    if not path.is_file():
        raise ValueError(f"bound Spot/LP path is missing: {relative_path}")
    return {"path": relative_path, "sha256": _sha256(path)}


def _policy(asset_authority_profile_root: str) -> dict[str, Any]:
    return {
        "schema": RUST_CANDIDATE_SCHEMA,
        "asset_authority_profile_root": asset_authority_profile_root,
        "swap_fee_bps": SWAP_FEE_BPS,
        "protocol_fee_share_bps": PROTOCOL_FEE_SHARE_BPS,
        "fee_rounding": "CEIL_GROSS_INPUT",
        "output_rounding": "FLOOR_POOL_OUTPUT",
        "fee_owner": "CURRENT_LP_CLAIMANTS_VIA_POOL_RESERVES",
        "reserve_ingress": "POOL_KERNEL_ONLY",
        "initial_lp_mint": "FLOOR_SQRT_PRODUCT_NO_PERMANENT_LOCK",
        "additional_lp_mint": "MAX_NON_DILUTING_SHARES_CEIL_ASSET_USE_REFUND_EXCESS",
        "withdrawal": "PRO_RATA_FLOOR_FINAL_BURN_DRAINS_AND_CLOSES",
        "residue_owner": "REMAINING_LP_CLAIMANTS_THEN_FINAL_BURNER",
        "max_pool_atoms": MAX_POOL_ATOMS,
        "selection": "CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED",
    }


def _canonical_rust_binding(policy: Mapping[str, Any]) -> dict[str, str]:
    canonical_bytes = json.dumps(
        policy,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    profile_hasher = hashlib.sha256()
    profile_hasher.update(b"zenodex:")
    profile_hasher.update(RUST_CANDIDATE_HASH_DOMAIN.encode("ascii"))
    profile_hasher.update(b":v1\0")
    profile_hasher.update(canonical_bytes)
    return {
        "status": "EXACT_PYTHON_RUST_POLICY_AND_MATH_VECTORS",
        "canonical_bytes_sha256": f"sha256:{hashlib.sha256(canonical_bytes).hexdigest()}",
        "candidate_profile_root": f"0x{profile_hasher.hexdigest()}",
    }


def _preflight() -> dict[str, Any]:
    return {
        "artifact_and_authority": (
            "Pure inactive policy and arithmetic candidate; no route, receipt, commit, or writer."
        ),
        "construction_and_ownership": (
            "Owned scalar inputs and immutable result values; no retained aliases or mutable graphs."
        ),
        "semantics": {
            "units": "E8 ledger atoms under the predecessor asset-authority profile",
            "rounding": (
                "ceil fee and add-liquidity asset use; floor swap output, LP mint, and partial withdrawal"
            ),
            "residue": (
                "pool reserves remain claims of outstanding LP shares; the final full burn drains all atoms"
            ),
            "reject_semantics": "pure typed rejection returns no successor",
        },
        "encoding_and_binding": (
            "Versioned canonical JSON and domain-separated SHA-256 profile root."
        ),
        "commit_and_failure_model": (
            "Out of scope for this unmounted pure candidate; no persistence or external effects exist."
        ),
        "performance": "O(1) arithmetic plus a bounded 64-iteration integer square root",
        "change_separation": (
            "Legacy Python and RISC0 Spot implementations remain unchanged and retain their current claim ceilings."
        ),
    }


def _asset_binding(repo_root: Path) -> tuple[Path, str]:
    asset_path = repo_root / ASSET_AUTHORITY_ARTIFACT_PATH
    asset_artifact = _load(asset_path)
    predecessor_report = _asset_checker.check_artifact(asset_path, repo_root)
    if predecessor_report.get("ok") is not True:
        details = "; ".join(str(error) for error in predecessor_report.get("errors", []))
        raise ValueError(f"asset-authority predecessor artifact failed: {details}")
    if asset_artifact.get("production_authority") != "NONE":
        raise ValueError("asset-authority predecessor unexpectedly grants authority")
    binding = asset_artifact.get("canonical_rust_binding")
    if not isinstance(binding, Mapping):
        raise ValueError("asset-authority candidate root is missing")
    profile_root = binding.get("candidate_profile_root")
    if (
        not isinstance(profile_root, str)
        or re.fullmatch(r"0x[0-9a-f]{64}", profile_root) is None
        or profile_root == "0x" + ("0" * 64)
    ):
        raise ValueError("asset-authority candidate root is malformed")
    return asset_path, profile_root


def _implementation_binding(repo_root: Path) -> dict[str, Any]:
    return {
        "status": "IMPLEMENTED_RUST_PURE_CANDIDATE_UNMOUNTED",
        "source_pins": [_source_pin(repo_root, path) for path in BOUND_PATHS],
        "rust_contracts": [
            "G1SpotLpPolicyCandidateV1",
            "SpotPoolMathStateV1",
            "spot_exact_in_quote_v1",
            "spot_exact_out_quote_v1",
            "lp_create_quote_v1",
            "lp_add_quote_v1",
            "lp_remove_quote_v1",
        ],
        "python_rust_differential_vectors": 11,
        "mounted_transition_binding": "ABSENT",
        "proof_guest_binding": "ABSENT",
        "tau_runtime_binding": "ABSENT",
        "writer_binding": "ABSENT",
    }


def _profile_decision_effect() -> dict[str, Any]:
    return {
        "closed_profile_decisions": [],
        "narrowed_profile_decisions": ["spot_lp_fee_dust_withdrawal_policy"],
        "remaining_before_selection": [
            "user confirmation of this exact Spot/LP policy",
            "pool asset registry and release-compatible LP-share namespace",
            "mounted transition and complete canonical effect projection",
            "RISC0 guest, route, terminal, migration, and writer refinement evidence",
            "economic review of zero protocol fee and no-permanent-lock construction",
        ],
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    asset_path, asset_profile_root = _asset_binding(repo_root)
    policy = _policy(asset_profile_root)
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_SPOT_LP_POLICY_CANDIDATE_RESEARCH_ONLY",
        "decision_id": "spot_lp_fee_dust_withdrawal_policy",
        "decision_status": "PROPOSED_UNSELECTED_USER_CONFIRMATION_REQUIRED",
        "production_authority": "NONE",
        "asset_authority_binding": {
            "artifact": ASSET_AUTHORITY_ARTIFACT_PATH,
            "sha256": _sha256(asset_path),
            "candidate_profile_root": asset_profile_root,
        },
        "spot_lp_policy": {
            key: value
            for key, value in policy.items()
            if key not in {"schema", "asset_authority_profile_root", "selection"}
        },
        "canonical_rust_binding": _canonical_rust_binding(policy),
        "differential_vectors": build_differential_vectors(),
        "refactoring_preflight": _preflight(),
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
            "This is an unselected testnet policy candidate.",
            "The candidate does not modify or mount the legacy Spot, LP, RISC0, Tau, API, or ledger paths.",
            "Pure Rust arithmetic and Python differential vectors do not establish economic optimality, runtime refinement, proof admission, or settlement safety.",
            "The zero protocol share leaves each swap fee in pool reserves for current LP claimants and does not fund tokenomics.",
            "Final closure is safe only when reserve changes are exclusively constructed by the pool kernel and every outstanding LP share is burned.",
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
            errors.append("Spot/LP artifact is not canonically encoded JSON")
        if observed != expected:
            errors.append("artifact differs from the exact Spot/LP policy candidate")
    except (OSError, TypeError, ValueError, KeyError) as exc:
        errors.append(str(exc))

    gate_value = observed.get("release_gate")
    gate = gate_value if isinstance(gate_value, Mapping) else {}
    selected_profile_count = gate.get("selected_profile_count", 0)
    if observed.get("decision_status") == "SELECTED" or gate.get("activation_eligible") is True:
        selected_profile_count = max(
            selected_profile_count if type(selected_profile_count) is int else 0,
            1,
        )
    return {
        "schema": "zenodex/production-readiness-g1-spot-lp-policy-check/v1",
        "ok": not errors,
        "candidate_profile_count": gate.get("candidate_profile_count", 0),
        "selected_profile_count": selected_profile_count,
        "production_authority": "NONE",
        "g1_complete": False,
        "production_ready": False,
        "activation_eligible": False,
        "errors": errors,
        "nonclaim": (
            "PASS confirms one exact inactive policy and differential vectors; it grants no value-moving, proof, activation, or publication authority."
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
            print("PASS: exact inactive G1 Spot/LP policy candidate")
        else:
            print("FAIL: " + "; ".join(report["errors"]))
        return 0 if report["ok"] else 1

    _write_atomic(args.output, build_document(args.repo_root))
    if args.json:
        print(json.dumps({"ok": True, "output": str(args.output)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
