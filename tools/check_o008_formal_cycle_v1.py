#!/usr/bin/env python3
"""Fail-closed checker for the bounded O-008 formal-cycle evidence packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ARTIFACT = ROOT / "docs" / "research" / "ZENODEX_O008_FORMAL_CYCLE_V1.json"

EXPECTED_TOP_LEVEL = {
    "schema",
    "created_date",
    "subject_commit",
    "subject_parent",
    "formal_cycle_status",
    "supported_claim",
    "o008_status",
    "formal_core_complete",
    "whole_value_movement_safe",
    "value_movement_gates_closed",
    "value_movement_gates_total",
    "production_authority",
    "settlement_authority",
    "release_authority",
    "verifier_authority",
    "completion_scope",
    "source_pins",
    "esso_evidence",
    "lean_evidence",
    "v1_information_loss",
    "lane_source_data",
    "required_sidecar",
    "replay_commands",
    "nonclaims",
}

EXPECTED_LANES = (
    "ASSET_TRANSFER",
    "SPOT_LIQUIDITY",
    "FARM_INCENTIVES",
    "ZDEX_TOKENOMICS",
    "ZUSD_MONETARY",
    "PERPS_MARKET",
    "ORACLE_MARKET",
    "SEALED_AUCTION",
    "STRATEGY_ESCROW",
    "PROOF_REWARDS",
    "EXTERNAL_CUSTODY",
    "GOVERNANCE_MIGRATION",
)

EXPECTED_SIDECAR_FIELDS = (
    "global_state_root",
    "profile_root",
    "writer_epoch",
    "chain_context",
    "ordered_lane_fragments",
    "canonical_allocation_rows",
    "field_ownership_root",
    "terminal_binding_root",
    "allocation_root",
)

EXPECTED_SIDECAR_CHECKS = (
    "exact_twelve_lane_order",
    "enabled_lane_supported_receipt_backed_producer",
    "disabled_lane_registered_empty_state_root",
    "every_controlled_source_atom_assigned_exactly_once",
    "claimant_allocations_equal_liabilities",
    "reserve_allocations_equal_selected_normative_reserve_interpretation",
    "external_obligations_bind_asset_amount_destination_and_commitment",
    "terminal_rows_bind_claimant_asset_amount_domain_principal_lane_and_state_root",
    "lane_aggregates_equal_global_economic_tables",
    "checked_u128_arithmetic_and_canonical_order",
)

REQUIRED_THEOREMS = {
    "exactAllocation_noUnclassified_implies_certificateRelation",
    "controlledClaimReserveEquation_iff_exactCustody",
    "deposit_preserves_currentProfileCertificateRelation",
    "drain_preserves_currentProfileCertificateRelation",
    "aggregateOnly_permits_crossDomainBacking",
    "aggregateClaimants_permit_claimantSwap",
    "reserveMasking_violates_controlledClaimReserveEquation",
    "terminalProjection_domainErasure_notInjective",
    "terminalProjection_hasNoUniversalDomainRecovery",
}


class DuplicateKeyError(ValueError):
    """Raised when canonical evidence JSON repeats an object key."""


def _closed_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_closed_object)
    if type(value) is not dict:
        raise ValueError("formal-cycle artifact must be one JSON object")
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )


def _require(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def _check_subject(artifact: dict[str, Any], errors: list[str]) -> None:
    subject = artifact.get("subject_commit")
    parent = artifact.get("subject_parent")
    _require(type(subject) is str and re.fullmatch(r"[0-9a-f]{40}", subject) is not None,
             "subject_commit must be a full lowercase Git object id", errors)
    _require(type(parent) is str and re.fullmatch(r"[0-9a-f]{40}", parent) is not None,
             "subject_parent must be a full lowercase Git object id", errors)
    if not isinstance(subject, str) or not isinstance(parent, str):
        return
    exists = _git("cat-file", "-e", f"{subject}^{{commit}}")
    _require(exists.returncode == 0, "subject_commit is unavailable", errors)
    actual_parent = _git("rev-parse", f"{subject}^")
    _require(
        actual_parent.returncode == 0 and actual_parent.stdout.strip() == parent,
        "subject_parent is not the exact first parent",
        errors,
    )
    ancestor = _git("merge-base", "--is-ancestor", subject, "HEAD")
    _require(ancestor.returncode == 0, "subject_commit is not an ancestor of HEAD", errors)


def _check_source_pins(artifact: dict[str, Any], errors: list[str]) -> None:
    pins = artifact.get("source_pins")
    if type(pins) is not list:
        errors.append("source_pins must be a list")
        return
    seen: set[str] = set()
    for index, row in enumerate(pins):
        if type(row) is not dict or set(row) != {"path", "sha256", "role"}:
            errors.append(f"source_pins[{index}] has an invalid closed shape")
            continue
        relative = row["path"]
        digest = row["sha256"]
        if type(relative) is not str or not relative or Path(relative).is_absolute() or ".." in Path(relative).parts:
            errors.append(f"source_pins[{index}] has an unsafe path")
            continue
        if relative in seen:
            errors.append(f"duplicate source pin: {relative}")
            continue
        seen.add(relative)
        path = ROOT / relative
        _require(path.is_file(), f"pinned source is missing: {relative}", errors)
        _require(type(digest) is str and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                 f"invalid SHA-256 for {relative}", errors)
        if path.is_file() and isinstance(digest, str):
            _require(_sha256(path) == digest, f"source drift: {relative}", errors)


def _check_status(artifact: dict[str, Any], errors: list[str]) -> None:
    exact = {
        "schema": "zenodex/o008-formal-cycle-evidence/v1",
        "formal_cycle_status": "FORMAL_CYCLE_COMPLETE_O008_OPEN",
        "supported_claim": "O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED",
        "o008_status": "OPEN_EXACT_ALL_12_RECONCILIATION_MISSING",
        "formal_core_complete": False,
        "whole_value_movement_safe": False,
        "value_movement_gates_closed": 0,
        "value_movement_gates_total": 12,
        "production_authority": "NONE",
        "settlement_authority": "NONE",
        "release_authority": "NONE",
        "verifier_authority": "NONE",
    }
    for key, expected in exact.items():
        _require(type(artifact.get(key)) is type(expected) and artifact.get(key) == expected,
                 f"unsafe or unexpected {key}", errors)


def _check_esso(artifact: dict[str, Any], errors: list[str]) -> None:
    evidence = artifact.get("esso_evidence")
    if type(evidence) is not dict:
        errors.append("esso_evidence must be an object")
        return
    _require(evidence.get("model_id") == "global_claimant_custody_certificate_v1",
             "unexpected ESSO model id", errors)
    _require(evidence.get("invariant_count") == 8, "ESSO invariant count must be eight", errors)
    _require(evidence.get("per_invariant_projections") == 8,
             "every ESSO invariant needs a recorded projection", errors)
    _require(evidence.get("named_mutants_with_two_solver_counterexamples") == 5,
             "five named ESSO mutant counterexamples are required", errors)
    _require(evidence.get("queries") == ["init_implies_inv", "inductive_open_claim", "inductive_drain_claim"],
             "ESSO query surface drift", errors)
    _require(evidence.get("esso_code_commit") == "7f80c6216be85c827e8d1cc2fa08ee3107a74588",
             "ESSO tool subject drift", errors)


def _check_lean(artifact: dict[str, Any], errors: list[str]) -> None:
    evidence = artifact.get("lean_evidence")
    if type(evidence) is not dict:
        errors.append("lean_evidence must be an object")
        return
    _require(evidence.get("toolchain") == "leanprover/lean4:v4.27.0",
             "Lean toolchain drift", errors)
    _require(evidence.get("sorry_admit_sorryAx_count") == 0,
             "Lean placeholder count must be zero", errors)
    _require(evidence.get("theorem_count") == 18, "Lean theorem count must be eighteen", errors)
    _require(set(evidence.get("required_theorems", [])) == REQUIRED_THEOREMS,
             "required Lean theorem inventory drift", errors)

    proof = ROOT / "lean-mathlib" / "Proofs" / "GlobalClaimantCustodyRelationV1.lean"
    if proof.is_file():
        names = set(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", proof.read_text(encoding="utf-8"), re.MULTILINE))
        _require(len(names) == 18, "live Lean theorem count drift", errors)
        _require(REQUIRED_THEOREMS <= names, "live Lean theorem surface is incomplete", errors)


def _check_v1_information_loss(artifact: dict[str, Any], errors: list[str]) -> None:
    loss = artifact.get("v1_information_loss")
    if type(loss) is not dict:
        errors.append("v1_information_loss must be an object")
        return
    _require(loss.get("terminal_missing_fields") == ["liability_domain", "custody_principal"],
             "V1 terminal information-loss fields drift", errors)
    _require(loss.get("external_outbox_missing_fields") == ["asset", "amount_atoms"],
             "V1 outbox information-loss fields drift", errors)
    _require(loss.get("formal_result") == "NO_UNIVERSAL_RECOVERY_FROM_V1_TERMINAL_PROJECTION",
             "V1 no-recovery result is absent", errors)
    _require(loss.get("mounted_exploit_claim") is False,
             "mounted exploit claim must remain false", errors)

    python_types = (ROOT / "src" / "core" / "global_settlement_types_v1.py").read_text(encoding="utf-8")
    terminal_match = re.search(
        r"class TerminalObligationV1:\n(?P<body>.*?)(?=\n\nclass OutboxStatusV1)",
        python_types,
        re.DOTALL,
    )
    _require(terminal_match is not None, "Python TerminalObligationV1 is missing", errors)
    if terminal_match is not None:
        body = terminal_match.group("body")
        _require("liability_domain:" not in body and "custody_principal:" not in body,
                 "V1 terminal unexpectedly contains the recorded missing fields", errors)


def _check_lane_and_sidecar(artifact: dict[str, Any], errors: list[str]) -> None:
    lanes = artifact.get("lane_source_data")
    if type(lanes) is not list:
        errors.append("lane_source_data must be a list")
    else:
        _require(tuple(row.get("lane_id") for row in lanes if type(row) is dict) == EXPECTED_LANES,
                 "lane source-data inventory must cover the exact twelve-lane order", errors)
        _require(len(lanes) == 12 and all(type(row) is dict and set(row) == {"lane_id", "status", "missing"} for row in lanes),
                 "lane source-data rows need a closed shape", errors)
        _require(all(row.get("status") != "COMPLETE" for row in lanes if type(row) is dict),
                 "no lane may claim complete exact reconciliation", errors)

    sidecar = artifact.get("required_sidecar")
    if type(sidecar) is not dict:
        errors.append("required_sidecar must be an object")
        return
    _require(sidecar.get("type_name") == "GlobalAccountingAllocationCertificateV1",
             "sidecar type drift", errors)
    _require(tuple(sidecar.get("required_fields", ())) == EXPECTED_SIDECAR_FIELDS,
             "sidecar field inventory drift", errors)
    _require(tuple(sidecar.get("required_checks", ())) == EXPECTED_SIDECAR_CHECKS,
             "sidecar checker obligation inventory drift", errors)
    _require(sidecar.get("host_only_authority") == "EVIDENCE_ONLY",
             "detached host sidecar must remain evidence-only", errors)


def check_artifact(path: Path) -> dict[str, Any]:
    errors: list[str] = []
    try:
        artifact = _load(path)
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError, ValueError) as exc:
        return {"ok": False, "artifact": str(path), "errors": [str(exc)]}

    _require(set(artifact) == EXPECTED_TOP_LEVEL, "top-level artifact schema drift", errors)
    _check_status(artifact, errors)
    _check_subject(artifact, errors)
    _check_source_pins(artifact, errors)
    _check_esso(artifact, errors)
    _check_lean(artifact, errors)
    _check_v1_information_loss(artifact, errors)
    _check_lane_and_sidecar(artifact, errors)

    nonclaims = " ".join(str(item) for item in artifact.get("nonclaims", []))
    for phrase in (
        "does not complete O-008",
        "not implemented or mounted",
        "No production, release, settlement, verifier, migration, publication, or value-moving authority",
    ):
        _require(phrase in nonclaims, f"missing nonclaim: {phrase}", errors)

    return {
        "ok": not errors,
        "artifact": str(path),
        "subject_commit": artifact.get("subject_commit"),
        "formal_cycle_status": artifact.get("formal_cycle_status"),
        "o008_status": artifact.get("o008_status"),
        "source_pin_count": len(artifact.get("source_pins", [])),
        "lane_count": len(artifact.get("lane_source_data", [])),
        "errors": errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    args = parser.parse_args()
    result = check_artifact(args.artifact.resolve())
    print(json.dumps(result, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
