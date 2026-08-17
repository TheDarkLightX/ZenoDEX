#!/usr/bin/env python3
"""Render the canonical research-only V2 microkernel architecture manifest."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib
import json
import sys
from pathlib import Path
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

contract = importlib.import_module("tools.production_readiness_architecture_candidate_contract_v2")


DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_ARCHITECTURE_CANDIDATE_V2.json"

MUTANT_DESCRIPTIONS = {
    "ACK_EPOCH_OMITTED": "Remove writer-epoch binding from acknowledgment ingress.",
    "ACK_MUTATES_FROM_SHELL": "Let delivery success mutate economic state from the shell.",
    "ACK_BYPASSES_SETTLEMENT": "Route a destination acknowledgment around the core transition.",
    "ADVISORY_SELECTION": "Set architecture_selected from advisory structural scores.",
    "ASSUMPTION_TOKEN_INVENTED": "Replace both sides of a port contract with invented token X.",
    "CALLER_CONSTRUCTED_AUTHORITY": "Permit a caller to construct VerifiedAdmissionV2.",
    "CALLER_CONSTRUCTED_GOVERNANCE_AUTHORITY": (
        "Permit a caller to construct the governed-control authorization witness."
    ),
    "COMMAND_OMITTED": "Remove one command route.",
    "COMMAND_ORDER_AFTER_MODULE_ORDER": "Group a batch by module before command index.",
    "COMMAND_WRONG_MODULE": "Move zUSD borrow to the spot module.",
    "DEPENDENCY_CYCLE": "Make the ABI build-depend on the settlement kernel.",
    "DIRECT_CARRIES_ZRPF_WITNESS": "Attach a ZRPF-only verified journal to direct execution.",
    "DIRECT_GUEST_CORE_MISMATCH": "Use a guest-specific transition core.",
    "DRAIN_CREATES_OBJECT": "Permit new lifecycle objects during drain.",
    "EPOCH_CONTROL_UNTYPED": "Replace governed epoch control with an untyped control payload.",
    "EXTERNAL_EFFECT_BEFORE_COMMIT": "Dispatch staged outbox data before HEAD commit.",
    "FOREIGN_PROPOSAL_WRITE": "Let perps propose a zUSD state write.",
    "GOVERNANCE_WITNESS_DROPPED_DOWNSTREAM": (
        "Replace an authorized governance request with a raw control payload."
    ),
    "ISSUE_WRONG_ASSET": "Let a module issue an asset outside its exact capability scope.",
    "BURN_WRONG_ASSET": "Let a module burn an asset outside its exact capability scope.",
    "MIGRATION_CLASS_OMITTED": "Remove retained-pinned from the migration partition.",
    "MIGRATION_OBJECT_KIND_OMITTED": "Remove one persistent object kind from migration inventory.",
    "NATIVE_BACKUP_WITHOUT_GOVERNANCE_OR_EQUIVALENCE": (
        "Activate native backup without governance authorization or equivalence evidence."
    ),
    "OCCURRENCE_OMITS_RELEASE_SET": "Remove module-release-set root from occurrence identity.",
    "OUTBOX_ID_OMITS_PUBLICATION": "Remove publication root from effect idempotency.",
    "PORT_ASSUMPTION_NOT_GUARANTEED": "Add a response assumption absent from its guarantee.",
    "PORT_ORDER_ARRIVAL": "Use arrival order on a module evaluation port.",
    "PORT_TYPE_ANY": "Replace a closed port request type with ANY.",
    "PUBLICATION_DUPLICATE_BINDING": "Duplicate candidate fields without a canonical equality rule.",
    "POLICY_RELEASE_PARTIAL_COMMIT": "Permit one governed control subchange to commit alone.",
    "RELEASE_CONTROL_BYPASS": "Change release state outside ZenoLedger submission.",
    "ROUTE_INTENT_EXCEEDS_CAPABILITY": "Require an issue intent from the perps module.",
    "ROUTE_STEP_STEALS_INTENT": "Assign the burn intent to the spot acquisition step.",
    "SECOND_DURABLE_WRITER": "Give a state domain a second durable writer.",
    "SELF_ATTESTED_EVIDENCE": "Mark a gate verified with a publisher-authored reference.",
    "SOLVER_UNKNOWN_ACCEPTED": "Permit UNKNOWN, timeout, or solver disagreement.",
    "SOURCE_SPLIT_SNAPSHOT": "Validate semantics from different source bytes than the pinned hash.",
    "SOURCE_SYMLINK_SUBSTITUTION": "Resolve a pinned source through a symlink.",
    "SOURCE_EXECUTION_SNAPSHOT_SPLIT": (
        "Claim that the already-running checker authenticated its own executable identity."
    ),
    "TRUST_MODULE_DELTA": "Accept a module-supplied value delta as authoritative.",
    "TAU_ESCALATES_TO_RELEASE_CONTROL": "Let Tau connectivity mutate the software release registry.",
    "TAU_FAILOVER_UNGOVERNED": "Switch from Tau to native policy verification without governed equivalence.",
    "TAU_FAILOVER_PER_QUERY_SWITCH": (
        "Let one policy query choose a backend outside the epoch-bound profile."
    ),
    "TAU_QUANTITY_CONTRACT_OMITTED": "Omit scale, rounding, permanence, or recovery from Tau representation.",
    "TAU_REPRESENTATION_UNRESOLVED": "Evaluate a Tau value route without a resolved representation lane.",
    "TRANSFER_WRONG_CUSTODY_ROLE": "Permit a transfer outside the module account-role scope.",
    "UNPORTED_DEPENDENCY": "Add a runtime dependency with no typed port.",
    "UNKNOWN_INTENT": "Add an intent outside the closed intent registry.",
    "VERIFIER_MISMATCH_FAILS_OPEN": "Prefer one verifier result on disagreement.",
    "VERIFIER_PROFILE_SUBSTITUTION": "Permit a valid receipt under another profile.",
    "ZRPF_BYPASSES_SHARED_COMMIT": "Give an accepted ZRPF root a separate durable writer.",
    "ZRPF_BINDING_PATH_UNREALIZABLE": (
        "Name a ZRPF equality token whose declared schema path does not exist."
    ),
    "ZRPF_WITNESS_OMITTED": "Permit a ZRPF admission without its verified journal.",
    "ZRPF_WITNESS_CANDIDATE_SUBSTITUTION": "Publish a candidate that differs from the verified ZRPF journal.",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _with_id(row_id: str, value: dict[str, Any]) -> dict[str, Any]:
    return {"id": row_id, **copy.deepcopy(value)}


def _header_sections(repo_root: Path) -> dict[str, Any]:
    parent_path = repo_root / "docs/research/PRODUCTION_READINESS_ARCHITECTURE_TOURNAMENT_V1.json"
    return {
        "schema": contract.SCHEMA,
        "status": "STRUCTURALLY_SPECIFIED_RESEARCH_ONLY",
        "production_promotion": False,
        "architecture_selected": False,
        "reviewed_subject": contract.REVIEWED_SUBJECT,
        "parent_tournament": {
            "path": parent_path.relative_to(repo_root).as_posix(),
            "sha256": _sha256(parent_path),
            "candidate_id": contract.PARENT_CANDIDATE_ID,
            "selection_status": "RESEARCH_LEADER_UNSELECTED",
        },
        "source_pins": [
            {"id": path, "sha256": _sha256(repo_root / path)}
            for path in contract.EXPECTED_SOURCE_PATHS
        ],
        "verifier_bootstrap": copy.deepcopy(contract.EXPECTED_VERIFIER_BOOTSTRAP),
    }


def _registry_sections() -> dict[str, Any]:
    return {
        "command_registry": [
            {"id": command_id, "source_semantics_id": command_id}
            for command_id in sorted(contract.EXPECTED_COMMANDS)
        ],
        "command_payload_schemas": [
            _with_id(command_id, contract.EXPECTED_COMMAND_PAYLOAD_SCHEMAS[command_id])
            for command_id in sorted(contract.EXPECTED_COMMAND_PAYLOAD_SCHEMAS)
        ],
        "intent_registry": [
            {
                "id": intent_id,
                "owner": "SETTLEMENT_KERNEL",
                "stage": "PROPOSED",
                "external_effect": intent_id == "OUTBOX_ENQUEUE",
            }
            for intent_id in sorted(contract.EXPECTED_INTENTS)
        ],
        "intent_payload_schemas": [
            _with_id(intent_id, contract.EXPECTED_INTENT_PAYLOAD_SCHEMAS[intent_id])
            for intent_id in sorted(contract.EXPECTED_INTENT_PAYLOAD_SCHEMAS)
        ],
        "intent_capabilities": [
            _with_id(capability_id, contract.EXPECTED_INTENT_CAPABILITIES[capability_id])
            for capability_id in sorted(contract.EXPECTED_INTENT_CAPABILITIES)
        ],
        "view_registry": [
            _with_id(view_id, contract.EXPECTED_VIEW_SPECS[view_id])
            for view_id in sorted(contract.EXPECTED_VIEW_SPECS)
        ],
        "route_constraint_registry": [
            {
                "id": constraint_id,
                "meaning": contract.EXPECTED_ROUTE_CONSTRAINT_SPECS[constraint_id],
            }
            for constraint_id in sorted(contract.EXPECTED_ROUTE_CONSTRAINT_SPECS)
        ],
        "type_registry": [
            copy.deepcopy(contract.EXPECTED_TYPE_SPECS[type_id])
            for type_id in sorted(contract.EXPECTED_TYPE_SPECS)
        ],
        "state_domains": [
            {
                "id": domain_id,
                "semantic_owner": owner,
                "durable_writers": ["ZENO_LEDGER"],
            }
            for domain_id, owner in contract.EXPECTED_STATE_OWNERS.items()
        ],
        "module_descriptors": [
            _with_id(module_id, contract.EXPECTED_MODULE_SPECS[module_id])
            for module_id in sorted(contract.EXPECTED_MODULE_SPECS)
        ],
        "port_contracts": [
            _with_id(port_id, contract.EXPECTED_PORT_SPECS[port_id])
            for port_id in sorted(contract.EXPECTED_PORT_SPECS)
        ],
        "routes": [
            _with_id(command_id, contract.EXPECTED_ROUTE_SPECS[command_id])
            for command_id in sorted(contract.EXPECTED_ROUTE_SPECS)
        ],
    }


def _assurance_sections() -> dict[str, Any]:
    return {
        "composition_contract": copy.deepcopy(contract.EXPECTED_COMPOSITION),
        "evidence_gates": [
            {
                "id": gate_id,
                "minimum_grade": minimum_grade,
                "structural_status": structural_status,
                "evidence_status": "UNVERIFIED",
                "evidence_refs": [],
            }
            for gate_id, (minimum_grade, structural_status) in contract.EVIDENCE_GATES.items()
        ],
        "named_mutants": [
            {
                "id": mutant_id,
                "description": MUTANT_DESCRIPTIONS[mutant_id],
                "expected_detection": "V2 exact structural checker rejects the mutation.",
            }
            for mutant_id in sorted(contract.EXPECTED_MUTANTS)
        ],
        "nonclaims": copy.deepcopy(list(contract.EXPECTED_NONCLAIMS)),
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    return {
        **_header_sections(repo_root),
        **_registry_sections(),
        **_assurance_sections(),
    }


def render(document: dict[str, Any]) -> str:
    return json.dumps(document, indent=2, sort_keys=False) + "\n"


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.write and args.check:
        raise SystemExit("--write and --check are mutually exclusive")
    expected = render(build_document())
    if args.write:
        args.output.write_text(expected, encoding="utf-8")
        print(args.output)
        return 0
    if args.check:
        try:
            actual = args.output.read_text(encoding="utf-8")
        except OSError as exc:
            print(f"candidate render check: FAIL: {exc}", file=sys.stderr)
            return 1
        if actual != expected:
            print("candidate render check: FAIL: generated bytes differ", file=sys.stderr)
            return 1
        print("candidate render check: PASS")
        return 0
    sys.stdout.write(expected)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
