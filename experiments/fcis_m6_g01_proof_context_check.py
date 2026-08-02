"""Independent G01 proof-context checker and deterministic vector builder."""

from __future__ import annotations

import json
from pathlib import Path

from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_g01_proof_context import (
    FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1,
    G01ProofContextCodeV1,
    G01ProofContextRejectV1,
    G01ProofContextV1,
    build_g01_proof_context_v1,
    validate_g01_proof_context_v1,
)
from src.core.fcis_m6_profile_ids import SEMANTIC_ALLOCATOR_PROFILE_ID_V1
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_G01_PROOF_CONTEXT_V1.json"


def _root(label: str) -> str:
    return f"0x{tagged_digest(label)}"


def build_context() -> G01ProofContextV1:
    return build_g01_proof_context_v1(
        chain_id="zenodex/research-chain",
        deployment_id="zenodex/research-deployment-v1",
        state_root=_root("g01/state"),
        configuration_root=_root("g01/configuration"),
        protocol_version="fcis-m6/protocol-v1",
        language_runtime_version="python-3.12/lean-4.27",
        verifier_implementation_id="fcis-verifier/research-v1",
        verification_key_digest=_root("g01/verification-key"),
        statement_schema_id="fcis/statement/public-inputs-v1",
        algorithm_profile_id=SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        history_genesis_authority_root=_root("g01/genesis-authority"),
        authority_epoch=7,
        not_before_epoch=5,
        expires_at_epoch=10,
    )


def _require_reject(value: object, code: G01ProofContextCodeV1, message: str) -> None:
    if type(value) is not G01ProofContextRejectV1:
        raise AssertionError(message)
    if value.code is not code:
        raise AssertionError(f"{message}: got {value.code.value}")


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    context = build_context()
    accepted = validate_g01_proof_context_v1(context, at_epoch=7)
    if type(accepted) is not G01ProofContextV1 or accepted != context:
        raise AssertionError("G01 rejected a valid active context")
    if not context.is_active_at(5) or not context.is_active_at(10):
        raise AssertionError("G01 boundary epochs are not inclusive")
    if context.is_active_at(4) or context.is_active_at(11):
        raise AssertionError("G01 accepted an out-of-window epoch")

    mutated_root = object.__new__(G01ProofContextV1)
    for field_name in context.__dataclass_fields__:
        object.__setattr__(mutated_root, field_name, object.__getattribute__(context, field_name))
    object.__setattr__(mutated_root, "state_root", _root("g01/foreign-state"))
    _require_reject(
        validate_g01_proof_context_v1(mutated_root),
        G01ProofContextCodeV1.CONTEXT_ROOT_MISMATCH,
        "G01 accepted a state-root substitution",
    )

    wrong_root = object.__new__(G01ProofContextV1)
    for field_name in context.__dataclass_fields__:
        object.__setattr__(wrong_root, field_name, object.__getattribute__(context, field_name))
    object.__setattr__(wrong_root, "context_root", _root("g01/foreign-context"))
    _require_reject(
        validate_g01_proof_context_v1(wrong_root),
        G01ProofContextCodeV1.CONTEXT_ROOT_MISMATCH,
        "G01 accepted a forged context root",
    )

    incomplete = object.__new__(G01ProofContextV1)
    _require_reject(
        validate_g01_proof_context_v1(incomplete),
        G01ProofContextCodeV1.INVALID_TEXT,
        "G01 accepted an incomplete exact context object",
    )
    _require_reject(
        validate_g01_proof_context_v1(context, at_epoch=True),
        G01ProofContextCodeV1.INVALID_EPOCH,
        "G01 accepted a boolean epoch",
    )
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: G01 proof-context vector is stale")
    return build_payload()


def build_payload() -> dict[str, object]:
    context = build_context()
    return {
        "schema": FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1,
        "context_root": context.context_root,
        "canonical_value": context.to_wire(),
        "authority_epoch": context.authority_epoch,
        "active_boundary": [context.not_before_epoch, context.expires_at_epoch],
        "mutants_rejected": [
            "state_root_substitution",
            "forged_context_root",
            "incomplete_exact_object",
            "boolean_epoch",
            "before_not_before_epoch",
            "after_expiry_epoch",
        ],
        "all_rejections_typed": True,
    }


def main() -> None:
    result = run_checks()
    print("G01_PROOF_CONTEXT_CHECKS_PASS", result["context_root"])


if __name__ == "__main__":
    main()
