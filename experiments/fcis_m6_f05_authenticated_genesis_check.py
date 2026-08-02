"""Independent checker and canonical vector builder for F05."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_g01_proof_context_check import build_context
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_f01_history_atom import FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1
from src.core.fcis_m6_f05_authenticated_genesis import (
    FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1,
    F05GenesisAcceptanceV1,
    F05GenesisCodeV1,
    F05GenesisPinV1,
    F05GenesisRejectV1,
    F05GenesisV1,
    authenticate_f05_genesis_v1,
    build_f05_genesis_pin_v1,
    build_f05_genesis_v1,
    validate_f05_genesis_pin_value,
    validate_f05_genesis_value,
)
from src.core.fcis_m6_g01_proof_context import FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_F05_AUTHENTICATED_GENESIS_V1.json"
MIGRATION_POLICY_ID = "zenodex/fcis/m6/migration-policy/v1"
MIGRATION_POLICY_ROOT = f"0x{tagged_digest('f05/migration-policy')}"
AUTHORITY_PROFILE_ID = "zenodex/fcis/m6/authority/genesis-v1"


def _root(label: str) -> str:
    return f"0x{tagged_digest(f'f05/{label}')}"


def build_genesis() -> F05GenesisV1:
    context = build_context()
    return build_f05_genesis_v1(
        chain_id=context.chain_id,
        deployment_id=context.deployment_id,
        initial_state_root=context.state_root,
        initial_configuration_root=context.configuration_root,
        initial_authority_profile_id=AUTHORITY_PROFILE_ID,
        initial_authority_profile_root=context.history_genesis_authority_root,
        history_schema=FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1,
        proof_context_policy_id=FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1,
        proof_context_policy_root=context.context_root,
        migration_policy_id=MIGRATION_POLICY_ID,
        migration_policy_root=MIGRATION_POLICY_ROOT,
    )


def build_pin(genesis: F05GenesisV1 | None = None) -> F05GenesisPinV1:
    value = build_genesis() if genesis is None else genesis
    return build_f05_genesis_pin_v1(
        chain_id=value.chain_id,
        deployment_id=value.deployment_id,
        expected_genesis_root=value.genesis_root,
        expected_initial_state_root=value.initial_state_root,
        expected_configuration_root=value.initial_configuration_root,
        expected_authority_profile_id=value.initial_authority_profile_id,
        expected_authority_profile_root=value.initial_authority_profile_root,
        expected_history_schema=value.history_schema,
        expected_proof_context_policy_id=value.proof_context_policy_id,
        expected_proof_context_policy_root=value.proof_context_policy_root,
        expected_migration_policy_id=value.migration_policy_id,
        expected_migration_policy_root=value.migration_policy_root,
        activation_epoch=5,
    )


def _require_reject(value: object, code: F05GenesisCodeV1, message: str) -> F05GenesisRejectV1:
    if type(value) is not F05GenesisRejectV1:
        raise AssertionError(message)
    if value.code is not code:
        raise AssertionError(f"{message}: got {value.code.value}")
    return value


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    genesis = build_genesis()
    pin = build_pin(genesis)
    if type(validate_f05_genesis_value(genesis)) is not F05GenesisV1:
        raise AssertionError("F05 rejected its canonical genesis value")
    if type(validate_f05_genesis_pin_value(pin)) is not F05GenesisPinV1:
        raise AssertionError("F05 rejected its canonical deployment pin")
    accepted = authenticate_f05_genesis_v1(genesis, pin)
    if type(accepted) is not F05GenesisAcceptanceV1:
        raise AssertionError("F05 rejected the matching genesis/pin relation")
    if accepted.admission_root != derive_admission_root(genesis, pin):
        raise AssertionError("F05 admission root is not stable")

    forged_genesis = build_f05_genesis_v1(
        chain_id=genesis.chain_id,
        deployment_id=genesis.deployment_id,
        initial_state_root=_root("foreign-state"),
        initial_configuration_root=genesis.initial_configuration_root,
        initial_authority_profile_id=genesis.initial_authority_profile_id,
        initial_authority_profile_root=genesis.initial_authority_profile_root,
        history_schema=genesis.history_schema,
        proof_context_policy_id=genesis.proof_context_policy_id,
        proof_context_policy_root=genesis.proof_context_policy_root,
        migration_policy_id=genesis.migration_policy_id,
        migration_policy_root=genesis.migration_policy_root,
    )
    _require_reject(
        authenticate_f05_genesis_v1(forged_genesis, pin),
        F05GenesisCodeV1.STATE_MISMATCH,
        "F05 accepted a genesis with a foreign initial state root",
    )

    crossed_pin = build_f05_genesis_pin_v1(
        chain_id=genesis.chain_id,
        deployment_id=genesis.deployment_id,
        expected_genesis_root=_root("foreign-genesis"),
        expected_initial_state_root=genesis.initial_state_root,
        expected_configuration_root=genesis.initial_configuration_root,
        expected_authority_profile_id=genesis.initial_authority_profile_id,
        expected_authority_profile_root=genesis.initial_authority_profile_root,
        expected_history_schema=genesis.history_schema,
        expected_proof_context_policy_id=genesis.proof_context_policy_id,
        expected_proof_context_policy_root=genesis.proof_context_policy_root,
        expected_migration_policy_id=genesis.migration_policy_id,
        expected_migration_policy_root=genesis.migration_policy_root,
        activation_epoch=5,
    )
    _require_reject(
        authenticate_f05_genesis_v1(genesis, crossed_pin),
        F05GenesisCodeV1.GENESIS_PIN_MISMATCH,
        "F05 accepted a genesis root crossed with the deployment pin",
    )

    wrong_chain_pin = build_f05_genesis_pin_v1(
        chain_id="foreign-chain",
        deployment_id=pin.deployment_id,
        expected_genesis_root=pin.expected_genesis_root,
        expected_initial_state_root=pin.expected_initial_state_root,
        expected_configuration_root=pin.expected_configuration_root,
        expected_authority_profile_id=pin.expected_authority_profile_id,
        expected_authority_profile_root=pin.expected_authority_profile_root,
        expected_history_schema=pin.expected_history_schema,
        expected_proof_context_policy_id=pin.expected_proof_context_policy_id,
        expected_proof_context_policy_root=pin.expected_proof_context_policy_root,
        expected_migration_policy_id=pin.expected_migration_policy_id,
        expected_migration_policy_root=pin.expected_migration_policy_root,
        activation_epoch=5,
    )
    _require_reject(
        authenticate_f05_genesis_v1(genesis, wrong_chain_pin),
        F05GenesisCodeV1.CHAIN_MISMATCH,
        "F05 accepted a foreign chain pin",
    )

    wrong_authority_pin = build_f05_genesis_pin_v1(
        chain_id=pin.chain_id,
        deployment_id=pin.deployment_id,
        expected_genesis_root=pin.expected_genesis_root,
        expected_initial_state_root=pin.expected_initial_state_root,
        expected_configuration_root=pin.expected_configuration_root,
        expected_authority_profile_id="foreign-authority-profile",
        expected_authority_profile_root=pin.expected_authority_profile_root,
        expected_history_schema=pin.expected_history_schema,
        expected_proof_context_policy_id=pin.expected_proof_context_policy_id,
        expected_proof_context_policy_root=pin.expected_proof_context_policy_root,
        expected_migration_policy_id=pin.expected_migration_policy_id,
        expected_migration_policy_root=pin.expected_migration_policy_root,
        activation_epoch=5,
    )
    _require_reject(
        authenticate_f05_genesis_v1(genesis, wrong_authority_pin),
        F05GenesisCodeV1.AUTHORITY_PROFILE_MISMATCH,
        "F05 accepted a foreign authority profile pin",
    )

    object.__setattr__(genesis, "genesis_root", _root("forged-root"))
    _require_reject(
        validate_f05_genesis_value(genesis),
        F05GenesisCodeV1.GENESIS_ROOT_MISMATCH,
        "F05 accepted a forged genesis root",
    )
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: F05 authenticated-genesis vector is stale")
    return build_payload()


def derive_admission_root(genesis: F05GenesisV1, pin: F05GenesisPinV1) -> str:
    """Mirror the admission-root relation for the independent checker."""

    payload = {"genesis_root": genesis.genesis_root, "pin_root": pin.pin_root}
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zenodex/fcis/m6/f05/admission", version=1)
            + canonical_json_bytes(payload)
        ),
    )


def build_payload() -> dict[str, object]:
    genesis = build_genesis()
    pin = build_pin(genesis)
    accepted = authenticate_f05_genesis_v1(genesis, pin)
    if type(accepted) is not F05GenesisAcceptanceV1:
        raise AssertionError("F05 vector fixture is not accepted")
    return {
        "schema": FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1,
        "genesis": genesis.to_wire(),
        "pin": pin.to_wire(),
        "genesis_root": genesis.genesis_root,
        "pin_root": pin.pin_root,
        "admission_root": accepted.admission_root,
        "activation_epoch": pin.activation_epoch,
        "mutants_rejected": [
            "foreign initial state root",
            "genesis root crossed with deployment pin",
            "foreign chain pin",
            "foreign authority profile pin",
            "forged genesis root",
        ],
        "all_rejections_typed": True,
    }


def main() -> None:
    result = run_checks()
    print("F05_AUTHENTICATED_GENESIS_CHECKS_PASS", result["admission_root"])


if __name__ == "__main__":
    main()
