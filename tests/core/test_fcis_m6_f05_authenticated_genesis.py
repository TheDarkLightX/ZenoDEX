"""Focused F05 authenticated-genesis relation tests."""

from __future__ import annotations

from experiments.fcis_m6_f05_authenticated_genesis_check import (
    build_genesis,
    build_pin,
)
from src.core.fcis_m6_f05_authenticated_genesis import (
    F05GenesisAcceptanceV1,
    F05GenesisCodeV1,
    F05GenesisRejectV1,
    authenticate_f05_genesis_v1,
    build_f05_genesis_v1,
    validate_f05_genesis_value,
)


def test_matching_genesis_and_deployment_pin_are_accepted() -> None:
    genesis = build_genesis()
    result = authenticate_f05_genesis_v1(genesis, build_pin(genesis))

    assert type(result) is F05GenesisAcceptanceV1
    assert result.genesis == genesis


def test_caller_selected_empty_or_foreign_genesis_is_rejected_by_pin() -> None:
    genesis = build_genesis()
    foreign = build_f05_genesis_v1(
        chain_id=genesis.chain_id,
        deployment_id=genesis.deployment_id,
        initial_state_root="0x" + "f" * 64,
        initial_configuration_root=genesis.initial_configuration_root,
        initial_authority_profile_id=genesis.initial_authority_profile_id,
        initial_authority_profile_root=genesis.initial_authority_profile_root,
        history_schema=genesis.history_schema,
        proof_context_policy_id=genesis.proof_context_policy_id,
        proof_context_policy_root=genesis.proof_context_policy_root,
        migration_policy_id=genesis.migration_policy_id,
        migration_policy_root=genesis.migration_policy_root,
    )

    result = authenticate_f05_genesis_v1(foreign, build_pin(genesis))

    assert type(result) is F05GenesisRejectV1
    assert result.code is F05GenesisCodeV1.STATE_MISMATCH


def test_forged_root_and_wrong_exact_type_return_typed_rejection() -> None:
    genesis = build_genesis()
    object.__setattr__(genesis, "genesis_root", "0x" + "e" * 64)

    forged = validate_f05_genesis_value(genesis)
    wrong_type = authenticate_f05_genesis_v1(object(), build_pin(build_genesis()))

    assert type(forged) is F05GenesisRejectV1
    assert forged.code is F05GenesisCodeV1.GENESIS_ROOT_MISMATCH
    assert type(wrong_type) is F05GenesisRejectV1
    assert wrong_type.code is F05GenesisCodeV1.WRONG_EXACT_TYPE
