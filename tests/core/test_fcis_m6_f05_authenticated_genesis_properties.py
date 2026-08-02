"""Property-style F05 genesis/pin mutation tests."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_f05_authenticated_genesis_check import build_genesis, build_pin
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_f05_authenticated_genesis import (
    F05GenesisCodeV1,
    F05GenesisRejectV1,
    authenticate_f05_genesis_v1,
    build_f05_genesis_v1,
)

_LABELS = st.text(
    alphabet=st.characters(
        whitelist_categories=("Ll", "Lu", "Nd"),
        whitelist_characters="_-",
    ),
    min_size=1,
    max_size=32,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(label=_LABELS)  # type: ignore[untyped-decorator]
def test_generated_initial_state_roots_cannot_cross_the_pinned_genesis(label: str) -> None:
    genesis = build_genesis()
    foreign = build_f05_genesis_v1(
        chain_id=genesis.chain_id,
        deployment_id=genesis.deployment_id,
        initial_state_root=f"0x{tagged_digest(f'f05/property/{label}')}",
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
