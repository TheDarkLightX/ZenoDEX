"""Focused J07 authority-switch and stale-token tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_j07_authority_switch_check import (
    build_f06_token,
    build_gate,
    run_checks,
)
from src.core.fcis_m6_j07_authority_switch import (
    J07Error,
    J07RejectCodeV1,
    J07SwitchSuccessV1,
    J07WriterAcceptedV1,
    J07WriterRejectV1,
    _mint_writer_token_v1,
    authorize_writer_v1,
    switch_authority_v1,
)


def _switch() -> tuple[object, object, object, object, J07SwitchSuccessV1]:
    reopened, genesis, migration_token, verifier = build_f06_token()
    gate = build_gate(migration_token)
    result = switch_authority_v1(
        gate,
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    assert type(result) is J07SwitchSuccessV1
    return reopened, genesis, migration_token, verifier, result


def test_j07_checker_passes() -> None:
    run_checks(check_vector=False)


def test_j07_switch_changes_only_authority_lineage_and_writer_profile() -> None:
    _, _, _, _, result = _switch()
    assert result.pre_context.phase.value == "QUIESCED"
    assert result.post_context.phase.value == "AUTHORITY_SWITCH"
    assert result.post_context.epoch_index == result.pre_context.epoch_index + 1
    assert result.pre_context.current_state_root == result.post_context.current_state_root
    assert result.pre_context.deployment_config_root == result.post_context.deployment_config_root
    assert result.pre_context.authority_state_root != result.post_context.authority_state_root
    assert result.pre_context.current_head_root != result.post_context.current_head_root
    assert result.pre_context.current_snapshot_root != result.post_context.current_snapshot_root
    assert result.post_context.allowed_writer_roots == (result.post_context.target_profile_root,)


def test_j07_old_writer_token_is_stale_and_target_token_is_accepted() -> None:
    _, _, _, _, result = _switch()
    old_token = _mint_writer_token_v1(result.pre_context, result.pre_context.legacy_profile_root)
    old_result = authorize_writer_v1(result.post_context, old_token)
    assert type(old_result) is J07WriterRejectV1
    assert old_result.code is J07RejectCodeV1.STALE_TOKEN

    target_token = _mint_writer_token_v1(
        result.post_context,
        result.post_context.target_profile_root,
    )
    target_result = authorize_writer_v1(result.post_context, target_token)
    assert type(target_result) is J07WriterAcceptedV1
    assert target_result.token_root == target_token.token_root


def test_j07_public_context_and_token_constructors_cannot_mint_authority() -> None:
    _, _, _, _, result = _switch()
    with pytest.raises(J07Error, match="verifier-owned"):
        replace(result.pre_context)
    token = _mint_writer_token_v1(result.post_context, result.post_context.target_profile_root)
    with pytest.raises(J07Error, match="verifier-owned"):
        replace(token)


def test_j07_registered_context_mutation_rejects_at_point_of_use() -> None:
    _, _, _, _, result = _switch()
    token = _mint_writer_token_v1(result.post_context, result.post_context.target_profile_root)
    object.__setattr__(
        result.post_context, "active_profile_root", result.post_context.legacy_profile_root
    )
    rejected = authorize_writer_v1(result.post_context, token)
    assert type(rejected) is J07WriterRejectV1
    assert rejected.code is J07RejectCodeV1.CONTEXT_REJECTED
