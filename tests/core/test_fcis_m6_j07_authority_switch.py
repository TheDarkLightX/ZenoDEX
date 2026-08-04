"""Focused J07 authority-switch and stale-token tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_j07_authority_switch_check import (
    build_f06_token,
    build_gate,
    build_writer_eligibility,
    run_checks,
)
from src.core.fcis_m6_j07_authority_switch import (
    J07Error,
    J07RejectCodeV1,
    J07SwitchRejectV1,
    J07SwitchSuccessV1,
    J07WriterRejectV1,
    _context_root,
    _mint_writer_token_v1,
    _register_context_v1,
    is_verified_authority_context_v1,
    issue_writer_token_v2,
    switch_authority_v1,
)
from src.core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityClaimV1,
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


def test_j07_v2_token_path_requires_the_versioned_admission_context() -> None:
    _, _, _, _, result = _switch()
    eligibility = build_writer_eligibility(
        result.post_context, result.post_context.target_profile_root
    )
    rejected = issue_writer_token_v2(result.post_context, eligibility)
    assert type(rejected) is J07WriterRejectV1
    assert rejected.code is J07RejectCodeV1.WRITER_ADMISSION_CONTEXT_REQUIRED


def test_j07_public_context_constructor_cannot_mint_authority() -> None:
    _, _, _, _, result = _switch()
    with pytest.raises(J07Error, match="verifier-owned"):
        replace(result.pre_context)


def test_j07_writer_token_cannot_be_minted_without_profile_eligibility() -> None:
    """Retain the direct context-plus-profile token-mint bypass witness."""

    _, _, _, _, result = _switch()
    with pytest.raises(J07Error, match="eligibility"):
        _mint_writer_token_v1(
            result.post_context,
            result.post_context.target_profile_root,
        )


def test_j07_registered_context_mutation_rejects_at_point_of_use() -> None:
    _, _, _, _, result = _switch()
    object.__setattr__(
        result.post_context, "active_profile_root", result.post_context.legacy_profile_root
    )
    assert not is_verified_authority_context_v1(result.post_context)


def test_j07_claim_data_cannot_substitute_for_verified_eligibility() -> None:
    _, _, _, _, result = _switch()
    receipt = build_writer_eligibility(result.post_context, result.post_context.target_profile_root)
    claim = receipt.claim
    assert type(claim) is WriterProfileEligibilityClaimV1
    rejected = issue_writer_token_v2(result.post_context, claim)
    assert type(rejected) is J07WriterRejectV1
    assert rejected.code is J07RejectCodeV1.WRITER_ADMISSION_CONTEXT_REQUIRED


def test_j07_v2_cannot_issue_from_crossed_eligibility() -> None:
    _, _, _, _, result = _switch()
    first = build_writer_eligibility(
        result.post_context,
        result.post_context.target_profile_root,
        promotion_subject_root="1" * 64,
    )
    rejected = issue_writer_token_v2(result.post_context, first)
    assert type(rejected) is J07WriterRejectV1
    assert rejected.code is J07RejectCodeV1.WRITER_ADMISSION_CONTEXT_REQUIRED


def test_j07_eligibility_bound_to_another_context_cannot_issue() -> None:
    _, _, _, _, result = _switch()
    stale = build_writer_eligibility(result.pre_context, result.post_context.target_profile_root)
    rejected = issue_writer_token_v2(result.post_context, stale)
    assert type(rejected) is J07WriterRejectV1
    assert rejected.code is J07RejectCodeV1.WRITER_ADMISSION_CONTEXT_REQUIRED


@pytest.mark.parametrize("field", ("current_state_root", "deployment_config_root"))
def test_j07_post_context_cannot_change_state_or_deployment(
    field: str,
) -> None:
    _, _, _, _, result = _switch()
    context = result.post_context
    replacement = "f" * 64
    object.__setattr__(context, field, replacement)
    object.__setattr__(context, "context_root", _context_root(context))
    with pytest.raises(J07Error, match="changed the"):
        context._validate_fields()


def test_j07_switch_result_rechecks_predecessor_profile_identity() -> None:
    _, _, _, _, result = _switch()
    post = result.post_context
    object.__setattr__(post, "legacy_profile_root", "f" * 64)
    object.__setattr__(post, "context_root", _context_root(post))
    _register_context_v1(post)
    with pytest.raises(J07Error, match="legacy profile identity"):
        result.to_wire()


@pytest.mark.parametrize(
    "rejection_type",
    (J07WriterRejectV1, J07SwitchRejectV1),
)
@pytest.mark.parametrize("path", ((), tuple(f"p{index}" for index in range(9)), ("x" * 65,)))
def test_j07_rejection_paths_are_bounded_and_typed(
    rejection_type: type[J07WriterRejectV1] | type[J07SwitchRejectV1],
    path: tuple[str, ...],
) -> None:
    with pytest.raises(J07Error):
        rejection_type(J07RejectCodeV1.CONTEXT_REJECTED, path)
