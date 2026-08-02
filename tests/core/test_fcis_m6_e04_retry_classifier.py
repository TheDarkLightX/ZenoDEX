"""Focused E04 total-partition, provenance, and transport-separation tests."""

from __future__ import annotations

from typing import cast

import pytest

from experiments.fcis_m6_e04_retry_classifier import (
    GENESIS_STATE_ROOT_V1,
    OTHER_STATE_ROOT_V1,
    OTHER_WRITER_ROOT_V1,
    POST_STATE_ROOT_V1,
    build_attempt,
    build_committed_state,
    build_nullifier_collision_state,
    build_reopen_receipt,
    build_state,
)
from src.core.fcis_m6_e03_unique_commit_port import _mint_e03_commit_identity_v1
from src.core.fcis_m6_e04_retry_classifier import (
    MAX_E04_REJECT_PATH_ITEMS_V1,
    E04AttemptV1,
    E04ClientKnowledgeV1,
    E04DurableOutcomeV1,
    E04Error,
    E04RejectCodeV1,
    E04RejectV1,
    E04ReopenReceiptV1,
    E04RetryResolutionV1,
    E04SequenceBindingV1,
    E04StoredCommitV1,
    E04StoredStateV1,
    _mint_e04_sequence_binding_v1,
    classify_e04_retry,
    is_verified_e04_attempt_v1,
    is_verified_e04_reopen_receipt_v1,
    is_verified_e04_stored_commit_v1,
    is_verified_e04_stored_state_v1,
)
from tools.build_fcis_m6_e03_database_uniqueness import build_candidate


def _resolution(result: object) -> E04RetryResolutionV1:
    assert type(result) is E04RetryResolutionV1
    return result


def _rejection(result: object, code: E04RejectCodeV1) -> E04RejectV1:
    assert type(result) is E04RejectV1
    rejection = result
    assert rejection.code is code
    return rejection


def _receipt(state: E04StoredStateV1) -> E04ReopenReceiptV1:
    return cast(E04ReopenReceiptV1, build_reopen_receipt(state))


def test_five_outcome_enum_is_closed_and_transport_is_separate() -> None:
    assert tuple(outcome.value for outcome in E04DurableOutcomeV1) == (
        "newly_committed",
        "already_committed",
        "absent_retryable",
        "stale_state",
        "definite_rejection",
    )
    assert tuple(knowledge.value for knowledge in E04ClientKnowledgeV1) == (
        "confirmed",
        "indeterminate",
    )


def test_absent_current_head_is_retryable_for_both_client_knowledge_values() -> None:
    attempt = build_attempt()
    state = build_state()
    receipt = _receipt(state)
    confirmed = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, receipt)
    )
    indeterminate = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.INDETERMINATE, receipt)
    )
    assert confirmed.outcome is E04DurableOutcomeV1.ABSENT_RETRYABLE
    assert indeterminate.outcome is confirmed.outcome
    assert indeterminate.attempt_root == confirmed.attempt_root
    assert indeterminate.snapshot_root == confirmed.snapshot_root
    assert indeterminate.client_knowledge is E04ClientKnowledgeV1.INDETERMINATE


def test_same_commit_and_same_full_fingerprint_is_already_committed() -> None:
    attempt = build_attempt()
    state = build_committed_state(attempt)
    result = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.INDETERMINATE, _receipt(state))
    )
    assert result.outcome is E04DurableOutcomeV1.ALREADY_COMMITTED
    assert result.matched_commit_id == attempt.commit.commit_id


def test_same_commit_and_changed_attempt_fingerprint_is_hard_rejection() -> None:
    original = build_attempt()
    state = build_committed_state(original)
    changed = build_attempt(expected_pre_root=OTHER_STATE_ROOT_V1)
    result = _resolution(
        classify_e04_retry(changed, state, E04ClientKnowledgeV1.CONFIRMED, _receipt(state))
    )
    assert result.outcome is E04DurableOutcomeV1.DEFINITE_REJECTION
    assert result.matched_commit_id is None


def test_consumed_nullifier_belonging_to_another_commit_is_rejected() -> None:
    attempt = build_attempt()
    state = build_nullifier_collision_state()
    result = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.INDETERMINATE, _receipt(state))
    )
    assert result.outcome is E04DurableOutcomeV1.DEFINITE_REJECTION


def test_changed_current_state_is_stale_before_head_authorization_checks() -> None:
    attempt = build_attempt()
    state = build_state(
        genesis_state_root=OTHER_STATE_ROOT_V1,
        current_state_root=OTHER_STATE_ROOT_V1,
    )
    result = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, _receipt(state))
    )
    assert result.outcome is E04DurableOutcomeV1.STALE_STATE


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    "state_overrides",
    (
        {"authority_epoch_index": 4},
        {"authority_state_root": "7" * 64},
        {"allowed_writer_roots": (OTHER_WRITER_ROOT_V1,)},
        {"verifier_profile_root": "7" * 64},
    ),
)
def test_changed_head_or_authority_context_is_rejected(
    state_overrides: dict[str, object],
) -> None:
    attempt = build_attempt()
    state = build_state(**state_overrides)
    result = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, _receipt(state))
    )
    assert result.outcome is E04DurableOutcomeV1.DEFINITE_REJECTION


def test_sequence_mismatch_is_rejected_after_current_root_matches() -> None:
    baseline = build_candidate()
    second_commit = _mint_e03_commit_identity_v1(
        sequence=2,
        commit_id="f" * 64,
        nullifier=baseline.nullifier,
        effects=baseline.effects,
    )
    attempt = build_attempt(commit=second_commit)
    state = build_state()
    result = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, _receipt(state))
    )
    assert result.outcome is E04DurableOutcomeV1.DEFINITE_REJECTION


def test_public_constructor_and_forged_state_do_not_create_verified_values() -> None:
    attempt = build_attempt()
    with pytest.raises(E04Error, match="verifier-owned"):
        E04AttemptV1(
            request_identity=attempt.request_identity,
            commit=attempt.commit,
            expected_pre_root=attempt.expected_pre_root,
            writer_profile_root=attempt.writer_profile_root,
            authority_state_root=attempt.authority_state_root,
            verifier_profile_root=attempt.verifier_profile_root,
            sequence_binding=attempt.sequence_binding,
        )

    state = build_state()
    forged = object.__new__(type(state))
    for name in (
        "genesis_state_root",
        "current_state_root",
        "authority_epoch_index",
        "authority_state_root",
        "allowed_writer_roots",
        "deployment_config_root",
        "verifier_profile_root",
        "commits",
        "snapshot_root",
    ):
        object.__setattr__(forged, name, object.__getattribute__(state, name))
    assert not is_verified_e04_stored_state_v1(forged)
    receipt = _receipt(state)
    _rejection(
        classify_e04_retry(attempt, forged, E04ClientKnowledgeV1.CONFIRMED, receipt),
        E04RejectCodeV1.UNVERIFIED_STATE,
    )


def test_mutating_verified_attempt_or_nested_state_invalidates_provenance() -> None:
    attempt = build_attempt()
    object.__setattr__(attempt, "expected_pre_root", OTHER_STATE_ROOT_V1)
    assert not is_verified_e04_attempt_v1(attempt)

    fresh_attempt = build_attempt()
    state = build_committed_state(fresh_attempt)
    receipt = _receipt(state)
    object.__setattr__(state.commits[0].attempt, "writer_profile_root", OTHER_WRITER_ROOT_V1)
    assert not is_verified_e04_stored_state_v1(state)
    clean_attempt = build_attempt()
    _rejection(
        classify_e04_retry(clean_attempt, state, E04ClientKnowledgeV1.CONFIRMED, receipt),
        E04RejectCodeV1.UNVERIFIED_STATE,
    )


def test_wrong_types_fail_closed_without_boolean_coercion() -> None:
    attempt = build_attempt()
    state = build_state()
    _rejection(
        classify_e04_retry(attempt, state, True, _receipt(state)),
        E04RejectCodeV1.WRONG_KNOWLEDGE_TYPE,
    )
    _rejection(
        classify_e04_retry(object(), state, E04ClientKnowledgeV1.CONFIRMED, _receipt(state)),
        E04RejectCodeV1.WRONG_ATTEMPT_TYPE,
    )
    _rejection(
        classify_e04_retry(attempt, object(), E04ClientKnowledgeV1.CONFIRMED, _receipt(state)),
        E04RejectCodeV1.WRONG_STATE_TYPE,
    )


def test_reopen_receipt_is_required_verified_and_subject_bound() -> None:
    attempt = build_attempt()
    state = build_state()
    receipt = _receipt(state)
    _rejection(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, object()),
        E04RejectCodeV1.WRONG_REOPEN_RECEIPT_TYPE,
    )
    forged = object.__new__(type(receipt))
    for name in (
        "snapshot_root",
        "current_state_root",
        "authority_epoch_index",
        "authority_state_root",
        "deployment_config_root",
        "verifier_profile_root",
        "datastore_profile_root",
        "read_version",
        "freshness_epoch",
        "receipt_root",
    ):
        object.__setattr__(forged, name, object.__getattribute__(receipt, name))
    assert not is_verified_e04_reopen_receipt_v1(forged)
    _rejection(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.CONFIRMED, forged),
        E04RejectCodeV1.UNVERIFIED_REOPEN_RECEIPT,
    )
    committed = build_committed_state()
    _rejection(
        classify_e04_retry(attempt, committed, E04ClientKnowledgeV1.CONFIRMED, receipt),
        E04RejectCodeV1.REOPEN_SUBJECT_MISMATCH,
    )


def test_rejection_path_has_an_exact_closed_capacity() -> None:
    E04RejectV1(
        code=E04RejectCodeV1.WRONG_ATTEMPT_TYPE,
        path=tuple(f"p{index}" for index in range(MAX_E04_REJECT_PATH_ITEMS_V1)),
    )
    with pytest.raises(E04Error, match="closed bound"):
        E04RejectV1(
            code=E04RejectCodeV1.WRONG_ATTEMPT_TYPE,
            path=tuple(f"p{index}" for index in range(MAX_E04_REJECT_PATH_ITEMS_V1 + 1)),
        )


def test_public_stored_commit_constructor_and_forgery_fail_closed() -> None:
    attempt = build_attempt()
    with pytest.raises(E04Error, match="verifier-owned"):
        E04StoredCommitV1(attempt=attempt, post_state_root=POST_STATE_ROOT_V1)
    stored = build_committed_state().commits[0]
    forged = object.__new__(type(stored))
    object.__setattr__(forged, "attempt", stored.attempt)
    object.__setattr__(forged, "post_state_root", stored.post_state_root)
    assert not is_verified_e04_stored_commit_v1(forged)


def test_sequence_binding_is_typed_and_crossed_coordinates_fail_closed() -> None:
    attempt = build_attempt()
    with pytest.raises(E04Error, match="verifier-owned"):
        E04SequenceBindingV1(
            request_expected_sequence=attempt.request_identity.expected_sequence,
            publication_sequence=attempt.commit.sequence,
            mapping_profile_root="4fae730960fd57820281426c3311efaff26237e9d576d040868d07220f66cabb",
        )
    crossed = _mint_e04_sequence_binding_v1(
        request_expected_sequence=attempt.request_identity.expected_sequence,
        publication_sequence=attempt.commit.sequence + 1,
    )
    object.__setattr__(attempt, "sequence_binding", crossed)
    assert not is_verified_e04_attempt_v1(attempt)


def test_resolution_wire_contains_attempt_and_snapshot_lineage() -> None:
    attempt = build_attempt()
    state = build_state()
    result = _resolution(
        classify_e04_retry(attempt, state, E04ClientKnowledgeV1.INDETERMINATE, _receipt(state))
    )
    wire = result.to_wire()
    assert wire["attempt_root"] == attempt.attempt_root
    assert wire["snapshot_root"] == build_state().snapshot_root
    assert wire["client_knowledge"] == "indeterminate"


def test_committed_state_root_is_post_state_and_not_pre_state() -> None:
    state = build_committed_state()
    assert state.current_state_root == POST_STATE_ROOT_V1
    assert state.current_state_root != GENESIS_STATE_ROOT_V1
