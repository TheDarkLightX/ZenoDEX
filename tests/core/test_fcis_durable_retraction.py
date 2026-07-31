from __future__ import annotations

import inspect
from dataclasses import replace
from pathlib import Path

import pytest

import src.core.fcis_durable_retraction as durable_retraction
from src.core.fcis_durable_retraction import (
    AuthorizedHistoryV1,
    ClientObservationV1,
    CommitAttemptV1,
    CommitResolutionV1,
    CrashPointV1,
    DeliveryClassV1,
    DestinationReceiptV1,
    DestinationResponseEvidenceV1,
    DestinationStateV1,
    DurableRetractionError,
    DurableSnapshotV1,
    ExternalHeadAuthorizationEvidenceV1,
    MigrationPhaseV1,
    OutboxEffectV1,
    OutboxRowV1,
    PublicationAtomV1,
    ReopenAuthorizationV1,
    ReopenCodeV1,
    ReopenRejectV1,
    VerifiedDestinationReceiptV1,
    VerifiedExternalHeadAuthorizationV1,
    _destination_attestation_root,
    _external_attestation_root,
    _snapshot_root_without_cache,
    acknowledge_delivery,
    advance_authority_state,
    attempt_commit,
    authorize_reopened_snapshot,
    classify_retry,
    deliver_effect,
    derive_destination_idempotency_root,
    derive_destination_receipt_root,
    derive_effect_id,
    encode_history,
    initial_authority_state,
    migrate_snapshot,
    normalize_snapshot,
    reopen_snapshot,
    tagged_digest,
    verify_destination_response,
    verify_external_head_authorization,
)


class _TestOnlyAcceptingHeadVerifier:
    """Deterministic test premise; never suitable for a mounted shell."""

    """Test-only stand-in for the shell's authoritative verifier."""

    def verify_external_head_authorization(self, evidence: object, **_expected: object) -> object:
        return type(evidence) is ExternalHeadAuthorizationEvidenceV1


class _TestOnlyAcceptingDestinationVerifier:
    """Deterministic test premise; never suitable for a mounted shell."""

    """Test-only stand-in for destination delivery and receipt verification."""

    def __init__(self, adapter_profile_root: str | None = None) -> None:
        self.adapter_profile_root = adapter_profile_root

    def deliver_and_verify(self, effect: OutboxEffectV1) -> object:
        return _raw_destination_response(
            effect,
            adapter_profile_root=self.adapter_profile_root,
        )

    def verify_destination_response(
        self,
        response: DestinationResponseEvidenceV1,
        *,
        expected_effect: OutboxEffectV1,
    ) -> object:
        return (
            type(response) is DestinationResponseEvidenceV1
            and type(expected_effect) is OutboxEffectV1
        )


_HEAD_VERIFIER = _TestOnlyAcceptingHeadVerifier()
_DESTINATION_VERIFIER = _TestOnlyAcceptingDestinationVerifier()


def _authority():
    return initial_authority_state(tagged_digest("profile/legacy"), tagged_digest("profile/target"))


def _empty_snapshot() -> DurableSnapshotV1:
    authority = _authority()
    return encode_history(
        AuthorizedHistoryV1(
            genesis_state_root=tagged_digest("state/genesis"),
            authority_epochs=(authority,),
            atoms=(),
            acks=(),
        )
    )


def _verified_external_authorization(
    snapshot: DurableSnapshotV1,
) -> VerifiedExternalHeadAuthorizationV1:
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    external_statement_root = tagged_digest("external/head-authorization")
    attestation_root = _external_attestation_root(
        snapshot_root=snapshot.snapshot_root,
        current_state_root=history.current_state_root,
        authority_state_root=history.authority.root,
        authority_epoch_index=history.authority.epoch_index,
        deployment_config_root=snapshot.deployment_config_root,
        verifier_profile_root=snapshot.verifier_profile_root,
        external_statement_root=external_statement_root,
        activation_epoch=0,
        expiration_epoch=None,
    )
    evidence = ExternalHeadAuthorizationEvidenceV1(
        snapshot_root=snapshot.snapshot_root,
        current_state_root=history.current_state_root,
        authority_state_root=history.authority.root,
        authority_epoch_index=history.authority.epoch_index,
        deployment_config_root=snapshot.deployment_config_root,
        verifier_profile_root=snapshot.verifier_profile_root,
        external_statement_root=external_statement_root,
        activation_epoch=0,
        expiration_epoch=None,
        attestation_root=attestation_root,
    )
    result = verify_external_head_authorization(
        evidence,
        verifier_adapter=_HEAD_VERIFIER,
        expected_snapshot_root=snapshot.snapshot_root,
        expected_current_state_root=history.current_state_root,
        expected_authority_state_root=history.authority.root,
        expected_authority_epoch_index=history.authority.epoch_index,
        expected_deployment_config_root=snapshot.deployment_config_root,
        expected_verifier_profile_root=snapshot.verifier_profile_root,
        current_epoch=history.authority.epoch_index,
    )
    assert type(result) is VerifiedExternalHeadAuthorizationV1
    return result


def _authorization(snapshot: DurableSnapshotV1) -> ReopenAuthorizationV1:
    verified = _verified_external_authorization(snapshot)
    evidence = ExternalHeadAuthorizationEvidenceV1(
        snapshot_root=verified.snapshot_root,
        current_state_root=verified.current_state_root,
        authority_state_root=verified.authority_state_root,
        authority_epoch_index=verified.authority_epoch_index,
        deployment_config_root=verified.deployment_config_root,
        verifier_profile_root=verified.verifier_profile_root,
        external_statement_root=verified.external_statement_root,
        activation_epoch=verified.activation_epoch,
        expiration_epoch=verified.expiration_epoch,
        attestation_root=verified.attestation_root,
    )
    result = authorize_reopened_snapshot(
        snapshot,
        external_authorization_evidence=evidence,
        verifier_adapter=_HEAD_VERIFIER,
    )
    assert type(result) is ReopenAuthorizationV1
    return result


def _attempt_commit(
    snapshot: object,
    authorization: object,
    atom: object,
    crash_point: object = CrashPointV1.NONE,
) -> CommitAttemptV1 | ReopenRejectV1:
    return attempt_commit(
        snapshot,
        authorization,
        atom,
        crash_point,
        authorization_verifier_adapter=_HEAD_VERIFIER,
    )


def _migrate_snapshot(
    snapshot: object,
    authorization: object,
    next_phase: object,
    transport_root: object,
) -> DurableSnapshotV1 | ReopenRejectV1:
    return migrate_snapshot(
        snapshot,
        authorization,
        next_phase,
        transport_root,
        authorization_verifier_adapter=_HEAD_VERIFIER,
    )


def _acknowledge_delivery(
    snapshot: object,
    authorization: object,
    receipt: object,
) -> DurableSnapshotV1 | ReopenRejectV1:
    return acknowledge_delivery(
        snapshot,
        authorization,
        receipt,
        authorization_verifier_adapter=_HEAD_VERIFIER,
        destination_verifier_adapter=_DESTINATION_VERIFIER,
    )


def _atom(
    snapshot: DurableSnapshotV1,
    *,
    label: str,
    nullifier_label: str | None = None,
    writer_root: str | None = None,
    commit_id: str | None = None,
    effect: bool = True,
) -> PublicationAtomV1:
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    authority = history.authority
    exact_commit_id = tagged_digest(f"commit/{label}") if commit_id is None else commit_id
    selected_writer = authority.active_profile_root if writer_root is None else writer_root
    payload_root = tagged_digest(f"payload/{label}")
    adapter_profile_root = tagged_digest("verifier/destination/research-v1")
    outbox = ()
    if effect:
        destination = "treasury"
        outbox = (
            OutboxEffectV1(
                effect_id=derive_effect_id(
                    commit_id=exact_commit_id,
                    ordinal=0,
                    destination=destination,
                    payload_root=payload_root,
                    writer_profile_root=selected_writer,
                    adapter_profile_root=adapter_profile_root,
                ),
                ordinal=0,
                destination=destination,
                payload_root=payload_root,
                adapter_profile_root=adapter_profile_root,
            ),
        )
    return PublicationAtomV1(
        sequence=len(history.atoms) + 1,
        commit_id=exact_commit_id,
        command_root=tagged_digest(f"command/{label}"),
        expected_pre_root=history.current_state_root,
        post_state_root=tagged_digest(f"state/{label}"),
        writer_profile_root=selected_writer,
        authority_epoch_index=authority.epoch_index,
        authority_state_root=authority.root,
        nullifier_root=tagged_digest(
            f"nullifier/{label}" if nullifier_label is None else nullifier_label
        ),
        response_root=tagged_digest(f"response/{label}"),
        receipt_root=tagged_digest(f"receipt/{label}"),
        decision_root=tagged_digest(f"decision/{label}"),
        bundle_root=tagged_digest(f"bundle/{label}"),
        replay_root=tagged_digest(f"replay/{label}"),
        outbox=outbox,
        deployment_config_root=snapshot.deployment_config_root,
        verifier_profile_root=snapshot.verifier_profile_root,
    )


def _raw_destination_response(
    effect,
    *,
    destination: str | None = None,
    payload_root: str | None = None,
    adapter_profile_root: str | None = None,
) -> DestinationResponseEvidenceV1:
    selected_destination = effect.destination if destination is None else destination
    selected_payload_root = effect.payload_root if payload_root is None else payload_root
    selected_adapter = (
        effect.adapter_profile_root if adapter_profile_root is None else adapter_profile_root
    )
    receipt_root = derive_destination_receipt_root(
        effect_id=effect.effect_id,
        destination=selected_destination,
        payload_root=selected_payload_root,
    )
    idempotency_root = derive_destination_idempotency_root(effect.effect_id)
    response_root = tagged_digest(f"raw-response/{effect.effect_id}")
    return DestinationResponseEvidenceV1(
        effect_id=effect.effect_id,
        destination=selected_destination,
        payload_root=selected_payload_root,
        destination_receipt_root=receipt_root,
        adapter_profile_root=selected_adapter,
        idempotency_root=idempotency_root,
        response_root=response_root,
        attestation_root=_destination_attestation_root(
            effect_id=effect.effect_id,
            destination=selected_destination,
            payload_root=selected_payload_root,
            destination_receipt_root=receipt_root,
            adapter_profile_root=selected_adapter,
            idempotency_root=idempotency_root,
            response_root=response_root,
        ),
    )


def _rehash(snapshot: DurableSnapshotV1, **changes: object) -> DurableSnapshotV1:
    provisional = replace(snapshot, **changes, snapshot_root="0" * 64)
    return replace(provisional, snapshot_root=_snapshot_root_without_cache(provisional))


def _commit(snapshot: DurableSnapshotV1, label: str) -> DurableSnapshotV1:
    result = _attempt_commit(snapshot, _authorization(snapshot), _atom(snapshot, label=label))
    assert type(result) is not ReopenRejectV1
    assert result.durable_resolution is CommitResolutionV1.NEWLY_COMMITTED
    assert result.client_observation is ClientObservationV1.CONFIRMED_NEW
    return result.snapshot


def test_encode_reopen_is_a_left_inverse_and_normalization_is_idempotent() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    assert encode_history(history) == snapshot
    first = normalize_snapshot(snapshot)
    assert type(first) is DurableSnapshotV1
    second = normalize_snapshot(first)
    assert second == first


def test_missing_surplus_duplicate_and_reordered_evidence_all_reject() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    rows = snapshot.evidence_rows
    mutants = (
        _rehash(snapshot, evidence_rows=rows[:-1]),
        _rehash(snapshot, evidence_rows=rows + (rows[0],)),
        _rehash(snapshot, evidence_rows=(rows[1], rows[0], *rows[2:])),
        _rehash(snapshot, evidence_rows=rows + (replace(rows[0], kind="foreign"),)),
    )
    for mutant in mutants:
        result = reopen_snapshot(mutant)
        assert type(result) is ReopenRejectV1
        assert result.code is ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE


def test_selected_digest_cannot_hide_a_crossed_evidence_row() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    rows = list(snapshot.evidence_rows)
    rows[0] = replace(rows[0], value_root=tagged_digest("foreign/value"))
    mutant = _rehash(snapshot, evidence_rows=tuple(rows))
    result = reopen_snapshot(mutant)
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE


def test_corrupt_cached_snapshot_root_rejects_before_reopen_authority() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    mutant = replace(snapshot, snapshot_root=tagged_digest("forged/snapshot"))
    result = reopen_snapshot(mutant)
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.SNAPSHOT_ROOT_MISMATCH


def test_reopen_does_not_restore_value_moving_authority_without_fresh_token() -> None:
    pre = _empty_snapshot()
    atom = _atom(pre, label="one")
    missing = _attempt_commit(pre, None, atom)
    assert missing.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    history = reopen_snapshot(pre)
    assert type(history) is AuthorizedHistoryV1
    statement_root = tagged_digest("external/self-selected")
    raw = ExternalHeadAuthorizationEvidenceV1(
        snapshot_root=pre.snapshot_root,
        current_state_root=history.current_state_root,
        authority_state_root=history.authority.root,
        authority_epoch_index=history.authority.epoch_index,
        deployment_config_root=pre.deployment_config_root,
        verifier_profile_root=pre.verifier_profile_root,
        external_statement_root=statement_root,
        activation_epoch=0,
        expiration_epoch=None,
        attestation_root=_external_attestation_root(
            snapshot_root=pre.snapshot_root,
            current_state_root=history.current_state_root,
            authority_state_root=history.authority.root,
            authority_epoch_index=history.authority.epoch_index,
            deployment_config_root=pre.deployment_config_root,
            verifier_profile_root=pre.verifier_profile_root,
            external_statement_root=statement_root,
            activation_epoch=0,
            expiration_epoch=None,
        ),
    )
    forged = authorize_reopened_snapshot(
        pre,
        external_authorization_evidence=raw,
        verifier_adapter=object(),
    )
    assert type(forged) is ReopenRejectV1


def test_same_request_retry_returns_original_response_without_second_commit() -> None:
    pre = _empty_snapshot()
    atom = _atom(pre, label="one")
    first = _attempt_commit(pre, _authorization(pre), atom)
    second = _attempt_commit(first.snapshot, _authorization(first.snapshot), atom)
    assert first.durable_resolution is CommitResolutionV1.NEWLY_COMMITTED
    assert second.durable_resolution is CommitResolutionV1.ALREADY_COMMITTED
    assert second.response_root == atom.response_root
    assert second.snapshot == first.snapshot


def test_two_distinct_commands_with_one_nullifier_cannot_both_commit() -> None:
    pre = _empty_snapshot()
    first_atom = _atom(pre, label="first", nullifier_label="shared")
    second_atom = _atom(pre, label="second", nullifier_label="shared")
    first = _attempt_commit(pre, _authorization(pre), first_atom)
    assert first.durable_resolution is CommitResolutionV1.NEWLY_COMMITTED
    second = _attempt_commit(first.snapshot, _authorization(first.snapshot), second_atom)
    assert second.durable_resolution in (
        CommitResolutionV1.STALE_STATE,
        CommitResolutionV1.DEFINITE_REJECTION,
    )
    reopened = reopen_snapshot(second.snapshot)
    assert type(reopened) is AuthorizedHistoryV1
    assert len(reopened.atoms) == 1
    assert reopened.atoms[0].commit_id == first_atom.commit_id


def test_commit_id_collision_is_definite_rejection() -> None:
    pre = _empty_snapshot()
    first_atom = _atom(pre, label="first")
    committed = _attempt_commit(pre, _authorization(pre), first_atom).snapshot
    colliding = _atom(
        pre,
        label="foreign",
        commit_id=first_atom.commit_id,
    )
    history = reopen_snapshot(committed)
    assert type(history) is AuthorizedHistoryV1
    result, response = classify_retry(history, colliding)
    assert result is CommitResolutionV1.DEFINITE_REJECTION
    assert response is None


def test_retry_identity_includes_the_exact_publication_sequence() -> None:
    pre = _empty_snapshot()
    committed_atom = _atom(pre, label="sequence-bound")
    committed = _attempt_commit(pre, _authorization(pre), committed_atom).snapshot
    history = reopen_snapshot(committed)
    assert type(history) is AuthorizedHistoryV1
    wrong_sequence = replace(committed_atom, sequence=committed_atom.sequence + 1)

    assert wrong_sequence.fingerprint != committed_atom.fingerprint
    resolution, response = classify_retry(history, wrong_sequence)
    assert resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert response is None


def test_retryable_absence_requires_the_exact_next_sequence_and_epoch() -> None:
    snapshot = _empty_snapshot()
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    atom = _atom(snapshot, label="retryable-index")

    wrong_sequence = replace(atom, sequence=atom.sequence + 1)
    sequence_resolution, sequence_response = classify_retry(history, wrong_sequence)
    assert sequence_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert sequence_response is None

    wrong_epoch = replace(atom, authority_epoch_index=history.authority.epoch_index + 1)
    epoch_resolution, epoch_response = classify_retry(history, wrong_epoch)
    assert epoch_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert epoch_response is None


def test_crash_refinement_exposes_only_exact_pre_or_exact_post() -> None:
    pre = _empty_snapshot()
    atom = _atom(pre, label="one")
    before = _attempt_commit(pre, _authorization(pre), atom, CrashPointV1.BEFORE_LINEARIZATION)
    after = _attempt_commit(pre, _authorization(pre), atom, CrashPointV1.AFTER_LINEARIZATION)
    assert before.snapshot == pre
    assert before.durable_resolution is CommitResolutionV1.ABSENT_RETRYABLE
    assert before.client_observation is ClientObservationV1.INDETERMINATE
    assert after.snapshot != pre
    assert after.durable_resolution is CommitResolutionV1.NEWLY_COMMITTED
    assert after.client_observation is ClientObservationV1.INDETERMINATE
    resolved = _attempt_commit(after.snapshot, _authorization(after.snapshot), atom)
    assert resolved.durable_resolution is CommitResolutionV1.ALREADY_COMMITTED


def test_outbox_delivery_requires_a_committed_ancestor() -> None:
    snapshot = _empty_snapshot()
    result = deliver_effect(
        snapshot,
        DestinationStateV1(()),
        tagged_digest("effect/not-committed"),
    )
    assert result.delivery_class is DeliveryClassV1.NOT_COMMITTED
    assert result.destination_state == DestinationStateV1(())


def test_lost_ack_retries_the_same_semantic_effect_identity() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    first = deliver_effect(
        snapshot,
        DestinationStateV1(()),
        effect.effect_id,
        adapter=_TestOnlyAcceptingDestinationVerifier(),
        lose_ack=True,
    )
    assert type(first) is not ReopenRejectV1
    assert first.delivery_class is DeliveryClassV1.INDETERMINATE_AFTER_ACCEPT
    assert first.receipt is not None
    retry = deliver_effect(
        snapshot,
        first.destination_state,
        effect.effect_id,
        adapter=_TestOnlyAcceptingDestinationVerifier(),
    )
    assert type(retry) is not ReopenRejectV1
    assert retry.delivery_class is DeliveryClassV1.ALREADY_ACCEPTED
    assert retry.receipt == first.receipt
    acknowledged = _acknowledge_delivery(snapshot, _authorization(snapshot), retry.receipt)
    assert type(acknowledged) is DurableSnapshotV1
    reopened = reopen_snapshot(acknowledged)
    assert type(reopened) is AuthorizedHistoryV1
    assert len(reopened.acks) == 1
    assert reopened.acks[0].effect_id == effect.effect_id


def test_crossed_destination_receipt_cannot_ack_an_effect() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    crossed = DestinationReceiptV1(
        effect_id=effect.effect_id,
        destination="foreign-destination",
        payload_root=effect.payload_root,
        receipt_root=derive_destination_receipt_root(
            effect_id=effect.effect_id,
            destination="foreign-destination",
            payload_root=effect.payload_root,
        ),
    )
    result = _acknowledge_delivery(snapshot, _authorization(snapshot), crossed)
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT


def test_forged_destination_receipt_root_is_not_admitted() -> None:
    snapshot = _commit(_empty_snapshot(), "one")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    with pytest.raises(DurableRetractionError, match="exact effect"):
        DestinationReceiptV1(
            effect_id=effect.effect_id,
            destination=effect.destination,
            payload_root=effect.payload_root,
            receipt_root=tagged_digest("receipt/forged"),
        )


def test_authority_lifecycle_is_exact_and_cannot_skip_a_gate() -> None:
    authority = _authority()
    with pytest.raises(DurableRetractionError, match="one edge"):
        advance_authority_state(
            authority,
            MigrationPhaseV1.DUAL_CHECK,
            tagged_digest("transport/skip"),
        )


def test_migration_preserves_history_and_disables_old_writer_after_switch() -> None:
    snapshot = _commit(_empty_snapshot(), "legacy-commit")
    phases = (
        MigrationPhaseV1.SHADOW_REPLAY,
        MigrationPhaseV1.DUAL_CHECK,
        MigrationPhaseV1.QUIESCED,
        MigrationPhaseV1.AUTHORITY_SWITCH,
    )
    for phase in phases:
        migrated = _migrate_snapshot(
            snapshot,
            _authorization(snapshot),
            phase,
            tagged_digest(f"transport/{phase.value}"),
        )
        assert type(migrated) is DurableSnapshotV1
        snapshot = migrated
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    assert len(history.atoms) == 1
    assert history.authority.phase is MigrationPhaseV1.AUTHORITY_SWITCH
    old_writer = history.authority.legacy_profile_root
    old_atom = _atom(snapshot, label="old-writer", writer_root=old_writer)
    old_result = _attempt_commit(snapshot, _authorization(snapshot), old_atom)
    assert old_result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    target_atom = _atom(snapshot, label="target-writer")
    target_result = _attempt_commit(snapshot, _authorization(snapshot), target_atom)
    assert target_result.durable_resolution is CommitResolutionV1.NEWLY_COMMITTED
    reopened = reopen_snapshot(target_result.snapshot)
    assert type(reopened) is AuthorizedHistoryV1
    assert len(reopened.atoms) == 2
    assert reopened.atoms[0].authority_epoch_index == 0
    assert reopened.atoms[1].authority_epoch_index == 4


def test_quiesced_phase_allows_no_value_moving_writer() -> None:
    snapshot = _empty_snapshot()
    for phase in (
        MigrationPhaseV1.SHADOW_REPLAY,
        MigrationPhaseV1.DUAL_CHECK,
        MigrationPhaseV1.QUIESCED,
    ):
        migrated = _migrate_snapshot(
            snapshot,
            _authorization(snapshot),
            phase,
            tagged_digest(f"transport/{phase.value}"),
        )
        assert type(migrated) is DurableSnapshotV1
        snapshot = migrated
    atom = _atom(
        snapshot,
        label="quiesced",
        writer_root=tagged_digest("profile/legacy"),
    )
    result = _attempt_commit(snapshot, _authorization(snapshot), atom)
    assert result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION


def test_boolean_integer_aliases_are_rejected() -> None:
    snapshot = _empty_snapshot()
    with pytest.raises(DurableRetractionError, match="exact int"):
        replace(_atom(snapshot, label="one"), sequence=True)


def test_dr_auth_01_self_selected_external_root_is_rejected() -> None:
    snapshot = _empty_snapshot()
    assert (
        "external_authorization_root"
        not in inspect.signature(authorize_reopened_snapshot).parameters
    )
    result = authorize_reopened_snapshot(
        snapshot,
        external_authorization_evidence=object(),
        verifier_adapter=_HEAD_VERIFIER,
    )
    assert type(result) is ReopenRejectV1


def test_dr_auth_02_changed_head_invalidates_the_old_verified_authorization() -> None:
    pre = _empty_snapshot()
    old_authorization = _authorization(pre)
    changed = _commit(pre, "changed-head")
    atom = _atom(changed, label="stale-authorization")
    result = _attempt_commit(changed, old_authorization, atom)
    assert result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert result.snapshot == changed


def test_dr_auth_03_cross_deployment_authorization_is_rejected() -> None:
    snapshot = _empty_snapshot()
    foreign = encode_history(
        AuthorizedHistoryV1(
            genesis_state_root=snapshot.genesis_state_root,
            authority_epochs=snapshot.authority_epochs,
            atoms=(),
            acks=(),
            deployment_config_root=tagged_digest("deployment/foreign"),
            verifier_profile_root=tagged_digest("verifier/foreign"),
        )
    )
    foreign_authorization = _authorization(foreign)
    result = _attempt_commit(
        snapshot, foreign_authorization, _atom(snapshot, label="cross-deployment")
    )
    assert result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert result.snapshot == snapshot


def test_dr_auth_04_cross_epoch_authorization_is_rejected() -> None:
    snapshot = _empty_snapshot()
    old_authorization = _authorization(snapshot)
    migrated = _migrate_snapshot(
        snapshot,
        old_authorization,
        MigrationPhaseV1.SHADOW_REPLAY,
        tagged_digest("transport/cross-epoch"),
    )
    assert type(migrated) is DurableSnapshotV1
    result = _attempt_commit(migrated, old_authorization, _atom(migrated, label="cross-epoch"))
    assert result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert result.snapshot == migrated


def test_dr_ack_01_local_receipt_digest_without_delivery_is_rejected() -> None:
    snapshot = _commit(_empty_snapshot(), "ack-without-delivery")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    forged = DestinationReceiptV1(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        receipt_root=derive_destination_receipt_root(
            effect_id=effect.effect_id,
            destination=effect.destination,
            payload_root=effect.payload_root,
        ),
    )
    result = _acknowledge_delivery(snapshot, _authorization(snapshot), forged)
    assert type(result) is ReopenRejectV1
    assert snapshot == _commit(_empty_snapshot(), "ack-without-delivery")


def test_dr_ack_02_cross_effect_verified_receipt_is_rejected() -> None:
    first = _commit(_empty_snapshot(), "first-effect")
    second = _commit(_empty_snapshot(), "second-effect")
    first_history = reopen_snapshot(first)
    assert type(first_history) is AuthorizedHistoryV1
    effect = first_history.atoms[0].outbox[0]
    delivery = deliver_effect(
        first,
        DestinationStateV1(()),
        effect.effect_id,
        adapter=_TestOnlyAcceptingDestinationVerifier(),
    )
    assert type(delivery) is not ReopenRejectV1
    assert type(delivery.receipt) is VerifiedDestinationReceiptV1
    result = _acknowledge_delivery(second, _authorization(second), delivery.receipt)
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE
    assert second == _commit(_empty_snapshot(), "second-effect")


def test_dr_ack_03_cross_destination_payload_and_verifier_are_rejected() -> None:
    snapshot = _commit(_empty_snapshot(), "receipt-bindings")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    for response in (
        _raw_destination_response(effect, destination="foreign-destination"),
        _raw_destination_response(effect, payload_root=tagged_digest("payload/foreign")),
        _raw_destination_response(
            effect,
            adapter_profile_root=tagged_digest("verifier/foreign"),
        ),
    ):
        verified = verify_destination_response(
            response,
            verifier_adapter=_DESTINATION_VERIFIER,
            expected_effect=effect,
            expected_adapter_profile_root=effect.adapter_profile_root,
            expected_idempotency_root=derive_destination_idempotency_root(effect.effect_id),
        )
        assert type(verified) is ReopenRejectV1
        assert verified.code is ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT
    assert snapshot == _commit(_empty_snapshot(), "receipt-bindings")


def test_dr_bound_01_outbox_ordinal_is_u32_and_rejects_boolean_alias() -> None:
    fields = dict(
        effect_id=tagged_digest("effect/bounds"),
        commit_id=tagged_digest("commit/bounds"),
        destination="treasury",
        payload_root=tagged_digest("payload/bounds"),
        adapter_profile_root=tagged_digest("verifier/destination/research-v1"),
    )
    OutboxRowV1(ordinal=2**32 - 1, **fields)
    with pytest.raises(DurableRetractionError, match="ordinal"):
        OutboxRowV1(ordinal=2**32, **fields)
    with pytest.raises(DurableRetractionError, match="exact int"):
        OutboxRowV1(ordinal=True, **fields)


def test_dr_bound_02_string_crash_point_is_a_typed_rejection() -> None:
    snapshot = _empty_snapshot()
    atom = _atom(snapshot, label="string-crash-point")
    result = _attempt_commit(
        snapshot,
        _authorization(snapshot),
        atom,
        crash_point="BEFORE_LINEARIZATION",
    )
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.WRONG_EXACT_TYPE


def test_dr_bound_03_oversized_redundant_table_is_rejected_at_admission() -> None:
    snapshot = _commit(_empty_snapshot(), "oversized-table")
    with pytest.raises(DurableRetractionError, match="evidence_rows"):
        replace(snapshot, evidence_rows=snapshot.evidence_rows * 10_000)


def test_dr_lean_01_reopen_preserves_partial_rejection_semantics() -> None:
    source = Path("lean-mathlib/Proofs/FCISDurableRetraction.lean").read_text()
    assert "reopen : D → Except Reject A" in source


def test_dr_esso_01_authorization_requires_a_verified_environment_grant() -> None:
    source = Path("formal/esso/fcis_durable_retraction_v1.yaml").read_text()
    assert "authorize_reopened_head" not in source
    assert "verified_external_grant" in source


def test_dr_auth_00_raw_evidence_cannot_mint_a_verified_grant() -> None:
    snapshot = _empty_snapshot()
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    statement_root = tagged_digest("external/raw-without-verifier")
    raw = ExternalHeadAuthorizationEvidenceV1(
        snapshot_root=snapshot.snapshot_root,
        current_state_root=history.current_state_root,
        authority_state_root=history.authority.root,
        authority_epoch_index=history.authority.epoch_index,
        deployment_config_root=snapshot.deployment_config_root,
        verifier_profile_root=snapshot.verifier_profile_root,
        external_statement_root=statement_root,
        activation_epoch=0,
        expiration_epoch=None,
        attestation_root=_external_attestation_root(
            snapshot_root=snapshot.snapshot_root,
            current_state_root=history.current_state_root,
            authority_state_root=history.authority.root,
            authority_epoch_index=history.authority.epoch_index,
            deployment_config_root=snapshot.deployment_config_root,
            verifier_profile_root=snapshot.verifier_profile_root,
            external_statement_root=statement_root,
            activation_epoch=0,
            expiration_epoch=None,
        ),
    )
    result = verify_external_head_authorization(
        raw,
        verifier_adapter=object(),
        expected_snapshot_root=snapshot.snapshot_root,
        expected_current_state_root=history.current_state_root,
        expected_authority_state_root=history.authority.root,
        expected_authority_epoch_index=history.authority.epoch_index,
        expected_deployment_config_root=snapshot.deployment_config_root,
        expected_verifier_profile_root=snapshot.verifier_profile_root,
        current_epoch=history.authority.epoch_index,
    )
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.UNVERIFIED_AUTHORIZATION


def test_dr_auth_00a_module_tokens_cannot_be_imported_to_mint_authority() -> None:
    forbidden = (
        "_HEAD_AUTHORIZATION_TOKEN_V1",
        "_EXTERNAL_AUTHORIZATION_GRANT_TOKEN_V1",
        "_VERIFIED_EXTERNAL_AUTHORIZATION_TOKEN_V1",
        "_VERIFIED_DESTINATION_RECEIPT_TOKEN_V1",
    )
    assert all(not hasattr(durable_retraction, name) for name in forbidden)


def test_dr_auth_00b_commit_reverifies_the_authorization_at_point_of_use() -> None:
    snapshot = _empty_snapshot()
    authorization = _authorization(snapshot)
    atom = _atom(snapshot, label="fresh-verifier-required")
    result = attempt_commit(
        snapshot,
        authorization,
        atom,
        authorization_verifier_adapter=object(),
    )
    assert type(result) is not ReopenRejectV1
    assert result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert result.snapshot == snapshot


def test_dr_auth_00c_verifier_result_is_bound_to_requested_subject() -> None:
    snapshot = _empty_snapshot()
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    statement_root = tagged_digest("external/grant-subject")
    raw = ExternalHeadAuthorizationEvidenceV1(
        snapshot_root=snapshot.snapshot_root,
        current_state_root=history.current_state_root,
        authority_state_root=history.authority.root,
        authority_epoch_index=history.authority.epoch_index,
        deployment_config_root=snapshot.deployment_config_root,
        verifier_profile_root=snapshot.verifier_profile_root,
        external_statement_root=statement_root,
        activation_epoch=0,
        expiration_epoch=None,
        attestation_root=_external_attestation_root(
            snapshot_root=snapshot.snapshot_root,
            current_state_root=history.current_state_root,
            authority_state_root=history.authority.root,
            authority_epoch_index=history.authority.epoch_index,
            deployment_config_root=snapshot.deployment_config_root,
            verifier_profile_root=snapshot.verifier_profile_root,
            external_statement_root=statement_root,
            activation_epoch=0,
            expiration_epoch=None,
        ),
    )
    result = verify_external_head_authorization(
        raw,
        verifier_adapter=_HEAD_VERIFIER,
        expected_snapshot_root=tagged_digest("foreign/requested-snapshot"),
        expected_current_state_root=history.current_state_root,
        expected_authority_state_root=history.authority.root,
        expected_authority_epoch_index=history.authority.epoch_index,
        expected_deployment_config_root=snapshot.deployment_config_root,
        expected_verifier_profile_root=snapshot.verifier_profile_root,
        current_epoch=history.authority.epoch_index,
    )
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.NONCANONICAL_LAYOUT


def test_dr_ack_00a_acknowledgment_reverifies_the_destination_at_point_of_use() -> None:
    snapshot = _commit(_empty_snapshot(), "fresh-destination-verifier")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    delivery = deliver_effect(
        snapshot,
        DestinationStateV1(()),
        effect.effect_id,
        adapter=_DESTINATION_VERIFIER,
    )
    assert type(delivery) is not ReopenRejectV1
    assert type(delivery.receipt) is VerifiedDestinationReceiptV1
    result = acknowledge_delivery(
        snapshot,
        _authorization(snapshot),
        delivery.receipt,
        authorization_verifier_adapter=_HEAD_VERIFIER,
        destination_verifier_adapter=object(),
    )
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT
    assert snapshot == _commit(_empty_snapshot(), "fresh-destination-verifier")


def test_dr_ack_00_committed_delivery_requires_a_shell_adapter() -> None:
    snapshot = _commit(_empty_snapshot(), "adapter-required")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    result = deliver_effect(snapshot, DestinationStateV1(()), effect.effect_id)
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT


def test_dr_ack_04_raw_adapter_response_cannot_be_admitted() -> None:
    snapshot = _commit(_empty_snapshot(), "raw-adapter-response")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]

    class RawAdapter:
        def deliver_and_verify(self, selected_effect: OutboxEffectV1) -> object:
            return _raw_destination_response(selected_effect)

    result = deliver_effect(
        snapshot,
        DestinationStateV1(()),
        effect.effect_id,
        adapter=RawAdapter(),
    )
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT


def test_dr_ack_05_lose_ack_requires_an_exact_boolean() -> None:
    snapshot = _commit(_empty_snapshot(), "bool-ack")
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    effect = history.atoms[0].outbox[0]
    result = deliver_effect(
        snapshot,
        DestinationStateV1(()),
        effect.effect_id,
        adapter=_TestOnlyAcceptingDestinationVerifier(),
        lose_ack=1,
    )
    assert type(result) is ReopenRejectV1
    assert result.code is ReopenCodeV1.WRONG_EXACT_TYPE


def test_dr_context_01_retry_classification_rejects_foreign_publication_context() -> None:
    snapshot = _empty_snapshot()
    atom = replace(
        _atom(snapshot, label="foreign-context"),
        deployment_config_root=tagged_digest("deployment/foreign-context"),
    )
    history = reopen_snapshot(snapshot)
    assert type(history) is AuthorizedHistoryV1
    resolution, response = classify_retry(history, atom)
    assert resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert response is None
    result = _attempt_commit(snapshot, _authorization(snapshot), atom)
    assert type(result) is not ReopenRejectV1
    assert result.durable_resolution is CommitResolutionV1.DEFINITE_REJECTION
    assert result.snapshot == snapshot


def test_dr_context_02_effect_identity_survives_adapter_profile_rotation() -> None:
    snapshot = _empty_snapshot()
    atom = _atom(snapshot, label="rotating-adapter")
    effect = atom.outbox[0]
    rotated = replace(effect, adapter_profile_root=tagged_digest("verifier/destination/rotated"))
    assert rotated.effect_id == effect.effect_id
    rotated_atom = replace(atom, outbox=(rotated,))
    assert rotated_atom.fingerprint != atom.fingerprint


def test_dr_migration_01_identical_writer_roots_are_rejected() -> None:
    root = tagged_digest("profile/identical")
    with pytest.raises(DurableRetractionError, match="must differ"):
        initial_authority_state(root, root)


def test_dr_migration_02_transition_binding_is_canonical() -> None:
    snapshot = _commit(_empty_snapshot(), "transition-binding")
    with pytest.raises(DurableRetractionError, match="canonically bound"):
        replace(
            snapshot,
            authority_epochs=(
                snapshot.authority_epochs[0],
                replace(
                    advance_authority_state(
                        snapshot.authority_epochs[0],
                        MigrationPhaseV1.SHADOW_REPLAY,
                        tagged_digest("transport/transition-binding"),
                    ),
                    transition_root=tagged_digest("migration/forged-transition"),
                ),
            ),
        )


def test_dr_input_01_malformed_inputs_return_typed_rejections() -> None:
    snapshot = _empty_snapshot()
    atom = _atom(snapshot, label="malformed-inputs")
    assert type(_attempt_commit(object(), _authorization(snapshot), atom)) is ReopenRejectV1
    assert type(_attempt_commit(snapshot, _authorization(snapshot), object())) is ReopenRejectV1
    with pytest.raises(DurableRetractionError, match="wrong snapshot type"):
        CommitAttemptV1(
            snapshot=object(),
            durable_resolution=CommitResolutionV1.DEFINITE_REJECTION,
            client_observation=ClientObservationV1.CONFIRMED_REJECTION,
            response_root=None,
        )
