from __future__ import annotations

from src.core.cross_shard_decision_certificate import (
    USER_STATUS_COMMIT_ACCEPTED,
    USER_STATUS_COMMIT_REJECTED,
    USER_STATUS_PENDING_DECISION,
    CrossShardDecisionCertificateV1,
    CrossShardDecisionParticipantV1,
    CrossShardDecisionState,
    CrossShardReceiptStatus,
    ParticipantPrepareState,
    ParticipantVisibilityState,
    build_cross_shard_decision_certificate,
    cross_shard_decision_certificate_hash,
    participant_shard_ids_hash,
    verify_cross_shard_decision_certificate_payload,
)


def _hash(label: str) -> str:
    return "0x" + label * 64


_SETTLEMENT_CERT_HASH = _hash("d")


def _participant(
    shard_id: str,
    *,
    prepared: bool,
    visible: bool,
) -> CrossShardDecisionParticipantV1:
    return CrossShardDecisionParticipantV1(
        shard_id=shard_id,
        prepare_state=(
            ParticipantPrepareState.PREPARED
            if prepared
            else ParticipantPrepareState.UNPREPARED
        ),
        visibility_state=(
            ParticipantVisibilityState.VISIBLE
            if visible
            else ParticipantVisibilityState.HIDDEN
        ),
    )


def _participants(
    *,
    prepared: bool,
    visible: bool,
) -> tuple[CrossShardDecisionParticipantV1, ...]:
    return (
        _participant("shard-a", prepared=prepared, visible=visible),
        _participant("shard-b", prepared=prepared, visible=visible),
    )


def _payload(
    *,
    receipt_status: CrossShardReceiptStatus = CrossShardReceiptStatus.MATCHED,
    decision: CrossShardDecisionState = CrossShardDecisionState.COMMIT,
    participants: tuple[CrossShardDecisionParticipantV1, ...] | None = None,
    decision_step: int = 1,
    deadline_step: int = 3,
) -> dict[str, object]:
    cert = build_cross_shard_decision_certificate(
        batch_id="batch-1",
        transfer_id="transfer-1",
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        receipt_status=receipt_status,
        decision=decision,
        participants=participants
        if participants is not None
        else _participants(prepared=True, visible=True),
        decision_step=decision_step,
        deadline_step=deadline_step,
    )
    return cert.to_payload()


def test_cross_shard_decision_certificate_accepts_commit_all_prepared_visible() -> None:
    payload = _payload()

    result = verify_cross_shard_decision_certificate_payload(
        payload,
        expected_participant_shard_ids=("shard-a", "shard-b"),
        expected_sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        current_step=1,
    )

    assert result.ok is True
    assert result.error is None
    assert result.decision == "commit"
    assert result.user_status == USER_STATUS_COMMIT_ACCEPTED
    assert result.participant_count == 2
    assert result.visible_participant_count == 2
    assert result.decision_step == 1
    assert result.deadline_step == 3
    assert result.participant_shard_ids_hash == participant_shard_ids_hash(
        ("shard-a", "shard-b")
    )
    assert result.certificate_hash == cross_shard_decision_certificate_hash(payload)


def test_cross_shard_decision_certificate_accepts_reject_all_hidden() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.REJECTED,
        decision=CrossShardDecisionState.REJECT,
        participants=_participants(prepared=False, visible=False),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result.ok is True
    assert result.user_status == USER_STATUS_COMMIT_REJECTED
    assert result.visible_participant_count == 0


def test_cross_shard_decision_certificate_accepts_pending_all_hidden() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.PENDING,
        decision=CrossShardDecisionState.PENDING,
        participants=_participants(prepared=True, visible=False),
    )

    result = verify_cross_shard_decision_certificate_payload(payload, current_step=2)

    assert result.ok is True
    assert result.user_status == USER_STATUS_PENDING_DECISION
    assert result.visible_participant_count == 0
    assert result.decision_step == 1
    assert result.deadline_step == 3


def test_cross_shard_decision_certificate_rejects_expired_pending_decision() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.PENDING,
        decision=CrossShardDecisionState.PENDING,
        participants=_participants(prepared=True, visible=False),
        decision_step=2,
        deadline_step=3,
    )

    result = verify_cross_shard_decision_certificate_payload(payload, current_step=3)

    assert result == result.__class__(
        ok=False,
        error="pending decision expired at deadline_step",
    )


def test_cross_shard_decision_certificate_rejects_pending_created_at_deadline() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.PENDING,
        decision=CrossShardDecisionState.PENDING,
        participants=_participants(prepared=True, visible=False),
        decision_step=3,
        deadline_step=3,
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="pending decision requires decision_step < deadline_step",
    )


def test_cross_shard_decision_certificate_rejects_future_dated_decision() -> None:
    payload = _payload(decision_step=2, deadline_step=3)

    result = verify_cross_shard_decision_certificate_payload(payload, current_step=1)

    assert result == result.__class__(
        ok=False,
        error="certificate.decision_step must be <= current_step",
    )


def test_cross_shard_decision_certificate_rejects_decision_after_deadline() -> None:
    try:
        _payload(decision_step=4, deadline_step=3)
    except ValueError as exc:
        assert str(exc) == "certificate.decision_step must be <= certificate.deadline_step"
        return
    raise AssertionError("expected constructor to reject decision_step after deadline_step")


def test_cross_shard_decision_certificate_rejects_missing_deadline_field() -> None:
    payload = _payload()
    del payload["deadline_step"]

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate.deadline_step must be an int",
    )


def test_cross_shard_decision_certificate_rejects_negative_decision_step() -> None:
    payload = _payload()
    payload["decision_step"] = -1

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate.decision_step must be non-negative",
    )


def test_cross_shard_decision_certificate_rejects_partial_visibility_counterexample() -> None:
    payload = _payload(
        decision=CrossShardDecisionState.PENDING,
        participants=(
            _participant("shard-a", prepared=True, visible=False),
            _participant("shard-b", prepared=True, visible=True),
        ),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="non-commit decision requires every participant hidden",
    )


def test_cross_shard_decision_certificate_rejects_commit_with_hidden_participant() -> None:
    payload = _payload(
        participants=(
            _participant("shard-a", prepared=True, visible=True),
            _participant("shard-b", prepared=True, visible=False),
        ),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="commit decision requires every participant visible",
    )


def test_cross_shard_decision_certificate_rejects_commit_with_unprepared_participant() -> None:
    payload = _payload(
        participants=(
            _participant("shard-a", prepared=True, visible=True),
            _participant("shard-b", prepared=False, visible=True),
        ),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="commit decision requires every participant prepared",
    )


def test_cross_shard_decision_certificate_rejects_commit_without_matched_receipt() -> None:
    payload = _payload(receipt_status=CrossShardReceiptStatus.REJECTED)

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="commit decision requires matched receipt status",
    )


def test_cross_shard_decision_certificate_rejects_reject_with_pending_receipt() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.PENDING,
        decision=CrossShardDecisionState.REJECT,
        participants=_participants(prepared=False, visible=False),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="reject decision requires rejected receipt status",
    )


def test_cross_shard_decision_certificate_rejects_pending_with_rejected_receipt() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.REJECTED,
        decision=CrossShardDecisionState.PENDING,
        participants=_participants(prepared=False, visible=False),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="pending decision requires pending receipt status",
    )


def test_cross_shard_decision_certificate_rejects_reject_with_matched_receipt() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.MATCHED,
        decision=CrossShardDecisionState.REJECT,
        participants=_participants(prepared=False, visible=False),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="reject decision requires rejected receipt status",
    )


def test_cross_shard_decision_certificate_rejects_pending_with_matched_receipt() -> None:
    payload = _payload(
        receipt_status=CrossShardReceiptStatus.MATCHED,
        decision=CrossShardDecisionState.PENDING,
        participants=_participants(prepared=True, visible=False),
    )

    result = verify_cross_shard_decision_certificate_payload(payload, current_step=1)

    assert result == result.__class__(
        ok=False,
        error="pending decision requires pending receipt status",
    )


def test_cross_shard_decision_certificate_rejects_participant_hash_mismatch() -> None:
    payload = _payload()
    payload["participant_shard_ids_hash"] = _hash("f")

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate.participant_shard_ids_hash mismatch",
    )


def test_cross_shard_decision_certificate_rejects_duplicate_participant_shard() -> None:
    payload = _payload(
        participants=(
            _participant("shard-a", prepared=True, visible=True),
            _participant("shard-a", prepared=True, visible=True),
        ),
    )

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="duplicate shard_id in certificate.participants",
    )


def test_cross_shard_decision_certificate_rejects_unsorted_participants() -> None:
    payload = _payload()
    payload["participants"] = list(reversed(payload["participants"]))

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate.participants must be sorted by shard_id",
    )


def test_cross_shard_decision_certificate_rejects_expected_settlement_hash_mismatch() -> None:
    payload = _payload()

    result = verify_cross_shard_decision_certificate_payload(
        payload,
        expected_sharded_settlement_certificate_hash=_hash("e"),
    )

    assert result == result.__class__(
        ok=False,
        error="certificate settlement hash does not match expected hash",
    )


def test_cross_shard_decision_certificate_rejects_unknown_certificate_field() -> None:
    payload = _payload()
    payload["unexpected"] = True

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="certificate has unsupported fields: unexpected",
    )


def test_cross_shard_decision_certificate_rejects_unknown_visibility_state() -> None:
    payload = _payload()
    payload["participants"][0]["visibility_state"] = "maybe-visible"

    result = verify_cross_shard_decision_certificate_payload(payload)

    assert result == result.__class__(
        ok=False,
        error="participant.visibility_state must be one of: visible, hidden",
    )


def test_cross_shard_decision_certificate_constructor_rejects_non_participant() -> None:
    try:
        CrossShardDecisionCertificateV1(
            batch_id="batch-1",
            transfer_id="transfer-1",
            sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
            participant_shard_ids_hash=participant_shard_ids_hash(("shard-a",)),
            receipt_status=CrossShardReceiptStatus.MATCHED,
            decision=CrossShardDecisionState.COMMIT,
            participants=("shard-a",),
            decision_step=1,
            deadline_step=3,
        )
    except TypeError as exc:
        assert str(exc) == "certificate.participants must contain participant records"
        return
    raise AssertionError("expected constructor to reject non-participant record")
