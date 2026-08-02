"""I06 lost-ack recovery and stable-effect identity tests."""

from __future__ import annotations

from dataclasses import replace

from experiments.fcis_m6_i04_destination_dedup import (
    I04DedupContractCandidateV1,
    I04DedupModeV1,
    I04DestinationStateV1,
    I04VerifiedDedupContractV1,
    derive_dedup_contract_root,
    verify_dedup_contract_v1,
)
from experiments.fcis_m6_i06_lost_ack_recovery import (
    I06DeliveryStateV1,
    I06PhaseV1,
    I06RecoveryCodeV1,
    I06RecoveryOutcomeV1,
    I06RecoveryRejectV1,
    I06RecoveryResultV1,
    lose_response_after_destination_acceptance_v1,
    new_delivery_state_v1,
    redeliver_and_record_ack_v1,
)
from src.core.fcis_durable_retraction import (
    U32_MAX,
    OutboxEffectV1,
    derive_effect_id,
    tagged_digest,
)


def _effect(
    *,
    commit_label: str = "i06/commit",
    payload_label: str = "i06/payload",
    destination: str = "i06-destination",
) -> OutboxEffectV1:
    commit_id = tagged_digest(commit_label)
    writer_profile_root = tagged_digest("i06/writer")
    payload_root = tagged_digest(payload_label)
    adapter_profile_root = tagged_digest("i06/adapter")
    return OutboxEffectV1(
        effect_id=derive_effect_id(
            commit_id=commit_id,
            ordinal=0,
            destination=destination,
            payload_root=payload_root,
            writer_profile_root=writer_profile_root,
        ),
        ordinal=0,
        destination=destination,
        payload_root=payload_root,
        adapter_profile_root=adapter_profile_root,
    )


def _contract(effect: OutboxEffectV1) -> I04VerifiedDedupContractV1:
    contract_root = derive_dedup_contract_root(
        effect.destination,
        effect.adapter_profile_root,
        I04DedupModeV1.APPLICATION_RECEIPT_TABLE,
    )
    result = verify_dedup_contract_v1(
        I04DedupContractCandidateV1(
            destination=effect.destination,
            adapter_profile_root=effect.adapter_profile_root,
            mode=I04DedupModeV1.APPLICATION_RECEIPT_TABLE,
            contract_root=contract_root,
        )
    )
    if not isinstance(result, I04VerifiedDedupContractV1):
        raise AssertionError(f"expected verified contract, got {result!r}")
    return result


def _ready() -> I06DeliveryStateV1:
    effect = _effect()
    contract = _contract(effect)
    result = new_delivery_state_v1(contract, effect)
    if not isinstance(result, I06DeliveryStateV1):
        raise AssertionError(f"expected ready state, got {result!r}")
    return result


def _crashed() -> I06DeliveryStateV1:
    result = lose_response_after_destination_acceptance_v1(_ready())
    if not isinstance(result, I06DeliveryStateV1):
        raise AssertionError(f"expected crash state, got {result!r}")
    return result


def _recovered() -> I06DeliveryStateV1:
    result = redeliver_and_record_ack_v1(_crashed())
    if not isinstance(result, I06RecoveryResultV1):
        raise AssertionError(f"expected recovery result, got {result!r}")
    assert result.outcome is I06RecoveryOutcomeV1.REDELIVERED_ALREADY_ACCEPTED
    return result.state


def test_crash_keeps_destination_acceptance_and_loses_only_local_ack() -> None:
    ready = _ready()
    crashed = _crashed()

    assert ready.phase is I06PhaseV1.READY
    assert crashed.phase is I06PhaseV1.RESPONSE_LOST_AFTER_DESTINATION_ACCEPTANCE
    assert crashed.delivery_attempts == 1
    assert crashed.ack_journal is None
    assert len(crashed.destination_state.records) == 1
    assert crashed.destination_state.records[0].effect_id == ready.effect.effect_id
    assert crashed.effect.effect_id == ready.effect.effect_id


def test_redelivery_is_already_accepted_and_writes_one_durable_ack() -> None:
    crashed = _crashed()

    result = redeliver_and_record_ack_v1(crashed)

    assert isinstance(result, I06RecoveryResultV1)
    assert result.outcome is I06RecoveryOutcomeV1.REDELIVERED_ALREADY_ACCEPTED
    assert result.state.phase is I06PhaseV1.ACK_DURABLE
    assert result.state.delivery_attempts == 2
    assert result.state.ack_journal is not None
    assert result.state.ack_journal.write_count == 1
    assert result.state.ack_journal.ack.effect_id == crashed.effect.effect_id
    assert result.state.ack_journal.ack.destination_receipt_root == (
        crashed.destination_state.records[0].destination_receipt_root
    )


def test_repeated_redelivery_does_not_append_a_second_local_ack() -> None:
    recovered = _recovered()

    result = redeliver_and_record_ack_v1(recovered)

    assert isinstance(result, I06RecoveryResultV1)
    assert result.outcome is I06RecoveryOutcomeV1.ALREADY_DURABLE_NOOP
    assert result.state.delivery_attempts == recovered.delivery_attempts + 1
    assert result.state.ack_journal == recovered.ack_journal
    assert result.state.ack_journal is not None
    assert result.state.ack_journal.write_count == 1


def test_lost_ack_recovery_never_mints_a_new_effect_identity() -> None:
    crashed = _crashed()
    recovered = _recovered()

    assert recovered.effect.effect_id == crashed.effect.effect_id
    assert recovered.effect.payload_root == crashed.effect.payload_root
    assert recovered.destination_state == crashed.destination_state


def test_forged_destination_receipt_is_rejected_by_provenance_verifier() -> None:
    crashed = _crashed()
    record = crashed.destination_state.records[0]
    forged_record = replace(
        record,
        destination_receipt_root=tagged_digest("i06/foreign-receipt"),
    )
    forged_state = replace(
        crashed,
        destination_state=I04DestinationStateV1(records=(forged_record,)),
    )

    result = redeliver_and_record_ack_v1(forged_state)

    assert isinstance(result, I06RecoveryRejectV1)
    assert result.code is I06RecoveryCodeV1.PROVENANCE_REJECTED


def test_ready_state_cannot_skip_the_destination_acceptance_crash_phase() -> None:
    result = redeliver_and_record_ack_v1(_ready())

    assert isinstance(result, I06RecoveryRejectV1)
    assert result.code is I06RecoveryCodeV1.INVALID_PHASE


def test_recovery_state_rejects_exact_class_contract_without_verifier_provenance() -> None:
    ready = _ready()
    forged = object.__new__(I04VerifiedDedupContractV1)
    object.__setattr__(forged, "destination", ready.contract.destination)
    object.__setattr__(forged, "adapter_profile_root", ready.contract.adapter_profile_root)
    object.__setattr__(forged, "mode", ready.contract.mode)
    object.__setattr__(forged, "contract_root", ready.contract.contract_root)

    result = new_delivery_state_v1(forged, ready.effect)

    assert isinstance(result, I06RecoveryRejectV1)
    assert result.code is I06RecoveryCodeV1.INVALID_STATE


def test_attempt_counter_overflow_rejects_without_redelivery() -> None:
    recovered = _recovered()
    exhausted = replace(recovered, delivery_attempts=U32_MAX)

    result = redeliver_and_record_ack_v1(exhausted)

    assert isinstance(result, I06RecoveryRejectV1)
    assert result.code is I06RecoveryCodeV1.ATTEMPT_OVERFLOW


def test_malformed_state_is_typed_rejection() -> None:
    result = redeliver_and_record_ack_v1(object())

    assert isinstance(result, I06RecoveryRejectV1)
    assert result.code is I06RecoveryCodeV1.INVALID_STATE
