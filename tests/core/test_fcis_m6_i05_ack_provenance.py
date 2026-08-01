"""I05 destination acknowledgment provenance tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_i04_destination_dedup import (
    I04DedupContractCandidateV1,
    I04DedupModeV1,
    I04DedupRejectV1,
    I04DestinationReceiptV1,
    I04DestinationStateV1,
    I04VerifiedDedupContractV1,
    deliver_effect_v1,
    derive_dedup_contract_root,
    verify_dedup_contract_v1,
)
from experiments.fcis_m6_i05_ack_provenance import (
    I05_VERIFIER_PROFILE_ROOT,
    I05AckCandidateV1,
    I05AckCodeV1,
    I05AckRejectV1,
    I05VerifiedAckV1,
    derive_ack_subject_root,
    verify_ack_provenance_v1,
)
from src.core.fcis_durable_retraction import (
    OutboxEffectV1,
    derive_effect_id,
    tagged_digest,
)


def _effect(
    *,
    destination: str = "i05-destination",
    commit_label: str = "i05/commit",
    payload_label: str = "i05/payload",
    adapter_profile_root: str | None = None,
) -> OutboxEffectV1:
    commit_id = tagged_digest(commit_label)
    writer_profile_root = tagged_digest("i05/writer")
    payload_root = tagged_digest(payload_label)
    profile_root = adapter_profile_root or tagged_digest("i05/adapter")
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
        adapter_profile_root=profile_root,
    )


def _contract(effect: OutboxEffectV1) -> I04VerifiedDedupContractV1:
    root = derive_dedup_contract_root(
        effect.destination,
        effect.adapter_profile_root,
        I04DedupModeV1.APPLICATION_RECEIPT_TABLE,
    )
    result = verify_dedup_contract_v1(
        I04DedupContractCandidateV1(
            destination=effect.destination,
            adapter_profile_root=effect.adapter_profile_root,
            mode=I04DedupModeV1.APPLICATION_RECEIPT_TABLE,
            contract_root=root,
        )
    )
    if not isinstance(result, I04VerifiedDedupContractV1):
        raise AssertionError(f"expected verified contract, got {result!r}")
    return result


def _delivered(
    effect: OutboxEffectV1,
) -> tuple[I04VerifiedDedupContractV1, I04DestinationStateV1, I04DestinationReceiptV1]:
    contract = _contract(effect)
    state, result = deliver_effect_v1(contract, I04DestinationStateV1(), effect)
    if isinstance(result, I04DedupRejectV1):
        raise AssertionError(f"expected destination delivery, got {result!r}")
    return contract, state, result


def _candidate(
    effect: OutboxEffectV1,
    contract: I04VerifiedDedupContractV1,
    state: I04DestinationStateV1,
    receipt: I04DestinationReceiptV1,
    *,
    adapter_profile_root: str | None = None,
    verifier_profile_root: str = I05_VERIFIER_PROFILE_ROOT,
    subject_root: str | None = None,
) -> I05AckCandidateV1:
    adapter_root = adapter_profile_root or effect.adapter_profile_root
    subject = subject_root or derive_ack_subject_root(
        effect_id=receipt.effect_id,
        destination=receipt.destination,
        payload_root=receipt.payload_root,
        destination_receipt_root=receipt.destination_receipt_root,
        adapter_profile_root=adapter_root,
        verifier_profile_root=verifier_profile_root,
    )
    return I05AckCandidateV1(
        effect=effect,
        contract=contract,
        delivery_state=state,
        receipt=receipt,
        adapter_profile_root=adapter_root,
        verifier_profile_root=verifier_profile_root,
        subject_root=subject,
    )


def test_valid_ack_binds_delivery_receipt_and_subject() -> None:
    effect = _effect()
    contract, state, receipt = _delivered(effect)

    result = verify_ack_provenance_v1(_candidate(effect, contract, state, receipt))

    assert isinstance(result, I05VerifiedAckV1)
    assert result.effect_id == effect.effect_id
    assert result.payload_root == effect.payload_root
    assert result.destination_receipt_root == receipt.destination_receipt_root
    assert result.subject_root == derive_ack_subject_root(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        destination_receipt_root=receipt.destination_receipt_root,
        adapter_profile_root=effect.adapter_profile_root,
        verifier_profile_root=I05_VERIFIER_PROFILE_ROOT,
    )


def test_ack_before_delivery_rejects_even_with_well_shaped_receipt() -> None:
    effect = _effect()
    contract, delivered_state, receipt = _delivered(effect)
    assert delivered_state.records
    candidate = _candidate(effect, contract, I04DestinationStateV1(), receipt)

    result = verify_ack_provenance_v1(candidate)

    assert isinstance(result, I05AckRejectV1)
    assert result.code is I05AckCodeV1.DELIVERY_MISSING


def test_foreign_receipt_root_rejects_without_accepting_a_digest_shape() -> None:
    effect = _effect()
    contract, state, receipt = _delivered(effect)
    forged_receipt = replace(
        receipt,
        destination_receipt_root=tagged_digest("i05/foreign-receipt"),
    )
    candidate = _candidate(effect, contract, state, forged_receipt)

    result = verify_ack_provenance_v1(candidate)

    assert isinstance(result, I05AckRejectV1)
    assert result.code is I05AckCodeV1.RECEIPT_MISMATCH


def test_crossed_effect_and_receipt_reject() -> None:
    effect_a = _effect(commit_label="i05/commit-a", payload_label="i05/payload-a")
    effect_b = _effect(commit_label="i05/commit-b", payload_label="i05/payload-b")
    contract_a, state_a, receipt_a = _delivered(effect_a)
    _, _, receipt_b = _delivered(effect_b)
    candidate = _candidate(effect_a, contract_a, state_a, receipt_b)

    result = verify_ack_provenance_v1(candidate)

    assert isinstance(result, I05AckRejectV1)
    assert result.code is I05AckCodeV1.EFFECT_MISMATCH
    assert receipt_a.effect_id != receipt_b.effect_id


def test_foreign_verifier_and_adapter_profiles_reject() -> None:
    effect = _effect()
    contract, state, receipt = _delivered(effect)
    foreign_verifier = _candidate(
        effect,
        contract,
        state,
        receipt,
        verifier_profile_root=tagged_digest("i05/foreign-verifier"),
    )
    foreign_adapter = _candidate(
        effect,
        contract,
        state,
        receipt,
        adapter_profile_root=tagged_digest("i05/foreign-adapter"),
    )

    verifier_result = verify_ack_provenance_v1(foreign_verifier)
    adapter_result = verify_ack_provenance_v1(foreign_adapter)

    assert isinstance(verifier_result, I05AckRejectV1)
    assert verifier_result.code is I05AckCodeV1.VERIFIER_PROFILE_MISMATCH
    assert isinstance(adapter_result, I05AckRejectV1)
    assert adapter_result.code is I05AckCodeV1.ADAPTER_PROFILE_MISMATCH


def test_forged_subject_root_rejects_after_receipt_and_delivery_checks() -> None:
    effect = _effect()
    contract, state, receipt = _delivered(effect)
    candidate = _candidate(
        effect,
        contract,
        state,
        receipt,
        subject_root=tagged_digest("i05/foreign-subject"),
    )

    result = verify_ack_provenance_v1(candidate)

    assert isinstance(result, I05AckRejectV1)
    assert result.code is I05AckCodeV1.SUBJECT_MISMATCH


def test_invalid_candidate_type_rejects() -> None:
    result = verify_ack_provenance_v1(object())

    assert isinstance(result, I05AckRejectV1)
    assert result.code is I05AckCodeV1.INVALID_CANDIDATE


def test_candidate_subject_changes_when_any_provenance_field_changes() -> None:
    effect = _effect()
    contract, state, receipt = _delivered(effect)
    first = _candidate(effect, contract, state, receipt)
    changed = _candidate(
        effect,
        contract,
        state,
        receipt,
        verifier_profile_root=tagged_digest("i05/other-verifier"),
    )

    assert first.subject_root != changed.subject_root
    with pytest.raises(ValueError, match="subject root"):
        I05VerifiedAckV1(
            effect_id=effect.effect_id,
            destination=effect.destination,
            payload_root=effect.payload_root,
            destination_receipt_root=receipt.destination_receipt_root,
            adapter_profile_root=effect.adapter_profile_root,
            verifier_profile_root=changed.verifier_profile_root,
            subject_root=first.subject_root,
        )
