"""I04 destination deduplication contract tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_i04_destination_dedup import (
    MAX_DESTINATION_RECEIPTS_V1,
    I04DedupCodeV1,
    I04DedupContractCandidateV1,
    I04DedupModeV1,
    I04DedupRejectV1,
    I04DeliveryAcceptV1,
    I04DeliveryOutcomeV1,
    I04DestinationRecordV1,
    I04DestinationStateV1,
    I04Error,
    I04VerifiedDedupContractV1,
    deliver_effect_v1,
    derive_dedup_contract_root,
    verify_dedup_contract_v1,
)
from src.core.fcis_durable_retraction import (
    OutboxEffectV1,
    derive_effect_id,
    tagged_digest,
)


def _effect(
    *,
    destination: str = "i04-destination",
    payload_label: str = "i04/payload",
    adapter_profile_root: str | None = None,
) -> OutboxEffectV1:
    commit_id = tagged_digest("i04/commit")
    writer_profile_root = tagged_digest("i04/writer")
    payload_root = tagged_digest(payload_label)
    profile_root = adapter_profile_root or tagged_digest("i04/adapter")
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


def _contract(mode: I04DedupModeV1) -> I04VerifiedDedupContractV1:
    profile_root = tagged_digest("i04/adapter")
    root = derive_dedup_contract_root("i04-destination", profile_root, mode)
    result = verify_dedup_contract_v1(
        I04DedupContractCandidateV1(
            destination="i04-destination",
            adapter_profile_root=profile_root,
            mode=mode,
            contract_root=root,
        )
    )
    if not isinstance(result, I04VerifiedDedupContractV1):
        raise AssertionError(f"expected verified contract, got {result!r}")
    return result


def _accepted(result: object) -> I04DeliveryAcceptV1:
    assert isinstance(result, I04DeliveryAcceptV1)
    return result


def test_each_declared_mechanism_is_observationally_idempotent() -> None:
    for mode in I04DedupModeV1:
        contract = _contract(mode)
        effect = _effect()

        first = _accepted(deliver_effect_v1(contract, I04DestinationStateV1(), effect))
        second = _accepted(deliver_effect_v1(contract, first.next_state, effect))

        assert first.next_state.records == second.next_state.records
        assert first.receipt.outcome is I04DeliveryOutcomeV1.ACCEPTED
        assert second.receipt.outcome is I04DeliveryOutcomeV1.ALREADY_ACCEPTED
        assert first.receipt.effect_id == second.receipt.effect_id == effect.effect_id
        assert first.receipt.payload_root == second.receipt.payload_root == effect.payload_root
        assert first.receipt.destination_receipt_root == second.receipt.destination_receipt_root


def test_same_effect_id_with_changed_payload_rejects_without_state_change() -> None:
    contract = _contract(I04DedupModeV1.APPLICATION_RECEIPT_TABLE)
    effect = _effect()
    accepted = _accepted(deliver_effect_v1(contract, I04DestinationStateV1(), effect))

    changed = replace(effect, payload_root=tagged_digest("i04/foreign-payload"))
    result = deliver_effect_v1(contract, accepted.next_state, changed)

    assert isinstance(result, I04DedupRejectV1)
    assert result.code is I04DedupCodeV1.PAYLOAD_CONFLICT
    assert not hasattr(result, "next_state")


def test_destination_and_adapter_profile_crossings_reject() -> None:
    contract = _contract(I04DedupModeV1.NATIVE_IDEMPOTENCY_KEY)
    effect = _effect()

    foreign_destination = replace(effect, destination="foreign-destination")
    destination_result = deliver_effect_v1(
        contract,
        I04DestinationStateV1(),
        foreign_destination,
    )
    assert isinstance(destination_result, I04DedupRejectV1)
    assert destination_result.code is I04DedupCodeV1.DESTINATION_MISMATCH

    foreign_profile = replace(
        effect,
        adapter_profile_root=tagged_digest("i04/foreign-adapter"),
    )
    profile_result = deliver_effect_v1(contract, I04DestinationStateV1(), foreign_profile)
    assert isinstance(profile_result, I04DedupRejectV1)
    assert profile_result.code is I04DedupCodeV1.ADAPTER_PROFILE_MISMATCH


def test_unverified_or_unsupported_contract_is_unmountable() -> None:
    profile_root = tagged_digest("i04/adapter")
    valid_root = derive_dedup_contract_root(
        "i04-destination",
        profile_root,
        I04DedupModeV1.QUERY_BY_EFFECT_ID,
    )
    forged = verify_dedup_contract_v1(
        I04DedupContractCandidateV1(
            destination="i04-destination",
            adapter_profile_root=profile_root,
            mode=I04DedupModeV1.QUERY_BY_EFFECT_ID,
            contract_root=tagged_digest("i04/foreign-contract"),
        )
    )
    unsupported = verify_dedup_contract_v1(
        I04DedupContractCandidateV1(
            destination="i04-destination",
            adapter_profile_root=profile_root,
            mode="caller-asserted-exactly-once",
            contract_root=valid_root,
        )
    )

    assert isinstance(forged, I04DedupRejectV1)
    assert forged.code is I04DedupCodeV1.UNMOUNTABLE
    assert isinstance(unsupported, I04DedupRejectV1)
    assert unsupported.code is I04DedupCodeV1.UNMOUNTABLE


def test_i04_verified_contract_requires_provenance_and_fresh_use_validation() -> None:
    profile_root = tagged_digest("i04/adapter")
    mode = I04DedupModeV1.QUERY_BY_EFFECT_ID
    contract_root = derive_dedup_contract_root("i04-destination", profile_root, mode)
    with pytest.raises(I04Error, match="verifier-owned"):
        I04VerifiedDedupContractV1(
            destination="i04-destination",
            adapter_profile_root=profile_root,
            mode=mode,
            contract_root=contract_root,
        )

    verified = _contract(mode)
    object.__setattr__(verified, "destination", "foreign-destination")
    result = deliver_effect_v1(
        verified,
        I04DestinationStateV1(),
        _effect(destination="foreign-destination"),
    )
    assert isinstance(result, I04DedupRejectV1)
    assert result.code is I04DedupCodeV1.UNMOUNTABLE

    forged = object.__new__(I04VerifiedDedupContractV1)
    object.__setattr__(forged, "destination", "i04-destination")
    object.__setattr__(forged, "adapter_profile_root", profile_root)
    object.__setattr__(forged, "mode", mode)
    object.__setattr__(forged, "contract_root", contract_root)
    forged_result = deliver_effect_v1(forged, I04DestinationStateV1(), _effect())
    assert isinstance(forged_result, I04DedupRejectV1)
    assert forged_result.code is I04DedupCodeV1.UNMOUNTABLE


def test_invalid_contract_rejects_without_changing_valid_destination_state() -> None:
    contract = _contract(I04DedupModeV1.QUERY_BY_EFFECT_ID)
    effect = _effect()
    accepted = _accepted(deliver_effect_v1(contract, I04DestinationStateV1(), effect))

    result = deliver_effect_v1(object(), accepted.next_state, effect)

    assert isinstance(result, I04DedupRejectV1)
    assert result.code is I04DedupCodeV1.UNMOUNTABLE
    assert not hasattr(result, "next_state")


def test_delivery_accept_owns_one_matching_state_and_receipt_pair() -> None:
    contract = _contract(I04DedupModeV1.APPLICATION_RECEIPT_TABLE)
    accepted = _accepted(deliver_effect_v1(contract, I04DestinationStateV1(), _effect()))
    crossed_receipt = replace(
        accepted.receipt,
        payload_root=tagged_digest("i04/crossed-receipt-payload"),
    )

    with pytest.raises(I04Error, match="do not agree"):
        I04DeliveryAcceptV1(
            next_state=accepted.next_state,
            receipt=crossed_receipt,
        )


def test_destination_state_rejects_duplicate_or_noncanonical_records() -> None:
    first = I04DestinationRecordV1(
        effect_id=tagged_digest("i04/effect-a"),
        destination="i04-destination",
        payload_root=tagged_digest("i04/payload-a"),
        destination_receipt_root=tagged_digest("i04/receipt-a"),
    )
    second = replace(
        first,
        effect_id=tagged_digest("i04/effect-b"),
        payload_root=tagged_digest("i04/payload-b"),
        destination_receipt_root=tagged_digest("i04/receipt-b"),
    )
    with pytest.raises(ValueError, match="canonically ordered"):
        I04DestinationStateV1(records=(second, first))
    with pytest.raises(ValueError, match="unique"):
        I04DestinationStateV1(records=(first, first))

    malformed = object.__new__(I04DestinationRecordV1)
    object.__setattr__(malformed, "effect_id", first.effect_id)
    object.__setattr__(malformed, "destination", "")
    object.__setattr__(malformed, "payload_root", first.payload_root)
    object.__setattr__(malformed, "destination_receipt_root", first.destination_receipt_root)
    with pytest.raises(ValueError, match="destination"):
        I04DestinationStateV1(records=(malformed,))


def test_invalid_effect_is_rejected_without_creating_destination_state() -> None:
    contract = _contract(I04DedupModeV1.QUERY_BY_EFFECT_ID)
    state = I04DestinationStateV1()

    result = deliver_effect_v1(contract, state, object())

    assert isinstance(result, I04DedupRejectV1)
    assert result.code is I04DedupCodeV1.INVALID_EFFECT
    assert not hasattr(result, "next_state")


def _at_capacity_state() -> I04DestinationStateV1:
    records = tuple(
        sorted(
            (
                I04DestinationRecordV1(
                    effect_id=tagged_digest(f"i04/capacity/effect/{index:04d}"),
                    destination="i04-destination",
                    payload_root=tagged_digest(f"i04/capacity/payload/{index:04d}"),
                    destination_receipt_root=tagged_digest(f"i04/capacity/receipt/{index:04d}"),
                )
                for index in range(MAX_DESTINATION_RECEIPTS_V1)
            ),
            key=lambda record: record.effect_id,
        )
    )
    state = I04DestinationStateV1(records=records)
    state.__post_init__()
    return state


def test_destination_capacity_is_closed_at_construction_revalidation_and_delivery() -> None:
    state = _at_capacity_state()
    contract = _contract(I04DedupModeV1.APPLICATION_RECEIPT_TABLE)

    over_capacity = object.__new__(I04DestinationStateV1)
    object.__setattr__(over_capacity, "records", (*state.records, state.records[0]))
    with pytest.raises(ValueError, match="capacity bound"):
        over_capacity.__post_init__()

    result = deliver_effect_v1(contract, state, _effect(payload_label="i04/full"))

    assert isinstance(result, I04DedupRejectV1)
    assert result.code is I04DedupCodeV1.CAPACITY_EXCEEDED
    assert not hasattr(result, "next_state")

    forged_state = object.__new__(I04DestinationStateV1)
    object.__setattr__(forged_state, "records", (*state.records, state.records[0]))
    invalid_state = deliver_effect_v1(contract, forged_state, _effect())
    assert isinstance(invalid_state, I04DedupRejectV1)
    assert invalid_state.code is I04DedupCodeV1.STATE_INVALID
    assert not hasattr(invalid_state, "next_state")
