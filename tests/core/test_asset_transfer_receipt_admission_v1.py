"""Receipt admission for the ASSET_TRANSFER allocation fragment (C9a)."""

from __future__ import annotations

import pytest

from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core.asset_transfer_receipt_admission_v1 import (
    ReceiptWitnessRejectCodeV1,
    ReceiptWitnessRejectedV1,
    VerifiedLaneAllocationFragmentV1,
    verify_asset_transfer_fragment_receipt_v1,
)
from src.core.global_accounting_lane_producers_v1 import (
    ReceiptBackedProducerRejectCodeV1,
    ReceiptBackedProducerRejectedV1,
)
from src.core.global_settlement_types_v1 import LaneIdV1, LaneStateRootV1
from tests.core.test_global_settlement_abi_v1 import (
    _asset_module_input_for_occurrence,
    _epoch_asset_module_state,
    _global_state_from_asset_module,
    _occurrence,
    _profile,
    _verified_asset_module_for_occurrence,
)


def _admission_fixture():
    profile, route = _profile()
    module_state = _epoch_asset_module_state(profile)
    pre_state = _global_state_from_asset_module(profile, module_state, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(profile, occurrence, module_state)
    accepted, witness = _verified_asset_module_for_occurrence(profile, occurrence, module_input)
    lane_root = LaneStateRootV1(
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=accepted.module_journal.module_release_id,
        enabled=True,
        state_root=accepted.module_journal.post_lane_root,
    )
    prior = cert.LaneAllocationFragmentV1(
        lane_id=LaneIdV1.ASSET_TRANSFER,
        module_release_id=accepted.module_journal.module_release_id,
        enabled=True,
        lane_state_root=accepted.module_journal.pre_lane_root,
        producer_kind=cert.LaneProducerKindV1.RECEIPT_BACKED,
        binding_root=accepted.module_journal.pre_lane_root,
        controlled_locations=(),
        claimant_entitlements=(),
        unencumbered_reserves=(),
        pending_external_obligations=(),
        terminal_bindings=(),
    )
    return accepted, witness, lane_root, prior


def test_witness_token_is_verifier_only() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedLaneAllocationFragmentV1(object(), None)  # type: ignore[arg-type]


def test_admission_requires_the_module_witness_type() -> None:
    accepted, _witness, lane_root, prior = _admission_fixture()
    with pytest.raises(TypeError, match="module receipt witness"):
        verify_asset_transfer_fragment_receipt_v1(
            object(),  # type: ignore[arg-type]
            accepted,
            lane_root,
            prior,
            (),
        )


def test_receipt_admitted_fragment_carries_the_witness_binding() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    admitted = verify_asset_transfer_fragment_receipt_v1(witness, accepted, lane_root, prior, ())
    assert isinstance(admitted, VerifiedLaneAllocationFragmentV1)
    assert admitted.fragment.binding_root == accepted.module_journal.receipt_root
    assert admitted.module_journal_root == accepted.module_journal.journal_root
    assert admitted.expected_image_id == witness.expected_image_id
    assert admitted.receipt_digest == witness.receipt_digest
    with pytest.raises(AttributeError, match="immutable"):
        admitted.fragment = None  # type: ignore[misc,assignment]


def test_foreign_accepted_value_is_rejected_at_the_journal_root() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    profile, route = _profile(authority_epoch=8)
    module_state = _epoch_asset_module_state(profile)
    pre_state = _global_state_from_asset_module(profile, module_state, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(profile, occurrence, module_state)
    foreign_accepted, _foreign_witness = _verified_asset_module_for_occurrence(
        profile, occurrence, module_input
    )
    reject = verify_asset_transfer_fragment_receipt_v1(
        witness, foreign_accepted, lane_root, prior, ()
    )
    assert isinstance(reject, ReceiptWitnessRejectedV1)
    assert reject.code is ReceiptWitnessRejectCodeV1.WITNESS_JOURNAL_ROOT_DRIFT
    assert reject.detail == "journal root"


def test_forged_statement_root_is_rejected_behind_the_journal_binding() -> None:
    """The statement check is defensive double-binding; only object.__new__
    forgery (bypassing __post_init__) can vary the statement while keeping the
    journal, and the verifier still refuses it."""

    accepted, witness, lane_root, prior = _admission_fixture()
    forged = object.__new__(type(accepted))
    for field in type(accepted).__dataclass_fields__:
        object.__setattr__(forged, field, getattr(accepted, field))
    object.__setattr__(forged, "statement_root", "0x" + "77" * 32)
    reject = verify_asset_transfer_fragment_receipt_v1(witness, forged, lane_root, prior, ())
    assert isinstance(reject, ReceiptWitnessRejectedV1)
    assert reject.code is ReceiptWitnessRejectCodeV1.WITNESS_STATEMENT_ROOT_DRIFT


def test_producer_rejects_pass_through_unchanged() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    disabled = LaneStateRootV1(
        lane_id=lane_root.lane_id,
        module_release_id=lane_root.module_release_id,
        enabled=False,
        state_root=lane_root.state_root,
    )
    reject = verify_asset_transfer_fragment_receipt_v1(witness, accepted, disabled, prior, ())
    assert isinstance(reject, ReceiptBackedProducerRejectedV1)
    assert reject.code is ReceiptBackedProducerRejectCodeV1.LANE_DISABLED


def test_witness_reject_family_is_closed_and_ordered() -> None:
    assert [code.name for code in ReceiptWitnessRejectCodeV1] == [
        "WITNESS_KIND_DRIFT",
        "WITNESS_JOURNAL_ROOT_DRIFT",
        "WITNESS_STATEMENT_ROOT_DRIFT",
        "WITNESS_OCCURRENCE_DRIFT",
        "WITNESS_BINDING_ROOT_DRIFT",
    ]
    assert all(code.value == code.name for code in ReceiptWitnessRejectCodeV1)


def test_witness_reject_is_a_no_op_value() -> None:
    accepted, witness, lane_root, prior = _admission_fixture()
    before = accepted.module_journal.journal_root
    profile, route = _profile(authority_epoch=8)
    module_state = _epoch_asset_module_state(profile)
    pre_state = _global_state_from_asset_module(profile, module_state, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(profile, occurrence, module_state)
    foreign_accepted, _ = _verified_asset_module_for_occurrence(profile, occurrence, module_input)
    verify_asset_transfer_fragment_receipt_v1(witness, foreign_accepted, lane_root, prior, ())
    assert accepted.module_journal.journal_root == before
    assert witness.module_journal_root == before
