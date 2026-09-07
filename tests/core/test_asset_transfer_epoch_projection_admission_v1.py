"""Epoch fragment admission consumes the owned prospective projection."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import asset_transfer_epoch_projection_v1 as runtime_projection
from src.core import asset_transfer_receipt_admission_v1 as admission
from src.core import global_accounting_allocation_certificate_v1 as allocation
from src.core.asset_transfer_epoch_position_v1 import AssetTransferEpochPositionV1
from src.core.asset_transfer_global_allocation_v1 import (
    AssetTransferGlobalAllocationCandidateV1,
    GlobalAllocationBindingRejectCodeV1,
    GlobalAllocationBindingRejectedV1,
    _epoch_allocation_binding_reject_v1,
)
from src.core.global_settlement_types_v1 import ReplayStateV1, canonical_global_bytes_v1
from src.core.lane_module_receipt_verification_v1 import VerifiedLaneModuleTransitionV1
from tests.core.test_asset_transfer_epoch_allocation_v1 import _fixture
from tests.core.test_asset_transfer_global_allocation_v1 import _global_allocation_fixture
from tests.core.test_global_settlement_abi_v1 import (
    _asset_module_input_for_occurrence,
    _epoch_asset_module_state,
    _verified_asset_module_for_occurrence,
)


def _epoch_pair(candidate, evidence, index: int) -> AssetTransferGlobalAllocationCandidateV1:
    return AssetTransferGlobalAllocationCandidateV1(
        evidence[index][0],
        candidate.command_occurrences[index],
        candidate.pre_state
        if index == 0
        else candidate.route_state_disclosures[index - 1].post_state,
        candidate.route_state_disclosures[index].post_state,
    )


def _pair_input_bytes(
    pair: AssetTransferGlobalAllocationCandidateV1,
    position: AssetTransferEpochPositionV1,
) -> bytes:
    return canonical_global_bytes_v1(
        (
            position.epoch_source,
            position.occurrence_index,
            pair.predecessor,
            pair.current,
            pair.occurrence,
            pair.accepted.statement_root,
            pair.accepted.post_state,
            pair.accepted.effects,
            pair.accepted.module_journal,
            pair.accepted.private_port,
        )
    )


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _full_replay_rows() -> tuple[ReplayStateV1, ...]:
    return tuple(
        ReplayStateV1(f"admission-capacity-{index:05d}", _root(200_000 + index))
        for index in range(4096)
    )


def _capacity_replay_omission_fixture() -> tuple[
    VerifiedLaneModuleTransitionV1,
    AssetTransferGlobalAllocationCandidateV1,
    AssetTransferEpochPositionV1,
]:
    """Build a well-formed module witness with a valid full table missing its next row."""

    profile, _route, template, _accepted, _template_witness, initial, _post = (
        _global_allocation_fixture()
    )
    predecessor = replace(initial, replay_state=_full_replay_rows())
    occurrence = replace(template, pre_state_root=predecessor.state_root)
    module_state = replace(
        _epoch_asset_module_state(profile),
        balances=predecessor.balances,
        supplies=predecessor.supplies,
    )
    module_input = replace(
        _asset_module_input_for_occurrence(profile, occurrence, module_state),
        pre_state=module_state,
        custody=predecessor.custody,
    )
    accepted, rebuilt_witness = _verified_asset_module_for_occurrence(
        profile,
        occurrence,
        module_input,
    )
    private_post = accepted.private_port.post_state
    current = replace(
        predecessor,
        height=occurrence.height,
        lane_roots=(
            replace(predecessor.lane_roots[0], state_root=private_post.state_root),
            *predecessor.lane_roots[1:],
        ),
        balances=private_post.balances,
        supplies=private_post.supplies,
        # The row is deliberately absent while both states remain structurally valid.
        replay_state=predecessor.replay_state,
    )
    pair = AssetTransferGlobalAllocationCandidateV1(accepted, occurrence, predecessor, current)
    position = AssetTransferEpochPositionV1(predecessor, 0)
    added = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    assert len(predecessor.replay_state) == len(current.replay_state) == 4096
    assert all(row.replay_id != added.replay_id for row in predecessor.replay_state)
    assert all(row.occurrence_id != added.occurrence_id for row in predecessor.replay_state)
    assert occurrence.pre_state_root == predecessor.state_root
    assert current.height == occurrence.height == predecessor.height + 1
    assert current.lane_roots[0].state_root == private_post.state_root
    assert (current.balances, current.custody, current.supplies) == (
        private_post.balances,
        private_post.custody,
        private_post.supplies,
    )
    assert accepted.module_journal.command_occurrence_id == occurrence.occurrence_id
    assert rebuilt_witness.module_journal_root == accepted.module_journal.journal_root
    return rebuilt_witness, pair, position


@pytest.mark.parametrize("index", (0, 1))
def test_epoch_admission_recomputes_and_consumes_owned_runtime_projection(
    monkeypatch: pytest.MonkeyPatch,
    index: int,
) -> None:
    candidate, evidence = _fixture(count=2)
    pair = _epoch_pair(candidate, evidence, index)
    position = AssetTransferEpochPositionV1(candidate.pre_state, index)
    before = _pair_input_bytes(pair, position)
    projected = []
    admitted = []
    actual_project = runtime_projection.project_asset_transfer_epoch_position_v1
    actual_admit = admission._admit_global_fragment_v1

    def project_spy(**kwargs):
        result = actual_project(**kwargs)
        projected.append(result)
        return result

    def admit_spy(witness, accepted, predecessor, post_state):
        admitted.append((witness, accepted, predecessor, post_state))
        return actual_admit(witness, accepted, predecessor, post_state)

    # The attribute is deliberately absent before the repair. The spy delegates
    # to the real data constructor and cannot mint or substitute any authority.
    monkeypatch.setattr(
        admission,
        "project_asset_transfer_epoch_position_v1",
        project_spy,
        raising=False,
    )
    monkeypatch.setattr(admission, "_admit_global_fragment_v1", admit_spy)

    result = admission.verify_asset_transfer_epoch_fragment_receipt_v1(
        evidence[index][1], pair, position
    )

    assert isinstance(result, allocation.VerifiedLaneAllocationFragmentV1)
    assert len(projected) == len(admitted) == 1
    projection = projected[0]
    _witness, accepted, predecessor, post_state = admitted[0]
    assert projection.post_state == pair.current
    assert projection.position is not position
    assert projection.predecessor is not pair.predecessor
    assert projection.occurrence is not pair.occurrence
    assert projection.accepted is not pair.accepted
    assert accepted is projection.accepted
    assert predecessor is projection.predecessor
    assert post_state is projection.post_state
    assert _pair_input_bytes(pair, position) == before


def test_replay_capacity_omission_rejects_before_projection_or_fragment(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    witness, pair, position = _capacity_replay_omission_fixture()
    before = _pair_input_bytes(pair, position)
    baseline = _epoch_allocation_binding_reject_v1(pair, position)
    assert isinstance(baseline, GlobalAllocationBindingRejectedV1)
    assert baseline.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_REPLAY_CONTINUITY_DRIFT

    def unexpected(*_args, **_kwargs):
        pytest.fail("failed epoch relation must not construct or mint a fragment")

    monkeypatch.setattr(
        admission,
        "project_asset_transfer_epoch_position_v1",
        unexpected,
        raising=False,
    )
    monkeypatch.setattr(admission, "_admit_global_fragment_v1", unexpected)

    rejected = admission.verify_asset_transfer_epoch_fragment_receipt_v1(
        witness,
        pair,
        position,
    )

    assert isinstance(rejected, GlobalAllocationBindingRejectedV1)
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_REPLAY_CONTINUITY_DRIFT
    assert _pair_input_bytes(pair, position) == before


def test_projection_drift_blocks_fragment_minting_with_existing_binding_code(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate, evidence = _fixture(count=2)
    pair = _epoch_pair(candidate, evidence, 1)
    position = AssetTransferEpochPositionV1(candidate.pre_state, 1)
    before = _pair_input_bytes(pair, position)
    actual_project = runtime_projection.project_asset_transfer_epoch_position_v1

    def drifted_project(**kwargs):
        projection = actual_project(**kwargs)
        # This controlled result fault changes only ordinary proposal data.
        object.__setattr__(
            projection,
            "post_state",
            replace(projection.post_state, history_root="0x" + "dd" * 32),
        )
        return projection

    def unexpected_fragment(*_args, **_kwargs):
        pytest.fail("projection drift must block fragment minting")

    monkeypatch.setattr(
        admission,
        "project_asset_transfer_epoch_position_v1",
        drifted_project,
        raising=False,
    )
    monkeypatch.setattr(admission, "_admit_global_fragment_v1", unexpected_fragment)

    rejected = admission.verify_asset_transfer_epoch_fragment_receipt_v1(
        evidence[1][1],
        pair,
        position,
    )

    assert isinstance(rejected, GlobalAllocationBindingRejectedV1)
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_PROJECTION_ROWS_DRIFT
    assert _pair_input_bytes(pair, position) == before
