"""Epoch-position controls; cryptographic ports remain deterministic test mocks."""

from dataclasses import replace

import pytest

from src.core import asset_transfer_epoch_allocation_v1 as consumer
from src.core import asset_transfer_global_allocation_v1 as relation
from src.core import asset_transfer_receipt_admission_v1 as admission
from src.core import global_accounting_allocation_certificate_v1 as allocation
from src.core.asset_transfer_epoch_position_v1 import AssetTransferEpochPositionV1
from src.integration.global_economic_epoch_verification_v1 import verify_economic_epoch_v1
from tests.core.test_asset_transfer_epoch_allocation_v1 import _check, _fixture
from tests.core.test_global_settlement_abi_v1 import _RecordingReceiptVerifier


@pytest.mark.parametrize("count", (1, 2, 8, 9, 64))
def test_epoch_position_supports_every_declared_command_boundary(count):
    candidate, evidence = _fixture(count=count)
    verify_economic_epoch_v1(candidate, _RecordingReceiptVerifier())
    checked = _check(candidate, evidence)
    assert isinstance(checked, consumer.AssetTransferEpochAllocationAcceptedV1)
    assert len(checked.checks) == count
    assert tuple(item.global_state_root for item in checked.checks) == tuple(
        disclosure.post_state.state_root for disclosure in candidate.route_state_disclosures
    )


def _pair(candidate, evidence, index):
    return relation.AssetTransferGlobalAllocationCandidateV1(
        evidence[index][0],
        candidate.command_occurrences[index],
        candidate.pre_state
        if index == 0
        else candidate.route_state_disclosures[index - 1].post_state,
        candidate.route_state_disclosures[index].post_state,
    )


def test_standalone_adjacency_and_epoch_position_keep_distinct_meanings():
    candidate, evidence = _fixture(count=2)
    second = _pair(candidate, evidence, 1)
    standalone = admission.verify_asset_transfer_global_fragment_receipt_v1(evidence[1][1], second)
    assert standalone.code is relation.GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    epoch = admission.verify_asset_transfer_epoch_fragment_receipt_v1(
        evidence[1][1],
        second,
        AssetTransferEpochPositionV1(candidate.pre_state, 1),
    )
    assert isinstance(epoch, allocation.VerifiedLaneAllocationFragmentV1)
    assert second.predecessor.height == second.current.height == candidate.pre_state.height + 1
    assert second.predecessor.state_root == second.occurrence.pre_state_root


@pytest.mark.parametrize("index", (-1, 64, True, "1"))
def test_position_index_is_exact_and_bounded(index):
    candidate, _ = _fixture()
    with pytest.raises((TypeError, ValueError)):
        AssetTransferEpochPositionV1(candidate.pre_state, index)


@pytest.mark.parametrize(
    "change",
    ("first_as_second", "second_as_first", "source_height", "source_context", "first_source_root"),
)
def test_source_position_binding_refuses_independent_substitutions(change):
    candidate, evidence = _fixture(count=2)
    index = 0 if change in {"first_as_second", "first_source_root"} else 1
    source, claimed_index = candidate.pre_state, index
    if change == "first_as_second":
        claimed_index = 1
    elif change == "second_as_first":
        claimed_index = 0
    elif change == "source_height":
        source = replace(source, height=source.height + 1)
    elif change == "source_context":
        source = replace(source, chain_id="foreign")
    else:
        source = replace(source, history_root="0x" + "99" * 32)
    result = admission.verify_asset_transfer_epoch_fragment_receipt_v1(
        evidence[index][1],
        _pair(candidate, evidence, index),
        AssetTransferEpochPositionV1(source, claimed_index),
    )
    assert isinstance(result, relation.GlobalAllocationBindingRejectedV1)


@pytest.mark.parametrize("mode", (None, True, "EPOCH_POSITION", object()))
def test_unknown_private_height_mode_never_relaxes_adjacency(mode):
    candidate, evidence = _fixture(count=2)
    pair = _pair(candidate, evidence, 1)
    result = relation._global_allocation_binding_reject_v1(
        pair.accepted,
        pair.occurrence,
        pair.predecessor,
        pair.current,
        mode,
    )
    assert isinstance(result, relation.GlobalAllocationBindingRejectedV1)
    assert result.code is relation.GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT


def test_unregistered_same_type_enum_instance_is_not_an_epoch_capability():
    mode = object.__new__(relation._GlobalAllocationHeightModeV1)
    object.__setattr__(mode, "_name_", "FORGED")
    object.__setattr__(mode, "_value_", "EPOCH_POSITION")
    test_unknown_private_height_mode_never_relaxes_adjacency(mode)


def test_first_source_equality_guard_kills_its_omission_mutant():
    import inspect

    candidate, evidence = _fixture()
    pair = _pair(candidate, evidence, 0)
    wrong_source = replace(candidate.pre_state, history_root="0x" + "dd" * 32)
    position = AssetTransferEpochPositionV1(wrong_source, 0)
    original = relation._epoch_allocation_binding_reject_v1
    baseline = original(pair, position)
    assert isinstance(baseline, relation.GlobalAllocationBindingRejectedV1)
    assert baseline.code is relation.GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    source = inspect.getsource(original)
    target = "or (position.occurrence_index == 0 and prior != source)"
    assert source.count(target) == 1
    namespace = dict(vars(relation))
    exec(compile(source.replace(target, "", 1), "<epoch-first-source-mutant>", "exec"), namespace)
    assert namespace[original.__name__](pair, position) is None


def test_epoch_position_fixed_vectors_match_current_sources():
    from tools.render_asset_transfer_epoch_position_v1_golden import FIXTURE, render

    assert FIXTURE.read_text() == render()
