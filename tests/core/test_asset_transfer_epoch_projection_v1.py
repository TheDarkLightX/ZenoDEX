"""Prospective shared-height epoch projection controls.

The value built here is ordinary owned proposal data. Existing epoch allocation
relations remain the authority that decides whether a proposed position can be
used in a checked ordered epoch.
"""

from __future__ import annotations

import inspect
from dataclasses import replace

import pytest

from src.core import asset_transfer_epoch_projection_v1 as projection_module
from src.core.asset_transfer_epoch_position_v1 import AssetTransferEpochPositionV1
from src.core.asset_transfer_global_allocation_v1 import (
    AssetTransferGlobalAllocationCandidateV1,
    GlobalAllocationBindingRejectCodeV1,
    _epoch_allocation_binding_reject_v1,
)
from src.core.global_settlement_types_v1 import (
    MAX_U64_V1,
    EconomicAmountV1,
    LaneIdV1,
    OutboxStateV1,
    OutboxStatusV1,
    ReplayStateV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_epoch_state_closure_v1 import SharedHeightPair

AssetTransferEpochProspectiveProjectionV1 = (
    projection_module.AssetTransferEpochProspectiveProjectionV1
)
project_asset_transfer_epoch_position_v1 = (
    projection_module.project_asset_transfer_epoch_position_v1
)


def _accepted_canonical_view(accepted: object) -> dict[str, object]:
    """Return only canonical projections for a retained accepted value."""

    return {
        "statement_root": accepted.statement_root,  # type: ignore[attr-defined]
        "post_state": accepted.post_state,  # type: ignore[attr-defined]
        "effects": accepted.effects,  # type: ignore[attr-defined]
        "module_journal": accepted.module_journal,  # type: ignore[attr-defined]
        "private_port": accepted.private_port,  # type: ignore[attr-defined]
    }


def _retained_input_bytes(
    *,
    position: AssetTransferEpochPositionV1,
    predecessor: object,
    occurrence: object,
    accepted: object,
    post_state: object | None = None,
) -> bytes:
    """Canonical snapshot for no-alias controls without admitting new types."""

    value: dict[str, object] = {
        "position": {
            "epoch_source": position.epoch_source,
            "occurrence_index": position.occurrence_index,
        },
        "predecessor": predecessor,
        "occurrence": occurrence.to_canonical(),  # type: ignore[attr-defined]
        "accepted": _accepted_canonical_view(accepted),
    }
    if post_state is not None:
        value["post_state"] = post_state
    return canonical_global_bytes_v1(value)


def _projection_pair(height: int):
    pair = SharedHeightPair(height=height)
    first = project_asset_transfer_epoch_position_v1(
        position=AssetTransferEpochPositionV1(pair.source, 0),
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )
    second = project_asset_transfer_epoch_position_v1(
        position=AssetTransferEpochPositionV1(pair.source, 1),
        predecessor=first.post_state,
        occurrence=pair.second.occurrence,
        accepted=pair.second_accepted,
    )
    return pair, first, second


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _capacity_replay_rows(
    count: int,
    occurrence,
) -> tuple[ReplayStateV1, ...]:
    """Build canonical rows that cannot collide with the supplied fresh row."""

    excluded_replay_id = occurrence.replay_id
    excluded_occurrence_id = occurrence.occurrence_id
    rows: list[ReplayStateV1] = []
    index = 0
    while len(rows) < count:
        replay_id = f"capacity-replay-{index:05d}"
        occurrence_id = _root(100_000 + index)
        if replay_id != excluded_replay_id and occurrence_id != excluded_occurrence_id:
            rows.append(ReplayStateV1(replay_id, occurrence_id))
        index += 1
    return tuple(rows)


def _epoch_rejection(projection: AssetTransferEpochProspectiveProjectionV1):
    return _epoch_allocation_binding_reject_v1(
        AssetTransferGlobalAllocationCandidateV1(
            projection.accepted,
            projection.occurrence,
            projection.predecessor,
            projection.post_state,
        ),
        projection.position,
    )


def _assert_exact_frame(
    projection: AssetTransferEpochProspectiveProjectionV1,
    *,
    predecessor,
    occurrence,
    accepted,
) -> None:
    post_state = projection.post_state
    private_post = accepted.private_port.post_state
    expected_replay = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)

    assert post_state.height == occurrence.height
    assert post_state.balances == private_post.balances
    assert post_state.supplies == private_post.supplies
    assert post_state.replay_state == tuple(
        sorted(
            (*predecessor.replay_state, expected_replay),
            key=lambda replay: replay.replay_id,
        )
    )
    assert tuple(
        lane.state_root
        for lane in post_state.lane_roots
        if lane.lane_id is LaneIdV1.ASSET_TRANSFER
    ) == (private_post.state_root,)
    expected_other_lanes = tuple(
        lane for lane in predecessor.lane_roots if lane.lane_id is not LaneIdV1.ASSET_TRANSFER
    )
    assert expected_other_lanes
    assert tuple(
        lane for lane in post_state.lane_roots if lane.lane_id is not LaneIdV1.ASSET_TRANSFER
    ) == expected_other_lanes
    assert (
        post_state.chain_id,
        post_state.deployment_root,
        post_state.writer_epoch,
        post_state.profile_root,
        post_state.custody,
        post_state.liabilities,
        post_state.reserves,
        post_state.oracle_occurrences,
        post_state.terminal_obligations,
        post_state.history_root,
        post_state.outbox,
    ) == (
        predecessor.chain_id,
        predecessor.deployment_root,
        predecessor.writer_epoch,
        predecessor.profile_root,
        predecessor.custody,
        predecessor.liabilities,
        predecessor.reserves,
        predecessor.oracle_occurrences,
        predecessor.terminal_obligations,
        predecessor.history_root,
        predecessor.outbox,
    )


@pytest.mark.parametrize("height", (7, MAX_U64_V1 - 1))
def test_two_actual_custody_transfers_project_expected_shared_height_frames(height: int) -> None:
    pair, first, second = _projection_pair(height)

    # The fixture's first post-state comes from the unchanged adjacent projector.
    assert first.post_state == pair.first_post
    assert second.post_state == pair.second_post
    assert first.post_state.height == second.post_state.height == height + 1
    _assert_exact_frame(
        first,
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )
    _assert_exact_frame(
        second,
        predecessor=first.post_state,
        occurrence=pair.second.occurrence,
        accepted=pair.second_accepted,
    )
    assert _epoch_rejection(first) is None
    assert _epoch_rejection(second) is None


def test_direct_constructor_and_factory_snapshot_every_retained_input() -> None:
    pair = SharedHeightPair(height=7)
    position = AssetTransferEpochPositionV1(pair.source, 0)
    direct = AssetTransferEpochProspectiveProjectionV1(
        position=position,
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )
    factory = project_asset_transfer_epoch_position_v1(
        position=position,
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )
    assert direct == factory
    assert direct.position is not position
    assert direct.position.epoch_source is not pair.source
    assert direct.predecessor is not pair.source
    assert direct.occurrence is not pair.first.occurrence
    assert direct.accepted is not pair.first_accepted
    assert direct.accepted.private_port.post_state is not pair.first_accepted.private_port.post_state
    before = _retained_input_bytes(
        position=direct.position,
        predecessor=direct.predecessor,
        occurrence=direct.occurrence,
        accepted=direct.accepted,
        post_state=direct.post_state,
    )
    expected_post_root = direct.post_state.state_root

    object.__setattr__(pair.source, "height", pair.source.height + 1)
    object.__setattr__(pair.first.occurrence, "height", pair.first.occurrence.height + 1)
    object.__setattr__(pair.first_accepted.private_port.post_state, "balances", ())

    assert _retained_input_bytes(
        position=direct.position,
        predecessor=direct.predecessor,
        occurrence=direct.occurrence,
        accepted=direct.accepted,
        post_state=direct.post_state,
    ) == before
    assert direct.post_state.state_root == expected_post_root

    post_before_retained_probe = canonical_global_bytes_v1(direct.post_state)
    object.__setattr__(direct.predecessor, "height", direct.predecessor.height + 1)
    object.__setattr__(direct.accepted.private_port.post_state, "balances", ())
    assert canonical_global_bytes_v1(direct.post_state) == post_before_retained_probe

    with pytest.raises(TypeError):
        AssetTransferEpochProspectiveProjectionV1(
            position=position,
            predecessor=pair.source,
            occurrence=pair.first.occurrence,
            accepted=pair.first_accepted,
            post_state=pair.source,  # type: ignore[call-arg]
        )


class _ExplosiveValue:
    @property
    def epoch_source(self) -> object:
        raise AssertionError("exact type must reject before property access")


@pytest.mark.parametrize(
    ("field", "message"),
    (
        ("position", "epoch prospective position must have the exact typed value"),
        ("predecessor", "epoch prospective predecessor must have the exact typed value"),
        ("occurrence", "epoch prospective occurrence must have the exact typed value"),
        ("accepted", "epoch prospective acceptance must have the exact typed value"),
    ),
)
def test_public_construction_rejects_exact_type_substitutions_before_property_reads(
    field: str,
    message: str,
) -> None:
    pair = SharedHeightPair(height=7)
    values = {
        "position": AssetTransferEpochPositionV1(pair.source, 0),
        "predecessor": pair.source,
        "occurrence": pair.first.occurrence,
        "accepted": pair.first_accepted,
    }
    values[field] = _ExplosiveValue()
    with pytest.raises(TypeError, match=f"^{message}$"):
        project_asset_transfer_epoch_position_v1(**values)


def test_well_typed_wrong_position_source_is_only_proposal_data_until_relation_rejects() -> None:
    pair = SharedHeightPair(height=7)
    wrong_source = replace(pair.source, height=pair.source.height + 1)
    position = AssetTransferEpochPositionV1(wrong_source, 0)
    before = _retained_input_bytes(
        position=position,
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    projection = project_asset_transfer_epoch_position_v1(
        position=position,
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    assert projection.position.epoch_source == wrong_source
    rejected = _epoch_rejection(projection)
    assert rejected is not None
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    assert _retained_input_bytes(
        position=position,
        predecessor=pair.source,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    ) == before


def test_malformed_exact_nested_inputs_and_duplicate_replay_reject_without_input_change() -> None:
    pair = SharedHeightPair(height=7)
    malformed_position = object.__new__(AssetTransferEpochPositionV1)
    object.__setattr__(malformed_position, "epoch_source", _ExplosiveValue())
    object.__setattr__(malformed_position, "occurrence_index", 0)
    with pytest.raises(TypeError, match="economic refinement state"):
        project_asset_transfer_epoch_position_v1(
            position=malformed_position,
            predecessor=pair.source,
            occurrence=pair.first.occurrence,
            accepted=pair.first_accepted,
        )

    added = ReplayStateV1(pair.first.occurrence.replay_id, pair.first.occurrence.occurrence_id)
    predecessor = replace(
        pair.source,
        replay_state=tuple(
            sorted((*pair.source.replay_state, added), key=lambda replay: replay.replay_id)
        ),
    )
    position = AssetTransferEpochPositionV1(predecessor, 0)
    before = _retained_input_bytes(
        position=position,
        predecessor=predecessor,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )
    with pytest.raises(ValueError, match="global state replay state must be canonically ordered"):
        project_asset_transfer_epoch_position_v1(
            position=position,
            predecessor=predecessor,
            occurrence=pair.first.occurrence,
            accepted=pair.first_accepted,
        )
    assert _retained_input_bytes(
        position=position,
        predecessor=predecessor,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    ) == before


def test_distinct_replay_id_with_duplicate_occurrence_identity_rejects_without_input_change() -> None:
    pair = SharedHeightPair(height=7)
    collision = ReplayStateV1(
        "replay-distinct-occurrence-collision",
        pair.first.occurrence.occurrence_id,
    )
    assert collision.replay_id != pair.first.occurrence.replay_id
    assert all(row.occurrence_id != collision.occurrence_id for row in pair.source.replay_state)
    predecessor = replace(
        pair.source,
        replay_state=tuple(
            sorted((*pair.source.replay_state, collision), key=lambda row: row.replay_id)
        ),
    )
    position = AssetTransferEpochPositionV1(predecessor, 0)
    before = _retained_input_bytes(
        position=position,
        predecessor=predecessor,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    with pytest.raises(ValueError, match="^global state replay occurrence ids must be unique$"):
        project_asset_transfer_epoch_position_v1(
            position=position,
            predecessor=predecessor,
            occurrence=pair.first.occurrence,
            accepted=pair.first_accepted,
        )

    assert _retained_input_bytes(
        position=position,
        predecessor=predecessor,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    ) == before


def test_replay_table_capacity_is_structural_and_leaves_inputs_unchanged() -> None:
    """Builder-valid full states may not bind the accepted journal or source root."""

    pair = SharedHeightPair(height=7)
    rows = _capacity_replay_rows(4096, pair.first.occurrence)
    predecessor_4095 = replace(pair.source, replay_state=rows[:4095])
    position_4095 = AssetTransferEpochPositionV1(predecessor_4095, 0)
    before_4095 = _retained_input_bytes(
        position=position_4095,
        predecessor=predecessor_4095,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    positive = project_asset_transfer_epoch_position_v1(
        position=position_4095,
        predecessor=predecessor_4095,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    added = ReplayStateV1(pair.first.occurrence.replay_id, pair.first.occurrence.occurrence_id)
    assert len(positive.post_state.replay_state) == 4096
    assert positive.post_state.replay_state == tuple(
        sorted((*predecessor_4095.replay_state, added), key=lambda row: row.replay_id)
    )
    assert _retained_input_bytes(
        position=position_4095,
        predecessor=predecessor_4095,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    ) == before_4095

    predecessor_4096 = replace(pair.source, replay_state=rows)
    position_4096 = AssetTransferEpochPositionV1(predecessor_4096, 0)
    before_4096 = _retained_input_bytes(
        position=position_4096,
        predecessor=predecessor_4096,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    with pytest.raises(ValueError, match="^global state replay state exceeds its 4096-item ceiling$"):
        project_asset_transfer_epoch_position_v1(
            position=position_4096,
            predecessor=predecessor_4096,
            occurrence=pair.first.occurrence,
            accepted=pair.first_accepted,
        )

    assert _retained_input_bytes(
        position=position_4096,
        predecessor=predecessor_4096,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    ) == before_4096


def test_max_u64_source_projects_ordinary_data_then_existing_relation_rejects() -> None:
    """This bounds construction arithmetic; it is not a receipt-admission fixture."""

    pair = SharedHeightPair(height=7)
    source = replace(pair.source, height=MAX_U64_V1)
    occurrence = replace(
        pair.first.occurrence,
        height=MAX_U64_V1,
        pre_state_root=source.state_root,
    )
    position = AssetTransferEpochPositionV1(source, 0)
    before = _retained_input_bytes(
        position=position,
        predecessor=source,
        occurrence=occurrence,
        accepted=pair.first_accepted,
    )

    projection = project_asset_transfer_epoch_position_v1(
        position=position,
        predecessor=source,
        occurrence=occurrence,
        accepted=pair.first_accepted,
    )

    assert projection.post_state.height == MAX_U64_V1
    rejected = _epoch_rejection(projection)
    assert rejected is not None
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT
    assert _retained_input_bytes(
        position=position,
        predecessor=source,
        occurrence=occurrence,
        accepted=pair.first_accepted,
    ) == before


def test_projection_preserves_nonempty_typed_frame_without_epoch_admission_claim() -> None:
    """Unsupported tables remain ordinary proposal data for the existing checker."""

    pair = SharedHeightPair(height=7)
    rich_predecessor = replace(
        pair.source,
        reserves=(EconomicAmountV1("treasury", "USD", "reserve", 3),),
        terminal_obligations=(
            TerminalObligationV1(
                "terminal-0001",
                LaneIdV1.ZUSD_MONETARY,
                "claimant",
                "USD",
                2,
                TerminalObligationStatusV1.OPEN,
            ),
        ),
        outbox=(
            OutboxStateV1(
                _root(900),
                "bridge:epoch-projection",
                _root(901),
                _root(902),
                OutboxStatusV1.PENDING,
            ),
        ),
    )
    projection = project_asset_transfer_epoch_position_v1(
        position=AssetTransferEpochPositionV1(rich_predecessor, 0),
        predecessor=rich_predecessor,
        occurrence=pair.first.occurrence,
        accepted=pair.first_accepted,
    )

    assert rich_predecessor.reserves
    assert rich_predecessor.terminal_obligations
    assert rich_predecessor.outbox
    assert projection.post_state.reserves == rich_predecessor.reserves
    assert projection.post_state.terminal_obligations == rich_predecessor.terminal_obligations
    assert projection.post_state.outbox == rich_predecessor.outbox


def test_missing_replay_construction_mutant_is_rejected_by_existing_epoch_relation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pair, first, second = _projection_pair(7)
    assert _epoch_rejection(first) is None
    assert _epoch_rejection(second) is None

    source = inspect.getsource(projection_module._derive_epoch_post_state_v1)
    target = """    owned_replay = tuple(
        sorted(
            (*predecessor.replay_state, added_replay),
            key=lambda replay: replay.replay_id,
        )
    )
"""
    assert source.count(target) == 1, "projection mutation target is no longer unique"
    namespace = dict(vars(projection_module))
    exec(  # noqa: S102 - deliberate local structure-preserving construction mutant
        compile(
            source.replace(target, "    owned_replay = predecessor.replay_state\n", 1),
            "<missing-epoch-replay-mutant>",
            "exec",
        ),
        namespace,
    )
    monkeypatch.setattr(
        projection_module,
        "_derive_epoch_post_state_v1",
        namespace["_derive_epoch_post_state_v1"],
    )
    mutated = project_asset_transfer_epoch_position_v1(
        position=AssetTransferEpochPositionV1(pair.source, 1),
        predecessor=first.post_state,
        occurrence=pair.second.occurrence,
        accepted=pair.second_accepted,
    )
    rejected = _epoch_rejection(mutated)
    assert rejected is not None
    assert rejected.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_REPLAY_CONTINUITY_DRIFT
