"""Data-only prospective state construction for one asset epoch position.

This module derives an immutable candidate post state from an owned predecessor,
occurrence, and custody-complete module acceptance. The existing epoch allocation
and receipt-admission consumers retain source, position, receipt, authorization,
and semantic replay decisions for structurally constructible proposals. A
projection is ordinary proposal data and grants no verification, store,
publication, or mounted multi-command authority.

The reconstructed global state retains its structural validation: duplicate
replay or occurrence identities and replay-table capacity overflow raise
``ValueError`` during construction; malformed types or values can raise
``TypeError`` or ``ValueError``. This unmounted data constructor does not
translate those failures.
A mounted boundary must establish replay freshness first or translate the exact
construction failures into its typed rejection before exposing the operation.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace

from .asset_transfer_epoch_position_v1 import (
    AssetTransferEpochPositionV1,
    _snapshot_epoch_position_v1,
)
from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    _snapshot_asset_transfer_lane_module_accepted_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import GlobalEconomicStateV1, LaneIdV1, ReplayStateV1


@dataclass(frozen=True, slots=True)
class AssetTransferEpochProspectiveProjectionV1:
    """Owned inputs and their input-derived proposed global post state.

    ``post_state`` is derived during construction. The constructor first
    exact-type checks the top-level position, predecessor, occurrence, and
    acceptance in that order, then snapshots and revalidates those inputs in
    the same order before reading nested fields. It deliberately does not
    authenticate the epoch source, select an index, verify receipts, or establish
    that a later consumer may commit the data. It also does not establish replay
    freshness: structural output construction raises ``ValueError`` before the
    allocation relation for duplicate replay/occurrence identities or a full
    replay table. A mounted caller must establish freshness or translate those
    exact construction failures before exposing an operation result.
    """

    position: AssetTransferEpochPositionV1
    predecessor: GlobalEconomicStateV1
    occurrence: EconomicCommandOccurrenceV1
    accepted: AssetTransferLaneModuleAcceptedV1
    post_state: GlobalEconomicStateV1 = field(init=False)

    def __post_init__(self) -> None:
        position = self.position
        predecessor = self.predecessor
        occurrence = self.occurrence
        accepted = self.accepted
        if type(position) is not AssetTransferEpochPositionV1:
            raise TypeError("epoch prospective position must have the exact typed value")
        if type(predecessor) is not GlobalEconomicStateV1:
            raise TypeError("epoch prospective predecessor must have the exact typed value")
        if type(occurrence) is not EconomicCommandOccurrenceV1:
            raise TypeError("epoch prospective occurrence must have the exact typed value")
        if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
            raise TypeError("epoch prospective acceptance must have the exact typed value")

        owned_position = _snapshot_epoch_position_v1(position)
        owned_predecessor = _snapshot_state_v1(predecessor)
        owned_occurrence = _snapshot_occurrence_v1(occurrence)
        owned_accepted = _snapshot_asset_transfer_lane_module_accepted_v1(accepted)
        post_state = _derive_epoch_post_state_v1(
            predecessor=owned_predecessor,
            occurrence=owned_occurrence,
            accepted=owned_accepted,
        )
        object.__setattr__(self, "position", owned_position)
        object.__setattr__(self, "predecessor", owned_predecessor)
        object.__setattr__(self, "occurrence", owned_occurrence)
        object.__setattr__(self, "accepted", owned_accepted)
        object.__setattr__(self, "post_state", post_state)


def _derive_epoch_post_state_v1(
    *,
    predecessor: GlobalEconomicStateV1,
    occurrence: EconomicCommandOccurrenceV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> GlobalEconomicStateV1:
    """Derive only the prospective fields delegated to this constructor."""

    private_post = accepted.private_port.post_state
    lane_roots = tuple(
        replace(lane, state_root=private_post.state_root)
        if lane.lane_id is LaneIdV1.ASSET_TRANSFER
        else lane
        for lane in predecessor.lane_roots
    )
    added_replay = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    owned_replay = tuple(
        sorted(
            (*predecessor.replay_state, added_replay),
            key=lambda replay: replay.replay_id,
        )
    )
    return _snapshot_state_v1(
        replace(
            predecessor,
            height=occurrence.height,
            lane_roots=lane_roots,
            balances=private_post.balances,
            supplies=private_post.supplies,
            replay_state=owned_replay,
        )
    )


def project_asset_transfer_epoch_position_v1(
    *,
    position: AssetTransferEpochPositionV1,
    predecessor: GlobalEconomicStateV1,
    occurrence: EconomicCommandOccurrenceV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> AssetTransferEpochProspectiveProjectionV1:
    """Return one fully owned, input-derived prospective epoch position.

    The result updates only the occurrence height, asset lane root, balances,
    supplies, and canonical replay tuple. It preserves every other predecessor
    field. Existing consumers decide source authentication, position semantics,
    receipt admission, and any later publication. For structurally constructible
    proposals they also decide semantic replay continuity; direct replay
    collisions can instead be rejected during state construction as documented
    on the value type. A schema-valid full-state input can remain admission-invalid
    when its supplied context or roots do not bind; constructing it does not imply
    a mounted or admitted operation.
    """

    return AssetTransferEpochProspectiveProjectionV1(
        position=position,
        predecessor=predecessor,
        occurrence=occurrence,
        accepted=accepted,
    )


__all__ = [
    "AssetTransferEpochProspectiveProjectionV1",
    "project_asset_transfer_epoch_position_v1",
]
