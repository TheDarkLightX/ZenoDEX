"""Pure, restricted module-to-global allocation relation.

The caller must authenticate the complete, adjacent committed snapshots. This
module checks their content and the explicit occurrence relation; it confers no
store authority. The receipt admission owner separately binds the accepted
private port to a verified module journal before minting a fragment.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from .asset_transfer_epoch_position_v1 import AssetTransferEpochPositionV1
from .asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1
from .global_accounting_allocation_certificate_v1 import ClaimantEntitlementRowV1
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_settlement_types_v1 import GlobalEconomicStateV1, LaneIdV1, ReplayStateV1


class GlobalAllocationBindingRejectCodeV1(str, Enum):
    GLOBAL_CONTEXT_DRIFT = "GLOBAL_CONTEXT_DRIFT"
    GLOBAL_OCCURRENCE_DRIFT = "GLOBAL_OCCURRENCE_DRIFT"
    GLOBAL_LANE_SCOPE_UNSUPPORTED = "GLOBAL_LANE_SCOPE_UNSUPPORTED"
    GLOBAL_LANE_ROOT_DRIFT = "GLOBAL_LANE_ROOT_DRIFT"
    GLOBAL_PROJECTION_ROWS_DRIFT = "GLOBAL_PROJECTION_ROWS_DRIFT"
    GLOBAL_CLAIMANT_CONTINUITY_DRIFT = "GLOBAL_CLAIMANT_CONTINUITY_DRIFT"
    GLOBAL_UNSUPPORTED_STATE = "GLOBAL_UNSUPPORTED_STATE"
    GLOBAL_REPLAY_CONTINUITY_DRIFT = "GLOBAL_REPLAY_CONTINUITY_DRIFT"


class _GlobalAllocationHeightModeV1(Enum):
    ADJACENT_STATE = "ADJACENT_STATE"
    EPOCH_POSITION = "EPOCH_POSITION"


@dataclass(frozen=True, slots=True)
class GlobalAllocationBindingRejectedV1:
    code: GlobalAllocationBindingRejectCodeV1

    def __post_init__(self) -> None:
        if type(self.code) is not GlobalAllocationBindingRejectCodeV1:
            raise TypeError("global allocation binding reject must be a closed code")


@dataclass(frozen=True, slots=True)
class AssetTransferGlobalAllocationCandidateV1:
    """Caller-owned complete relation inputs; construction confers no authority."""

    accepted: AssetTransferLaneModuleAcceptedV1
    occurrence: EconomicCommandOccurrenceV1
    predecessor: GlobalEconomicStateV1
    current: GlobalEconomicStateV1


def _same_global_context_v1(
    accepted: AssetTransferLaneModuleAcceptedV1,
    occurrence: EconomicCommandOccurrenceV1,
    predecessor: GlobalEconomicStateV1,
    current: GlobalEconomicStateV1,
) -> bool:
    journal = accepted.module_journal
    context = (journal.chain_id, journal.deployment_root, journal.profile_root)
    return (
        occurrence.chain_id,
        occurrence.deployment_root,
        occurrence.profile_root,
    ) == context and all(
        (state.chain_id, state.deployment_root, state.profile_root) == context
        and state.writer_epoch == journal.writer_epoch
        for state in (predecessor, current)
    )


def _global_allocation_binding_reject_v1(
    accepted: AssetTransferLaneModuleAcceptedV1,
    occurrence: EconomicCommandOccurrenceV1,
    predecessor: GlobalEconomicStateV1,
    current: GlobalEconomicStateV1,
    height_mode: _GlobalAllocationHeightModeV1 = _GlobalAllocationHeightModeV1.ADJACENT_STATE,
) -> GlobalAllocationBindingRejectedV1 | None:
    """Check owned values in the ordered Python/Rust rejection family.

    The contiguous guard body retains standalone semantic-mutant coverage. Its
    fifth, private parameter is selected only after the epoch-position guard;
    the small length/parameter budget overrun preserves that auditable order.
    """
    code = GlobalAllocationBindingRejectCodeV1
    if (height_mode is not _GlobalAllocationHeightModeV1.ADJACENT_STATE
            and height_mode is not _GlobalAllocationHeightModeV1.EPOCH_POSITION):
        # Same-type Enum instances can be forged in Python; retained tests reach
        # this branch even though static enum exhaustiveness hides it.
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_OCCURRENCE_DRIFT)  # type: ignore[unreachable]
    journal = accepted.module_journal
    if not _same_global_context_v1(accepted, occurrence, predecessor, current):
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_CONTEXT_DRIFT)
    if (
        occurrence.occurrence_id != journal.command_occurrence_id
        or occurrence.pre_state_root != predecessor.state_root
        or occurrence.height != current.height
        or (height_mode is _GlobalAllocationHeightModeV1.ADJACENT_STATE
            and predecessor.height + 1 != current.height)
    ):
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_OCCURRENCE_DRIFT)
    for state in (predecessor, current):
        if tuple(row.lane_id for row in state.lane_roots if row.enabled) != (
            LaneIdV1.ASSET_TRANSFER,
        ):
            return GlobalAllocationBindingRejectedV1(code.GLOBAL_LANE_SCOPE_UNSUPPORTED)
        if state.lane_roots[0].module_release_id != journal.module_release_id:
            return GlobalAllocationBindingRejectedV1(code.GLOBAL_LANE_SCOPE_UNSUPPORTED)
    if predecessor.lane_roots[1:] != current.lane_roots[1:]:
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_LANE_SCOPE_UNSUPPORTED)
    for state, projection in (
        (predecessor, accepted.private_port.pre_state),
        (current, accepted.private_port.post_state),
    ):
        if state.lane_roots[0].state_root != projection.state_root:
            return GlobalAllocationBindingRejectedV1(code.GLOBAL_LANE_ROOT_DRIFT)
        if (state.balances, state.custody, state.supplies) != (
            projection.balances,
            projection.custody,
            projection.supplies,
        ):
            return GlobalAllocationBindingRejectedV1(code.GLOBAL_PROJECTION_ROWS_DRIFT)
    if predecessor.liabilities != current.liabilities:
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_CLAIMANT_CONTINUITY_DRIFT)
    if (
        predecessor.custody != current.custody
        or predecessor.history_root != current.history_root
        or predecessor.oracle_occurrences != current.oracle_occurrences
        or any(
            state.reserves or state.outbox or state.terminal_obligations
            for state in (predecessor, current)
        )
    ):
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_UNSUPPORTED_STATE)
    added = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    if any(
        row.replay_id == added.replay_id or row.occurrence_id == added.occurrence_id
        for row in predecessor.replay_state
    ) or current.replay_state != tuple(sorted((*predecessor.replay_state, added))):
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_REPLAY_CONTINUITY_DRIFT)
    return None


def _epoch_allocation_binding_reject_v1(
    candidate: AssetTransferGlobalAllocationCandidateV1,
    position: AssetTransferEpochPositionV1,
) -> GlobalAllocationBindingRejectedV1 | None:
    """Check an owned position before selecting the shared epoch height mode.

    Source authenticity and earlier pair association remain consumer premises.
    No state, occurrence, height or committed root is normalized here.
    """
    source = position.epoch_source
    accepted, command = candidate.accepted, candidate.occurrence
    prior, post = candidate.predecessor, candidate.current
    if not _same_global_context_v1(accepted, command, source, source):
        return GlobalAllocationBindingRejectedV1(GlobalAllocationBindingRejectCodeV1.GLOBAL_CONTEXT_DRIFT)
    target_height = source.height + 1
    expected_prior_height = source.height if position.occurrence_index == 0 else target_height
    if (command.height != target_height or post.height != target_height
            or prior.height != expected_prior_height
            or (position.occurrence_index == 0 and prior != source)):
        return GlobalAllocationBindingRejectedV1(GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT)
    return _global_allocation_binding_reject_v1(
        accepted, command, prior, post, _GlobalAllocationHeightModeV1.EPOCH_POSITION,
    )


def _derived_global_entitlements_v1(
    predecessor: GlobalEconomicStateV1,
) -> tuple[ClaimantEntitlementRowV1, ...]:
    """Preserve every claimant and amount from the committed state partition."""
    return tuple(
        ClaimantEntitlementRowV1(row.asset, row.owner, row.custody_domain, row.amount_atoms)
        for row in predecessor.liabilities
    )
