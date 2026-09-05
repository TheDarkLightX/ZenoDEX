"""Pure, restricted module-to-global allocation relation.

The caller must authenticate the complete, adjacent committed snapshots. This
module checks their content and the explicit occurrence relation; it confers no
store authority. The receipt admission owner separately binds the accepted
private port to a verified module journal before minting a fragment.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

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
) -> GlobalAllocationBindingRejectedV1 | None:
    """Check owned values in the ordered Python/Rust rejection family."""
    code = GlobalAllocationBindingRejectCodeV1
    journal = accepted.module_journal
    if not _same_global_context_v1(accepted, occurrence, predecessor, current):
        return GlobalAllocationBindingRejectedV1(code.GLOBAL_CONTEXT_DRIFT)
    if (
        occurrence.occurrence_id != journal.command_occurrence_id
        or occurrence.pre_state_root != predecessor.state_root
        or occurrence.height != current.height
        or predecessor.height + 1 != current.height
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


def _derived_global_entitlements_v1(
    predecessor: GlobalEconomicStateV1,
) -> tuple[ClaimantEntitlementRowV1, ...]:
    """Preserve every claimant and amount from the committed state partition."""
    return tuple(
        ClaimantEntitlementRowV1(row.asset, row.owner, row.custody_domain, row.amount_atoms)
        for row in predecessor.liabilities
    )
