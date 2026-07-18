"""Pure lifecycle guard shared by isolated perps engine versions.

The guard captures cross-action behavior that must not be weakened by an
adapter: a published price must settle before epoch advancement, and settlement
must use a seen, positive, sufficiently fresh oracle snapshot.
"""

from __future__ import annotations

from .perp_v2.math import is_settle_oracle_usable
from .perp_v2.types import Action, EpochPhase, PerpState


def epoch_lifecycle_reject_reason(
    state: PerpState,
    action: Action,
) -> str | None:
    """Return a stable lifecycle rejection reason, or ``None`` when allowed."""

    if action is Action.ADVANCE_EPOCH:
        if state.epoch_phase is EpochPhase.PRICE_PUBLISHED:
            return "pending_settlement"
        return None

    if action is Action.SETTLE_EPOCH and not is_settle_oracle_usable(
        state.now_epoch,
        state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs,
        state.oracle_seen,
        state.index_price_e8,
    ):
        return "unusable_oracle"

    return None


__all__ = ["epoch_lifecycle_reject_reason"]
