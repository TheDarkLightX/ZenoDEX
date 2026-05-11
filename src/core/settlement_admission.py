"""
Settlement admission boundary for the batch-clearing core.

This module separates structural admission from settlement math. It preserves
the legacy settlement behavior: malformed non-CREATE_POOL intents without a
usable pool_id are rejected with ``INVALID_INTENT`` after pool-scoped intents
have been processed.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ..state.intents import Intent, IntentKind
from .settlement import Fill, FillAction

INVALID_SETTLEMENT_INTENT_REASON = "INVALID_INTENT"


@dataclass(frozen=True)
class AdmittedPoolIntent:
    """Intent admitted into a specific pool-scoped clearing group."""

    pool_id: str
    intent: Intent


@dataclass(frozen=True)
class RejectedSettlementIntent:
    """Intent rejected before it reaches pool-scoped clearing math."""

    intent: Intent
    reason: str = INVALID_SETTLEMENT_INTENT_REASON

    def to_fill(self) -> Fill:
        return Fill(intent_id=self.intent.intent_id, action=FillAction.REJECT, reason=self.reason)


@dataclass(frozen=True)
class SettlementAdmission:
    """Result of the deterministic settlement admission pass."""

    create_pool_intents: tuple[Intent, ...]
    pool_intents: tuple[AdmittedPoolIntent, ...]
    rejected_intents: tuple[RejectedSettlementIntent, ...]

    def intents_by_pool(self) -> dict[str, list[Intent]]:
        grouped: dict[str, list[Intent]] = {}
        for admitted in self.pool_intents:
            grouped.setdefault(admitted.pool_id, []).append(admitted.intent)
        return grouped


def admit_settlement_intents(intents: Sequence[Intent]) -> SettlementAdmission:
    """
    Classify raw parsed intents before settlement math runs.

    CREATE_POOL intents are admitted through their own lane because a batch may
    create a pool and then consume it. Other intents must carry a non-empty
    string ``pool_id`` to reach pool-scoped clearing.
    """

    create_pool_intents: list[Intent] = []
    pool_intents: list[AdmittedPoolIntent] = []
    rejected_intents: list[RejectedSettlementIntent] = []

    for intent in intents:
        if intent.kind == IntentKind.CREATE_POOL:
            create_pool_intents.append(intent)
            continue

        pool_id = intent.get_field("pool_id")
        if isinstance(pool_id, str) and pool_id:
            pool_intents.append(AdmittedPoolIntent(pool_id=pool_id, intent=intent))
            continue

        rejected_intents.append(RejectedSettlementIntent(intent=intent))

    return SettlementAdmission(
        create_pool_intents=tuple(create_pool_intents),
        pool_intents=tuple(pool_intents),
        rejected_intents=tuple(rejected_intents),
    )
