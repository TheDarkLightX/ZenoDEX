"""Least-authority owned snapshots for the ZDEX buyback successor leaves.

The adapter revalidates locally derived SHADOW results and copies only the
canonical journal and effect plan needed by a later receipt verifier.  These
snapshots carry no proof, release, route, settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from .global_economic_refinement_snapshot_v1 import _snapshot_effect_plan_v1
from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_spot_buyback_transition_v2 import (
    ZDEXSpotBuybackAcceptedV2,
    ZDEXSpotBuybackJournalV2,
)
from .zdex_tokenomics_buyback_transition_v2 import (
    ZDEXTokenomicsBuybackAcceptedV2,
    ZDEXTokenomicsBuybackJournalV2,
)

ZDEX_SPOT_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2: Final = (
    "zenodex/zdex-spot-buyback-leaf-snapshot/v2"
)
ZDEX_TOKENOMICS_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2: Final = (
    "zenodex/zdex-tokenomics-buyback-leaf-snapshot/v2"
)


def _snapshot_spot_journal_v2(
    journal: ZDEXSpotBuybackJournalV2,
) -> ZDEXSpotBuybackJournalV2:
    if type(journal) is not ZDEXSpotBuybackJournalV2:
        raise TypeError("Spot leaf journal must be exact typed data")
    journal.validate()
    coordinates = replace(journal.context.coordinates)
    context = replace(journal.context, coordinates=coordinates)
    owned = replace(journal, context=context)
    owned.validate()
    return owned


def _snapshot_tokenomics_journal_v2(
    journal: ZDEXTokenomicsBuybackJournalV2,
) -> ZDEXTokenomicsBuybackJournalV2:
    if type(journal) is not ZDEXTokenomicsBuybackJournalV2:
        raise TypeError("Tokenomics leaf journal must be exact typed data")
    journal.validate()
    owned = replace(journal)
    owned.validate()
    return owned


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackLeafSnapshotV2:
    """Owned Spot journal/effects pair without receipt authority."""

    journal: ZDEXSpotBuybackJournalV2
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.journal) is not ZDEXSpotBuybackJournalV2:
            raise TypeError("Spot leaf snapshot journal must be exact typed data")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("Spot leaf snapshot effects must be exact typed data")
        self.journal.validate()
        self.effects.validate()
        writes = self.effects.lane_writes
        coordinates = self.journal.context.coordinates
        if (
            self.journal.effect_plan_root != self.effects.effect_plan_root
            or len(writes) != 1
            or writes[0].lane_id is not LaneIdV1.SPOT_LIQUIDITY
            or writes[0].pre_root != coordinates.spot_pre_state_root
            or writes[0].post_root != self.journal.post_state_root
        ):
            raise ValueError("Spot lane write or effect binding is inconsistent")
        if self.effects.occurrence_consumptions:
            raise ValueError("Spot leaf must not consume the route occurrence")
        if self.effects.external_outbox_enqueue:
            raise ValueError("Spot leaf must not enqueue an external effect")

    @property
    def journal_bytes(self) -> bytes:
        self.validate()
        return canonical_global_bytes_v1(self.journal)

    @property
    def journal_root(self) -> str:
        return self.journal.journal_root

    @property
    def effect_plan_root(self) -> str:
        return self.effects.effect_plan_root

    @property
    def snapshot_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-spot-buyback-leaf-snapshot-v2",
            {
                "schema": ZDEX_SPOT_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2,
                "journal_root": self.journal_root,
                "effect_plan_root": self.effect_plan_root,
            },
        )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackLeafSnapshotV2:
    """Owned Tokenomics journal/effects pair without receipt authority."""

    journal: ZDEXTokenomicsBuybackJournalV2
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.journal) is not ZDEXTokenomicsBuybackJournalV2:
            raise TypeError("Tokenomics leaf snapshot journal must be exact typed data")
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("Tokenomics leaf snapshot effects must be exact typed data")
        self.journal.validate()
        self.effects.validate()
        writes = self.effects.lane_writes
        if (
            self.journal.effect_plan_root != self.effects.effect_plan_root
            or len(writes) != 1
            or writes[0].lane_id is not LaneIdV1.ZDEX_TOKENOMICS
            or writes[0].pre_root != self.journal.pre_state_root
            or writes[0].post_root != self.journal.post_state_root
        ):
            raise ValueError("Tokenomics lane write or effect binding is inconsistent")
        if len(self.effects.occurrence_consumptions) != 1:
            raise ValueError("Tokenomics leaf must carry one occurrence consumption")
        if self.effects.external_outbox_enqueue:
            raise ValueError("Tokenomics leaf must not enqueue an external effect")

    @property
    def journal_bytes(self) -> bytes:
        self.validate()
        return canonical_global_bytes_v1(self.journal)

    @property
    def journal_root(self) -> str:
        return self.journal.journal_root

    @property
    def effect_plan_root(self) -> str:
        return self.effects.effect_plan_root

    @property
    def snapshot_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-tokenomics-buyback-leaf-snapshot-v2",
            {
                "schema": ZDEX_TOKENOMICS_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2,
                "journal_root": self.journal_root,
                "effect_plan_root": self.effect_plan_root,
            },
        )


def snapshot_zdex_spot_buyback_leaf_v2(
    accepted: ZDEXSpotBuybackAcceptedV2,
) -> ZDEXSpotBuybackLeafSnapshotV2:
    """Revalidate and own the exact Spot projection read by receipt admission."""

    if type(accepted) is not ZDEXSpotBuybackAcceptedV2:
        raise TypeError("Spot leaf adapter requires an exact accepted result")
    accepted.validate()
    journal = _snapshot_spot_journal_v2(accepted.journal)
    effects = _snapshot_effect_plan_v1(accepted.effects)
    accepted.validate()
    return ZDEXSpotBuybackLeafSnapshotV2(journal, effects)


def snapshot_zdex_tokenomics_buyback_leaf_v2(
    accepted: ZDEXTokenomicsBuybackAcceptedV2,
) -> ZDEXTokenomicsBuybackLeafSnapshotV2:
    """Revalidate and own the exact Tokenomics projection read by receipt admission."""

    if type(accepted) is not ZDEXTokenomicsBuybackAcceptedV2:
        raise TypeError("Tokenomics leaf adapter requires an exact accepted result")
    accepted.validate()
    journal = _snapshot_tokenomics_journal_v2(accepted.journal)
    effects = _snapshot_effect_plan_v1(accepted.effects)
    accepted.validate()
    return ZDEXTokenomicsBuybackLeafSnapshotV2(journal, effects)


__all__ = [
    "ZDEX_SPOT_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2",
    "ZDEX_TOKENOMICS_BUYBACK_LEAF_SNAPSHOT_SCHEMA_V2",
    "ZDEXSpotBuybackLeafSnapshotV2",
    "ZDEXTokenomicsBuybackLeafSnapshotV2",
    "snapshot_zdex_spot_buyback_leaf_v2",
    "snapshot_zdex_tokenomics_buyback_leaf_v2",
]
