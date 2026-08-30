"""Canonical leaf effect projections for ZDEX purchase-to-burn."""

from __future__ import annotations

from dataclasses import dataclass

from .global_settlement_types_v1 import (
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BURN_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1,
)


def _purchase_effects_from_journal_v1(
    journal: ZDEXAMMPurchaseJournalV1 | ZDEXAMMPurchaseJournalV2,
) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.quote_source_bucket_id,
                    journal.quote_asset_id,
                    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
                    -journal.quote_amount_in_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.quote_pool_bucket_id,
                    journal.quote_asset_id,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    journal.quote_amount_in_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.zdex_pool_bucket_id,
                    journal.zdex_asset_id,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    -journal.purchased_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.burn_bucket_id,
                    journal.zdex_asset_id,
                    PROTOCOL_BURN_CUSTODY_DOMAIN_V1,
                    journal.purchased_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    conservation = tuple(
        sorted(
            (
                AssetConservationRowV1(
                    journal.quote_asset_id,
                    journal.quote_owned_atoms,
                    journal.quote_owned_atoms,
                    journal.quote_supply_atoms,
                    journal.quote_supply_atoms,
                    0,
                    0,
                ),
                AssetConservationRowV1(
                    journal.zdex_asset_id,
                    journal.zdex_owned_atoms,
                    journal.zdex_owned_atoms,
                    journal.zdex_supply_atoms,
                    journal.zdex_supply_atoms,
                    0,
                    0,
                ),
            ),
            key=lambda row: row.asset,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows,
        conservation,
        (),
        (
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                journal.pre_spot_lane_root,
                journal.post_spot_lane_root,
            ),
        ),
        (journal.command_occurrence_id,),
        (),
    )


def purchase_effects_v1(
    journal: ZDEXAMMPurchaseJournalV1,
) -> GlobalEconomicEffectPlanV1:
    """Project the exact two-asset movement proved by a V1 Spot leaf."""

    if type(journal) is not ZDEXAMMPurchaseJournalV1:
        raise TypeError("ZDEX purchase V1 effects require an exact purchase journal")
    journal.validate()
    return _purchase_effects_from_journal_v1(journal)


def purchase_effects_v2(
    journal: ZDEXAMMPurchaseJournalV2,
) -> GlobalEconomicEffectPlanV1:
    """Project the same accounting movement from the authority-bound V2 leaf."""

    if type(journal) is not ZDEXAMMPurchaseJournalV2:
        raise TypeError("ZDEX purchase V2 effects require an exact purchase journal")
    journal.validate()
    return _purchase_effects_from_journal_v1(journal)


@dataclass(frozen=True, slots=True)
class _ZDEXBurnEffectInputsV1:
    command_occurrence_id: str
    zdex_asset_id: str
    burn_bucket_id: str
    burned_zdex_atoms: int
    zdex_owned_pre_atoms: int
    zdex_owned_post_atoms: int
    zdex_supply_pre_atoms: int
    zdex_supply_post_atoms: int


def _burn_effects_from_values_v1(
    inputs: _ZDEXBurnEffectInputsV1,
) -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.BURN,
                    ZDEX_SUPPLY_PRINCIPAL_V1,
                    inputs.zdex_asset_id,
                    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
                    -inputs.burned_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    inputs.burn_bucket_id,
                    inputs.zdex_asset_id,
                    PROTOCOL_BURN_CUSTODY_DOMAIN_V1,
                    -inputs.burned_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows,
        (
            AssetConservationRowV1(
                inputs.zdex_asset_id,
                inputs.zdex_owned_pre_atoms,
                inputs.zdex_owned_post_atoms,
                inputs.zdex_supply_pre_atoms,
                inputs.zdex_supply_post_atoms,
                0,
                inputs.burned_zdex_atoms,
            ),
        ),
        (),
        (),
        (inputs.command_occurrence_id,),
        (),
    )


def burn_effects_v1(journal: ZDEXBurnJournalV1) -> GlobalEconomicEffectPlanV1:
    """Project the exact supply and transient-bucket reduction of the burn leaf."""

    if type(journal) is not ZDEXBurnJournalV1:
        raise TypeError("ZDEX burn effects require an exact burn journal")
    journal.validate()
    return _burn_effects_from_values_v1(
        _ZDEXBurnEffectInputsV1(
            command_occurrence_id=journal.command_occurrence_id,
            zdex_asset_id=journal.zdex_asset_id,
            burn_bucket_id=journal.burn_bucket_id,
            burned_zdex_atoms=journal.burned_zdex_atoms,
            zdex_owned_pre_atoms=journal.zdex_owned_pre_atoms,
            zdex_owned_post_atoms=journal.zdex_owned_post_atoms,
            zdex_supply_pre_atoms=journal.zdex_supply_pre_atoms,
            zdex_supply_post_atoms=journal.zdex_supply_post_atoms,
        )
    )


__all__ = ["burn_effects_v1", "purchase_effects_v1", "purchase_effects_v2"]
