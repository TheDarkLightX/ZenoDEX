"""Canonical leaf effect projections for ZDEX purchase-to-burn."""

from __future__ import annotations

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
    ZDEXBurnJournalV1,
)


def purchase_effects_v1(
    journal: ZDEXAMMPurchaseJournalV1,
) -> GlobalEconomicEffectPlanV1:
    """Project the exact two-asset movement proved by the Spot leaf."""

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


def burn_effects_v1(journal: ZDEXBurnJournalV1) -> GlobalEconomicEffectPlanV1:
    """Project the exact supply and transient-bucket reduction of the burn leaf."""

    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.BURN,
                    ZDEX_SUPPLY_PRINCIPAL_V1,
                    journal.zdex_asset_id,
                    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
                    -journal.burned_zdex_atoms,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.CUSTODY,
                    journal.burn_bucket_id,
                    journal.zdex_asset_id,
                    PROTOCOL_BURN_CUSTODY_DOMAIN_V1,
                    -journal.burned_zdex_atoms,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows,
        (
            AssetConservationRowV1(
                journal.zdex_asset_id,
                journal.zdex_owned_pre_atoms,
                journal.zdex_owned_post_atoms,
                journal.zdex_supply_pre_atoms,
                journal.zdex_supply_post_atoms,
                0,
                journal.burned_zdex_atoms,
            ),
        ),
        (),
        (
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                journal.pre_tokenomics_lane_root,
                journal.post_tokenomics_lane_root,
            ),
        ),
        (journal.command_occurrence_id,),
        (),
    )


__all__ = ["burn_effects_v1", "purchase_effects_v1"]
