use crate::canonical::{AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::release::LaneIdV1;
use crate::zdex_purchase_burn_types::{
    ZDEXAMMPurchaseJournalV1, ZDEXBurnJournalV1, AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BURN_CUSTODY_DOMAIN_V1, PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1, ZDEX_SUPPLY_PRINCIPAL_V1,
};

fn effect_kind_label_v1(kind: EconomicEffectKindV1) -> &'static str {
    match kind {
        EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV1::ISSUE => "ISSUE",
        EconomicEffectKindV1::BURN => "BURN",
        EconomicEffectKindV1::CUSTODY => "CUSTODY",
        EconomicEffectKindV1::LIABILITY => "LIABILITY",
        EconomicEffectKindV1::RESERVE => "RESERVE",
        EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV1::REWARD => "REWARD",
        EconomicEffectKindV1::SLASH => "SLASH",
    }
}

fn sort_effect_rows_v1(rows: &mut [EconomicEffectRowV1]) {
    rows.sort_by(|left, right| {
        (
            effect_kind_label_v1(left.kind),
            left.asset.as_str(),
            left.principal.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                effect_kind_label_v1(right.kind),
                right.asset.as_str(),
                right.principal.as_str(),
                right.custody_domain.as_str(),
            ))
    });
}

fn positive_i128_v1(value: u128) -> AbiResultV1<i128> {
    i128::try_from(value).map_err(|_| AbiErrorV1::InvalidBounds("ZDEX effect amount"))
}

pub(crate) fn purchase_effects_v1(
    journal: &ZDEXAMMPurchaseJournalV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    journal.validate()?;
    let quote = positive_i128_v1(journal.quote_amount_in_atoms)?;
    let purchased = positive_i128_v1(journal.purchased_zdex_atoms)?;
    let mut rows = vec![
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::CUSTODY,
            principal: journal.quote_source_bucket_id.clone(),
            asset: journal.quote_asset_id.to_string(),
            custody_domain: PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: -quote,
        },
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::CUSTODY,
            principal: journal.quote_pool_bucket_id.clone(),
            asset: journal.quote_asset_id.to_string(),
            custody_domain: AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: quote,
        },
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::CUSTODY,
            principal: journal.zdex_pool_bucket_id.clone(),
            asset: journal.zdex_asset_id.to_string(),
            custody_domain: AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: -purchased,
        },
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::CUSTODY,
            principal: journal.burn_bucket_id.clone(),
            asset: journal.zdex_asset_id.to_string(),
            custody_domain: PROTOCOL_BURN_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: purchased,
        },
    ];
    sort_effect_rows_v1(&mut rows);
    let mut asset_conservation = vec![
        AssetConservationRowV1 {
            asset: journal.quote_asset_id.to_string(),
            owned_and_custodied_pre_atoms: journal.quote_owned_atoms,
            owned_and_custodied_post_atoms: journal.quote_owned_atoms,
            supply_pre_atoms: journal.quote_supply_atoms,
            supply_post_atoms: journal.quote_supply_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        },
        AssetConservationRowV1 {
            asset: journal.zdex_asset_id.to_string(),
            owned_and_custodied_pre_atoms: journal.zdex_owned_atoms,
            owned_and_custodied_post_atoms: journal.zdex_owned_atoms,
            supply_pre_atoms: journal.zdex_supply_atoms,
            supply_post_atoms: journal.zdex_supply_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        },
    ];
    asset_conservation.sort_by(|left, right| left.asset.cmp(&right.asset));
    let plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows,
        asset_conservation,
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::SPOT_LIQUIDITY,
            pre_root: journal.pre_spot_lane_root.clone(),
            post_root: journal.post_spot_lane_root.clone(),
        }],
        occurrence_consumptions: vec![journal.command_occurrence_id.clone()],
        external_outbox_enqueue: vec![],
    };
    plan.validate()?;
    Ok(plan)
}

pub(crate) struct ZDEXBurnEffectInputsV1<'a> {
    pub command_occurrence_id: &'a RootV1,
    pub zdex_asset_id: &'a RootV1,
    pub burn_bucket_id: &'a str,
    pub burned_zdex_atoms: u128,
    pub zdex_owned_pre_atoms: u128,
    pub zdex_owned_post_atoms: u128,
    pub zdex_supply_pre_atoms: u128,
    pub zdex_supply_post_atoms: u128,
    pub pre_tokenomics_lane_root: &'a RootV1,
    pub post_tokenomics_lane_root: &'a RootV1,
}

pub(crate) fn burn_effects_from_inputs_v1(
    inputs: &ZDEXBurnEffectInputsV1<'_>,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let burned = positive_i128_v1(inputs.burned_zdex_atoms)?;
    let mut rows = vec![
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::BURN,
            principal: ZDEX_SUPPLY_PRINCIPAL_V1.to_owned(),
            asset: inputs.zdex_asset_id.to_string(),
            custody_domain: PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: -burned,
        },
        EconomicEffectRowV1 {
            kind: EconomicEffectKindV1::CUSTODY,
            principal: inputs.burn_bucket_id.to_owned(),
            asset: inputs.zdex_asset_id.to_string(),
            custody_domain: PROTOCOL_BURN_CUSTODY_DOMAIN_V1.to_owned(),
            delta_atoms: -burned,
        },
    ];
    sort_effect_rows_v1(&mut rows);
    let plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows,
        asset_conservation: vec![AssetConservationRowV1 {
            asset: inputs.zdex_asset_id.to_string(),
            owned_and_custodied_pre_atoms: inputs.zdex_owned_pre_atoms,
            owned_and_custodied_post_atoms: inputs.zdex_owned_post_atoms,
            supply_pre_atoms: inputs.zdex_supply_pre_atoms,
            supply_post_atoms: inputs.zdex_supply_post_atoms,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: inputs.burned_zdex_atoms,
        }],
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: inputs.pre_tokenomics_lane_root.clone(),
            post_root: inputs.post_tokenomics_lane_root.clone(),
        }],
        occurrence_consumptions: vec![inputs.command_occurrence_id.clone()],
        external_outbox_enqueue: vec![],
    };
    plan.validate()?;
    Ok(plan)
}

pub(crate) fn burn_effects_v1(
    journal: &ZDEXBurnJournalV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    journal.validate()?;
    burn_effects_from_inputs_v1(&ZDEXBurnEffectInputsV1 {
        command_occurrence_id: &journal.command_occurrence_id,
        zdex_asset_id: &journal.zdex_asset_id,
        burn_bucket_id: &journal.burn_bucket_id,
        burned_zdex_atoms: journal.burned_zdex_atoms,
        zdex_owned_pre_atoms: journal.zdex_owned_pre_atoms,
        zdex_owned_post_atoms: journal.zdex_owned_post_atoms,
        zdex_supply_pre_atoms: journal.zdex_supply_pre_atoms,
        zdex_supply_post_atoms: journal.zdex_supply_post_atoms,
        pre_tokenomics_lane_root: &journal.pre_tokenomics_lane_root,
        post_tokenomics_lane_root: &journal.post_tokenomics_lane_root,
    })
}
