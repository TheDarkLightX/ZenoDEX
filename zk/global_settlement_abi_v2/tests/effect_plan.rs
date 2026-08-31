use zenodex_global_settlement_abi_v2::{
    AssetConservationRowV2, EconomicEffectKindV2, EconomicEffectRowV2, GlobalEconomicEffectPlanV2,
    GLOBAL_SETTLEMENT_ABI_V2,
};

#[test]
fn cancelling_issue_and_burn_at_u128_max_is_valid() {
    let plan = GlobalEconomicEffectPlanV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        rows: vec![
            EconomicEffectRowV2 {
                kind: EconomicEffectKindV2::BURN,
                principal: "authority".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                delta_atoms: -1,
            },
            EconomicEffectRowV2 {
                kind: EconomicEffectKindV2::ISSUE,
                principal: "authority".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                delta_atoms: 1,
            },
        ],
        asset_conservation: vec![AssetConservationRowV2 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: u128::MAX,
            owned_and_custodied_post_atoms: u128::MAX,
            supply_pre_atoms: u128::MAX,
            supply_post_atoms: u128::MAX,
            authorized_issue_atoms: 1,
            authorized_burn_atoms: 1,
        }],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };

    assert_eq!(plan.validate(), Ok(()));
}
