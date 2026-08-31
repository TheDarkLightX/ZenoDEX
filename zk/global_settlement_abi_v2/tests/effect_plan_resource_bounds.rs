use zenodex_global_settlement_abi_v2::{
    AbiErrorV2, AssetConservationRowV2, EconomicEffectKindV2, EconomicEffectRowV2,
    ExternalOutboxEnqueueV2, FeeConservationRowV2, GlobalEconomicEffectPlanV2, LaneIdV2,
    LaneWriteV2, RootV2, MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
    MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2, MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2,
    MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2, MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2,
    MAX_LANE_WRITES_PER_PLAN_V2, MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
};

fn root(value: u64) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "test root", false).expect("root")
}

fn account_row() -> EconomicEffectRowV2 {
    EconomicEffectRowV2 {
        kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
        principal: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "accounts".to_owned(),
        delta_atoms: 1,
    }
}

fn conservation_row() -> AssetConservationRowV2 {
    AssetConservationRowV2 {
        asset: "USD".to_owned(),
        owned_and_custodied_pre_atoms: 1,
        owned_and_custodied_post_atoms: 1,
        supply_pre_atoms: 1,
        supply_post_atoms: 1,
        authorized_issue_atoms: 0,
        authorized_burn_atoms: 0,
    }
}

fn fee_row() -> FeeConservationRowV2 {
    FeeConservationRowV2 {
        asset: "USD".to_owned(),
        fee_charged_atoms: 0,
        current_allocations_atoms: 0,
        carried_residue_atoms: 0,
    }
}

fn lane_write() -> LaneWriteV2 {
    LaneWriteV2 {
        lane_id: LaneIdV2::ASSET_TRANSFER,
        pre_root: root(1),
        post_root: root(2),
    }
}

fn outbox_row() -> ExternalOutboxEnqueueV2 {
    ExternalOutboxEnqueueV2 {
        effect_id: root(3),
        destination_id: "external:adapter".to_owned(),
        payload_hash: root(4),
        adapter_profile_root: root(5),
    }
}

#[test]
fn every_effect_plan_collection_has_an_independent_fail_closed_ceiling() {
    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.rows = vec![account_row(); MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2 + 1];
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds("effect plan rows"))
    );

    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.asset_conservation = vec![conservation_row(); MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2 + 1];
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds("effect plan asset conservation"))
    );

    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.fee_conservation = vec![fee_row(); MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2 + 1];
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds("effect plan fee conservation"))
    );

    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.lane_writes = vec![lane_write(); MAX_LANE_WRITES_PER_PLAN_V2 + 1];
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds("effect plan lane writes"))
    );

    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.occurrence_consumptions = vec![root(6); MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2 + 1];
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "effect plan occurrence consumptions"
        ))
    );

    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.external_outbox_enqueue = vec![outbox_row(); MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2 + 1];
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "effect plan external outbox enqueue"
        ))
    );
}

#[test]
fn aggregate_item_ceiling_runs_before_deep_validation() {
    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.rows = vec![account_row(); MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2];
    plan.external_outbox_enqueue = vec![outbox_row(); MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2];
    plan.asset_conservation = vec![conservation_row()];
    assert_eq!(
        plan.rows.len() + plan.external_outbox_enqueue.len() + plan.asset_conservation.len(),
        MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2 + 1
    );
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds("effect plan total items"))
    );
}

#[test]
fn canonical_encoding_above_one_mebibyte_is_rejected() {
    let mut plan = GlobalEconomicEffectPlanV2::empty();
    plan.rows = (0..2_000)
        .map(|index| EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: "p".repeat(160),
            asset: format!("A{index:04}{}", "x".repeat(155)),
            custody_domain: "c".repeat(160),
            delta_atoms: 1,
        })
        .collect();
    assert_eq!(
        plan.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "effect plan canonical encoding bytes"
        ))
    );
}
