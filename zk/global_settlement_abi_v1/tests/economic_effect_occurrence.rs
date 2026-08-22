use zenodex_global_settlement_abi_v1::{
    derive_route_effect_occurrences_v1, AssetConservationRowV1, EconomicEffectKindV1,
    EconomicEffectOccurrenceV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1, RootV1,
    GLOBAL_SETTLEMENT_ABI_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "effect occurrence test root",
        false,
    )
    .unwrap()
}

fn row(principal: &str, delta_atoms: i128) -> EconomicEffectRowV1 {
    EconomicEffectRowV1 {
        kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
        principal: principal.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "accounts".to_owned(),
        delta_atoms,
    }
}

fn plan(occurrence_id: RootV1) -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![row("alice", -7), row("bob", 7)],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: 20,
            owned_and_custodied_post_atoms: 20,
            supply_pre_atoms: 20,
            supply_post_atoms: 20,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
        }],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![occurrence_id],
        external_outbox_enqueue: vec![],
    }
}

#[test]
fn identity_binds_route_occurrence_index_and_row() {
    let base = EconomicEffectOccurrenceV1::build(root(1), root(2), 0, row("alice", -7))
        .expect("base effect occurrence must build");
    let variants = [
        EconomicEffectOccurrenceV1::build(root(3), root(2), 0, row("alice", -7)).unwrap(),
        EconomicEffectOccurrenceV1::build(root(1), root(4), 0, row("alice", -7)).unwrap(),
        EconomicEffectOccurrenceV1::build(root(1), root(2), 1, row("alice", -7)).unwrap(),
        EconomicEffectOccurrenceV1::build(root(1), root(2), 0, row("alice", -8)).unwrap(),
    ];
    let mut ids = variants
        .iter()
        .map(|item| item.effect_occurrence_id.clone())
        .collect::<std::collections::BTreeSet<_>>();
    ids.insert(base.effect_occurrence_id.clone());

    assert_eq!(ids.len(), 5);
    assert_eq!(
        base.effect_occurrence_id,
        base.derived_effect_occurrence_id().unwrap()
    );
    assert_eq!(
        base.effect_occurrence_id.as_str(),
        "0xe21c9a9fef43e18576caa49441b3b8652005834d06b0fd515184b2365c1de36c"
    );
}

#[test]
fn rejects_a_forged_effect_occurrence_id() {
    let mut forged =
        EconomicEffectOccurrenceV1::build(root(1), root(2), 0, row("alice", -7)).unwrap();
    forged.effect_occurrence_id = root(99);

    assert!(forged.validate().is_err());
}

#[test]
fn route_derivation_is_ordered_and_disjoint_across_commands() {
    let first = derive_route_effect_occurrences_v1(&root(1), &root(2), &plan(root(1))).unwrap();
    let second = derive_route_effect_occurrences_v1(&root(3), &root(2), &plan(root(3))).unwrap();
    let ids = first
        .iter()
        .chain(&second)
        .map(|item| item.effect_occurrence_id.clone())
        .collect::<std::collections::BTreeSet<_>>();

    assert_eq!(
        first
            .iter()
            .map(|item| item.effect_index)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert_eq!(ids.len(), 4);
    assert_eq!(first[0].effect_row, second[0].effect_row);
}

#[test]
fn route_derivation_requires_the_exact_consumed_occurrence() {
    assert!(derive_route_effect_occurrences_v1(&root(1), &root(2), &plan(root(99))).is_err());
}
