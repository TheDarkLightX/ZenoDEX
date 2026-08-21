//! RIPR evidence for exact global-state/effect refinement.
//!
//! Structural pre/post deltas are the independent semantic oracle. The shared
//! Python/Rust root detects canonical encoding drift.

use zenodex_global_settlement_abi_v1::{
    refine_global_economic_state_effects_v1, AbiErrorV1, AssetConservationRowV1, AssetSupplyV1,
    EconomicAmountV1, EconomicEffectKindV1, EconomicEffectRowV1, ExternalOutboxEnqueueV1,
    FeeConservationRowV1, GlobalEconomicEffectPlanV1,
    GlobalEconomicStateEffectRefinementCandidateV1, GlobalEconomicStateV1, LaneIdV1,
    LaneStateRootV1, LaneWriteV1, RootV1, ALL_LANE_IDS_V1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "refinement test root", false).unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(ZERO_ROOT_V1, "refinement test zero root", true).unwrap()
}

fn amount(owner: &str, asset: &str, domain: &str, atoms: u128) -> EconomicAmountV1 {
    EconomicAmountV1 {
        owner: owner.to_owned(),
        asset: asset.to_owned(),
        custody_domain: domain.to_owned(),
        amount_atoms: atoms,
    }
}

fn lane_roots(asset_root: u64) -> Vec<LaneStateRootV1> {
    ALL_LANE_IDS_V1
        .iter()
        .enumerate()
        .map(|(offset, lane_id)| {
            let index = offset as u64 + 1;
            LaneStateRootV1 {
                lane_id: *lane_id,
                module_release_id: root(100 + index),
                enabled: true,
                state_root: root(if *lane_id == LaneIdV1::ASSET_TRANSFER {
                    asset_root
                } else {
                    2_000 + index
                }),
            }
        })
        .collect()
}

fn pre_state() -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-refinement-test".to_owned(),
        deployment_root: root(1_000),
        writer_epoch: 17,
        height: 41,
        profile_root: root(1_001),
        lane_roots: lane_roots(2_001),
        balances: vec![amount("alice", "USD", "accounts", 100)],
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 175,
        }],
        custody: vec![
            amount("burn-bucket", "USD", "protocol-burn", 20),
            amount("pool", "USD", "amm-pool", 50),
        ],
        liabilities: vec![amount("vault", "USD", "vault-debt", 10)],
        reserves: vec![amount("treasury", "USD", "reserve", 5)],
        oracle_occurrences: vec![],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero_root(),
        outbox: vec![],
    }
}

fn post_state() -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-refinement-test".to_owned(),
        deployment_root: root(1_000),
        writer_epoch: 17,
        height: 41,
        profile_root: root(1_001),
        lane_roots: lane_roots(9_001),
        balances: vec![
            amount("alice", "USD", "accounts", 95),
            amount("bob", "USD", "accounts", 10),
            amount("treasury", "USD", "accounts", 2),
        ],
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 178,
        }],
        custody: vec![
            amount("burn-bucket", "USD", "protocol-burn", 16),
            amount("escrow", "USD", "strategy-escrow", 5),
            amount("pool", "USD", "amm-pool", 44),
        ],
        liabilities: vec![amount("vault", "USD", "vault-debt", 13)],
        reserves: vec![amount("treasury", "USD", "reserve", 6)],
        oracle_occurrences: vec![],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero_root(),
        outbox: vec![],
    }
}

fn effect(
    kind: EconomicEffectKindV1,
    principal: &str,
    domain: &str,
    delta_atoms: i128,
) -> EconomicEffectRowV1 {
    EconomicEffectRowV1 {
        kind,
        principal: principal.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: domain.to_owned(),
        delta_atoms,
    }
}

fn effect_plan() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            effect(
                EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                "alice",
                "accounts",
                -5,
            ),
            effect(
                EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                "bob",
                "accounts",
                10,
            ),
            effect(
                EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                "treasury",
                "accounts",
                2,
            ),
            effect(EconomicEffectKindV1::BURN, "supply", "supply", -4),
            effect(
                EconomicEffectKindV1::CUSTODY,
                "burn-bucket",
                "protocol-burn",
                -4,
            ),
            effect(
                EconomicEffectKindV1::CUSTODY,
                "escrow",
                "strategy-escrow",
                5,
            ),
            effect(EconomicEffectKindV1::CUSTODY, "pool", "amm-pool", -6),
            effect(
                EconomicEffectKindV1::FEE_ALLOCATION,
                "treasury",
                "accounts",
                2,
            ),
            effect(EconomicEffectKindV1::ISSUE, "supply", "supply", 7),
            effect(EconomicEffectKindV1::LIABILITY, "vault", "vault-debt", 3),
            effect(EconomicEffectKindV1::RESERVE, "treasury", "reserve", 1),
        ],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: 175,
            owned_and_custodied_post_atoms: 178,
            supply_pre_atoms: 175,
            supply_post_atoms: 178,
            authorized_issue_atoms: 7,
            authorized_burn_atoms: 4,
        }],
        fee_conservation: vec![FeeConservationRowV1 {
            asset: "USD".to_owned(),
            fee_charged_atoms: 2,
            current_allocations_atoms: 2,
            carried_residue_atoms: 0,
        }],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: root(2_001),
            post_root: root(9_001),
        }],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn candidate<'a>(
    pre: &'a GlobalEconomicStateV1,
    post: &'a GlobalEconomicStateV1,
    effects: &'a GlobalEconomicEffectPlanV1,
) -> GlobalEconomicStateEffectRefinementCandidateV1<'a> {
    GlobalEconomicStateEffectRefinementCandidateV1 {
        pre_state: pre,
        post_state: post,
        effect_plan: effects,
    }
}

#[test]
fn refinement_matches_python_golden_root() {
    let pre = pre_state();
    let post = post_state();
    let effects = effect_plan();

    let refinement = refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects))
        .expect("fixture must refine");

    assert_eq!(refinement.pre_state_root(), &pre.state_root().unwrap());
    assert_eq!(refinement.post_state_root(), &post.state_root().unwrap());
    assert_eq!(
        refinement.effect_plan_root(),
        &effects.effect_plan_root().unwrap()
    );
    assert_eq!(
        refinement.refinement_root().unwrap().as_str(),
        "0xa390b8bc7bf078478dab2d03a62e8d0824199b4a8c6dcfb03ef97e5578e7fd31"
    );
}

#[test]
fn refinement_rejects_each_hidden_amount_table_change() {
    let pre = pre_state();
    let effects = effect_plan();
    for field in 0..4 {
        let mut post = post_state();
        match field {
            0 => post.balances[0].amount_atoms += 1,
            1 => post.custody[2].amount_atoms += 1,
            2 => post.liabilities[0].amount_atoms -= 1,
            _ => post.reserves[0].amount_atoms += 1,
        }
        assert!(
            refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects)).is_err()
        );
    }
}

#[test]
fn refinement_rejects_supply_lane_and_conservation_substitution() {
    let pre = pre_state();
    let mut post = post_state();
    let effects = effect_plan();
    post.supplies[0].amount_atoms += 1;
    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects)).is_err());

    let post = post_state();
    let mut wrong_lane = effect_plan();
    wrong_lane.lane_writes[0].post_root = root(9_002);
    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &post, &wrong_lane)).is_err());

    let mut wrong_conservation = effect_plan();
    let row = &mut wrong_conservation.asset_conservation[0];
    row.owned_and_custodied_pre_atoms = 176;
    row.owned_and_custodied_post_atoms = 179;
    row.supply_pre_atoms = 176;
    row.supply_post_atoms = 179;
    assert!(
        refine_global_economic_state_effects_v1(&candidate(&pre, &post, &wrong_conservation,))
            .is_err()
    );
}

#[test]
fn refinement_rejects_unmirrored_fee_residue_and_unmapped_effects() {
    let pre = pre_state();
    let post = post_state();

    let mut unmirrored = effect_plan();
    unmirrored.rows[7].principal = "unfunded-fee".to_owned();
    assert!(
        refine_global_economic_state_effects_v1(&candidate(&pre, &post, &unmirrored,)).is_err()
    );

    let mut residue = effect_plan();
    residue.fee_conservation[0].fee_charged_atoms = 3;
    residue.fee_conservation[0].carried_residue_atoms = 1;
    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &post, &residue)).is_err());

    for kind in [EconomicEffectKindV1::REWARD, EconomicEffectKindV1::SLASH] {
        let mut effects = effect_plan();
        effects.rows.push(effect(kind, "actor", "accounts", 1));
        effects.rows.sort_by_key(|row| {
            let kind = match row.kind {
                EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
                EconomicEffectKindV1::ISSUE => "ISSUE",
                EconomicEffectKindV1::BURN => "BURN",
                EconomicEffectKindV1::CUSTODY => "CUSTODY",
                EconomicEffectKindV1::LIABILITY => "LIABILITY",
                EconomicEffectKindV1::RESERVE => "RESERVE",
                EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
                EconomicEffectKindV1::REWARD => "REWARD",
                EconomicEffectKindV1::SLASH => "SLASH",
            };
            (
                kind,
                row.asset.clone(),
                row.principal.clone(),
                row.custody_domain.clone(),
            )
        });
        assert!(
            refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects)).is_err()
        );
    }
}

#[test]
fn refinement_rejects_occurrence_consumption_and_zero_fee_alias() {
    let state = pre_state();
    let mut occurrence = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![root(5_000)],
        external_outbox_enqueue: vec![],
    };
    assert!(matches!(
        refine_global_economic_state_effects_v1(&candidate(&state, &state, &occurrence)),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement replay occurrence unavailable"
        ))
    ));

    occurrence.occurrence_consumptions.clear();
    occurrence.fee_conservation = vec![FeeConservationRowV1 {
        asset: "USD".to_owned(),
        fee_charged_atoms: 0,
        current_allocations_atoms: 0,
        carried_residue_atoms: 0,
    }];
    assert!(matches!(
        refine_global_economic_state_effects_v1(&candidate(&state, &state, &occurrence)),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement zero fee conservation row"
        ))
    ));
}

#[test]
fn refinement_rejects_unsupported_context_lane_metadata_outbox_and_zero_rows() {
    let pre = pre_state();
    let effects = effect_plan();

    let mut context = post_state();
    context.height += 1;
    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &context, &effects)).is_err());

    let mut metadata = post_state();
    metadata.lane_roots[0].enabled = false;
    assert!(
        refine_global_economic_state_effects_v1(&candidate(&pre, &metadata, &effects)).is_err()
    );

    let post = post_state();
    let mut outbox = effect_plan();
    outbox.external_outbox_enqueue = vec![ExternalOutboxEnqueueV1 {
        effect_id: root(8_001),
        destination_id: "bridge:test".to_owned(),
        payload_hash: root(8_002),
        adapter_profile_root: root(8_003),
    }];
    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &post, &outbox)).is_err());

    let mut zero = post_state();
    zero.balances.push(amount("ghost", "USD", "accounts", 0));
    zero.balances.sort_by_key(|row| {
        (
            row.asset.clone(),
            row.owner.clone(),
            row.custody_domain.clone(),
        )
    });
    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &zero, &effects)).is_err());
}

#[test]
fn refinement_rejects_state_where_owned_total_diverges_from_supply() {
    let mut pre = pre_state();
    let mut post = post_state();
    let mut effects = effect_plan();
    pre.supplies[0].amount_atoms = 180;
    post.supplies[0].amount_atoms = 183;
    effects.asset_conservation[0].supply_pre_atoms = 180;
    effects.asset_conservation[0].supply_post_atoms = 183;

    assert!(refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects)).is_err());
}

#[test]
fn refinement_rejects_unchanged_preexisting_owned_supply_drift() {
    let mut state = pre_state();
    state.balances[0].amount_atoms += 1;
    let empty = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };

    assert!(matches!(
        refine_global_economic_state_effects_v1(&candidate(&state, &state, &empty)),
        Err(AbiErrorV1::Conservation(
            "economic refinement owned total does not equal supply"
        ))
    ));
}

#[test]
fn refinement_allows_exact_burn_to_zero_supply() {
    let mut pre = pre_state();
    pre.balances = vec![amount("alice", "USD", "accounts", 1)];
    pre.supplies[0].amount_atoms = 1;
    pre.custody.clear();
    pre.liabilities.clear();
    pre.reserves.clear();
    let mut post = post_state();
    post.balances.clear();
    post.supplies[0].amount_atoms = 0;
    post.custody.clear();
    post.liabilities.clear();
    post.reserves.clear();
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            effect(
                EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                "alice",
                "accounts",
                -1,
            ),
            effect(EconomicEffectKindV1::BURN, "supply", "supply", -1),
        ],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: 1,
            owned_and_custodied_post_atoms: 0,
            supply_pre_atoms: 1,
            supply_post_atoms: 0,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 1,
        }],
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: root(2_001),
            post_root: root(9_001),
        }],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };

    let refinement = refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects))
        .expect("an exact final-atom burn must remain representable");

    assert_eq!(refinement.post_state_root(), &post.state_root().unwrap());
}

#[test]
fn refinement_aggregates_issue_and_burn_without_signed_order_overflow() {
    let pre = pre_state();
    let mut post = pre_state();
    post.lane_roots = lane_roots(9_001);
    let boundary = 1_u128 << 127;
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            effect(EconomicEffectKindV1::BURN, "burn-all", "supply", i128::MIN),
            effect(EconomicEffectKindV1::ISSUE, "issue-a", "supply", i128::MAX),
            effect(EconomicEffectKindV1::ISSUE, "issue-b", "supply", 1),
        ],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: 175,
            owned_and_custodied_post_atoms: 175,
            supply_pre_atoms: 175,
            supply_post_atoms: 175,
            authorized_issue_atoms: boundary,
            authorized_burn_atoms: boundary,
        }],
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: root(2_001),
            post_root: root(9_001),
        }],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };

    let refinement = refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects))
        .expect("separate u128 issue and burn totals avoid order-dependent overflow");

    assert_eq!(
        refinement.effect_plan_root(),
        &effects.effect_plan_root().unwrap()
    );
}

#[test]
fn refinement_signed_delta_bva_and_owned_total_overflow() {
    let mut pre = pre_state();
    pre.balances.clear();
    pre.supplies[0].amount_atoms = 0;
    pre.custody.clear();
    pre.liabilities.clear();
    pre.reserves.clear();
    let mut post = post_state();
    post.balances = vec![amount("alice", "USD", "accounts", i128::MAX as u128)];
    post.supplies[0].amount_atoms = i128::MAX as u128;
    post.custody.clear();
    post.liabilities.clear();
    post.reserves.clear();
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            effect(
                EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                "alice",
                "accounts",
                i128::MAX,
            ),
            effect(EconomicEffectKindV1::ISSUE, "supply", "supply", i128::MAX),
        ],
        asset_conservation: vec![AssetConservationRowV1 {
            asset: "USD".to_owned(),
            owned_and_custodied_pre_atoms: 0,
            owned_and_custodied_post_atoms: i128::MAX as u128,
            supply_pre_atoms: 0,
            supply_post_atoms: i128::MAX as u128,
            authorized_issue_atoms: i128::MAX as u128,
            authorized_burn_atoms: 0,
        }],
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ASSET_TRANSFER,
            pre_root: root(2_001),
            post_root: root(9_001),
        }],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };
    refine_global_economic_state_effects_v1(&candidate(&pre, &post, &effects))
        .expect("maximum signed state delta must remain representable");

    post.balances[0].amount_atoms = 1_u128 << 127;
    post.supplies[0].amount_atoms = 1_u128 << 127;
    let lane_only = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: effects.lane_writes.clone(),
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };
    assert!(matches!(
        refine_global_economic_state_effects_v1(&candidate(&pre, &post, &lane_only)),
        Err(AbiErrorV1::InvalidBounds(
            "economic refinement signed state delta"
        ))
    ));

    let mut overflow = pre_state();
    overflow.balances[0].amount_atoms = u128::MAX;
    overflow.supplies[0].amount_atoms = u128::MAX;
    overflow.custody = vec![amount("pool", "USD", "amm-pool", 1)];
    overflow.liabilities.clear();
    overflow.reserves.clear();
    let empty = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };
    assert!(matches!(
        refine_global_economic_state_effects_v1(&candidate(&overflow, &overflow, &empty)),
        Err(AbiErrorV1::Conservation(
            "economic refinement owned total overflow"
        ))
    ));
}
