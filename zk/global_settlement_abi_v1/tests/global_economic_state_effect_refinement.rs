//! RIPR evidence for exact global-state/effect refinement.
//!
//! Structural pre/post deltas are the independent semantic oracle. The shared
//! Python/Rust root detects canonical encoding drift.

use zenodex_global_settlement_abi_v1::{
    refine_global_economic_state_effects_v1, AbiErrorV1, AssetConservationRowV1, AssetSupplyV1,
    EconomicAmountV1, EconomicCommandOccurrenceV1, EconomicEffectKindV1, EconomicEffectRowV1,
    ExternalOutboxEnqueueV1, FeeConservationRowV1, GlobalEconomicEffectPlanV1,
    GlobalEconomicStateEffectRefinementCandidateV1, GlobalEconomicStateV1, LaneIdV1,
    LaneStateRootV1, LaneWriteV1, ReplayStateV1, RootV1, RouteCompositionJournalV1,
    ALL_LANE_IDS_V1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
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
        consumed_occurrences: &[],
        route_journals: &[],
    }
}

fn occurrence(
    chain_id: &str,
    command_kind: &str,
    nonce: u64,
    tx_index: u64,
    pre_state_root: RootV1,
) -> EconomicCommandOccurrenceV1 {
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: chain_id.to_owned(),
        deployment_root: root(1_000),
        height: 42,
        tx_index,
        op_index: 1,
        command_kind: command_kind.to_owned(),
        command_body_hash: root(5_000 + tx_index),
        route_release_id: root(4_001),
        subject_id: "alice".to_owned(),
        grant_root: root(4_002),
        nonce,
        profile_root: root(1_001),
        pre_state_root,
        consumed_object_ids: vec![],
    }
}

fn route_journal(
    occurrence: &EconomicCommandOccurrenceV1,
    post_state_root: RootV1,
) -> RouteCompositionJournalV1 {
    RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: 17,
        route_release_id: occurrence.route_release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id().unwrap(),
        ordered_lane_journal_roots: vec![root(20_000 + occurrence.tx_index)],
        pre_state_root: occurrence.pre_state_root.clone(),
        post_state_root,
        effect_plan_root: root(30_000 + occurrence.tx_index),
        terminal_obligations_root: zero_root(),
    }
}

fn replay_batch_for_nonces(
    nonces: &[u64],
) -> (
    GlobalEconomicStateV1,
    GlobalEconomicStateV1,
    GlobalEconomicEffectPlanV1,
    Vec<EconomicCommandOccurrenceV1>,
    Vec<RouteCompositionJournalV1>,
) {
    let pre = pre_state();
    let mut current = pre.clone();
    let mut occurrences = Vec::with_capacity(nonces.len());
    let mut journals = Vec::with_capacity(nonces.len());
    for (index, nonce) in nonces.iter().copied().enumerate() {
        let item = occurrence(
            "zeno-refinement-test",
            "TRANSFER",
            nonce,
            index as u64,
            current.state_root().unwrap(),
        );
        let replay = ReplayStateV1 {
            replay_id: item.replay_id().unwrap().to_string(),
            occurrence_id: item.occurrence_id().unwrap(),
        };
        let mut next = current.clone();
        next.height = 42;
        next.replay_state.push(replay);
        next.replay_state
            .sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
        journals.push(route_journal(&item, next.state_root().unwrap()));
        occurrences.push(item);
        current = next;
    }
    let mut consumptions = occurrences
        .iter()
        .map(|item| item.occurrence_id().unwrap())
        .collect::<Vec<_>>();
    consumptions.sort();
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: consumptions,
        external_outbox_enqueue: vec![],
    };
    (pre, current, effects, occurrences, journals)
}

fn replay_batch(
    count: usize,
) -> (
    GlobalEconomicStateV1,
    GlobalEconomicStateV1,
    GlobalEconomicEffectPlanV1,
    Vec<EconomicCommandOccurrenceV1>,
    Vec<RouteCompositionJournalV1>,
) {
    replay_batch_for_nonces(&(0..count as u64).collect::<Vec<_>>())
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
        "0x5026263a651e46d40e4ee6d818c3e222a7d36f484ac48a180500047f51725fdc"
    );
}

#[test]
fn refinement_height_progression_kills_static_epoch_and_overflow_mutants() {
    let pre = pre_state();
    let mut wrong_static_post = post_state();
    wrong_static_post.height += 1;
    assert!(matches!(
        refine_global_economic_state_effects_v1(&candidate(
            &pre,
            &wrong_static_post,
            &effect_plan(),
        )),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement state height progression"
        ))
    ));

    let (epoch_pre, mut wrong_epoch_post, epoch_effects, occurrences, journals) = replay_batch(1);
    wrong_epoch_post.height = epoch_pre.height;
    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &epoch_pre,
            post_state: &wrong_epoch_post,
            effect_plan: &epoch_effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        }),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement state height progression"
        ))
    ));

    let mut overflow_pre = epoch_pre;
    let mut overflow_post = wrong_epoch_post;
    overflow_pre.height = u64::MAX;
    overflow_post.height = u64::MAX;
    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &overflow_pre,
            post_state: &overflow_post,
            effect_plan: &epoch_effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        }),
        Err(AbiErrorV1::InvalidBounds(
            "economic refinement state height"
        ))
    ));
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
            "economic refinement occurrence disclosure mismatch"
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
fn replay_refinement_derives_subject_nonce_identity_and_exact_post_row() {
    let (pre, post, effects, occurrences, journals) = replay_batch(1);
    let replay_id = occurrences[0].replay_id().unwrap();

    let refinement =
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &post,
            effect_plan: &effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        })
        .expect("exact replay insertion must refine");

    assert_eq!(
        replay_id.as_str(),
        "0x1ea84f66c7d749c6608390a7e07c501c1366809cde0780a57d67b0ce8354dde2"
    );
    assert_eq!(refinement.post_state_root(), &post.state_root().unwrap());
}

#[test]
fn replay_refinement_rejects_missing_post_cross_context_and_prior_consumption() {
    let (pre, mut post, effects, occurrences, mut journals) = replay_batch(1);
    post.replay_state.clear();
    journals[0].post_state_root = post.state_root().unwrap();

    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &post,
            effect_plan: &effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        }),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement replay state delta mismatch"
        ))
    ));

    let foreign = occurrence(
        "foreign-chain",
        "TRANSFER",
        11,
        3,
        pre.state_root().unwrap(),
    );
    let foreign_id = foreign.occurrence_id().unwrap();
    let foreign_replay_id = foreign.replay_id().unwrap();
    let foreign_occurrences = [foreign];
    let mut foreign_effects = effects.clone();
    foreign_effects.occurrence_consumptions = vec![foreign_id.clone()];
    let mut foreign_post = post.clone();
    foreign_post.replay_state = vec![ReplayStateV1 {
        replay_id: foreign_replay_id.to_string(),
        occurrence_id: foreign_id,
    }];
    let foreign_journals = [route_journal(
        &foreign_occurrences[0],
        foreign_post.state_root().unwrap(),
    )];
    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &foreign_post,
            effect_plan: &foreign_effects,
            consumed_occurrences: &foreign_occurrences,
            route_journals: &foreign_journals,
        }),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement occurrence state context mismatch"
        ))
    ));

    let original = &occurrences[0];
    let replay_row = ReplayStateV1 {
        replay_id: original.replay_id().unwrap().to_string(),
        occurrence_id: original.occurrence_id().unwrap(),
    };
    let mut replayed_pre = pre.clone();
    replayed_pre.replay_state = vec![replay_row.clone()];
    let repeated = occurrence(
        "zeno-refinement-test",
        "TRANSFER",
        0,
        3,
        replayed_pre.state_root().unwrap(),
    );
    let replayed_occurrences = [repeated];
    let mut replayed_effects = effects;
    replayed_effects.occurrence_consumptions =
        vec![replayed_occurrences[0].occurrence_id().unwrap()];
    let mut replayed_post = replayed_pre.clone();
    replayed_post.height = 42;
    replayed_post.replay_state = vec![replay_row];
    let replayed_journals = [route_journal(
        &replayed_occurrences[0],
        replayed_post.state_root().unwrap(),
    )];
    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &replayed_pre,
            post_state: &replayed_post,
            effect_plan: &replayed_effects,
            consumed_occurrences: &replayed_occurrences,
            route_journals: &replayed_journals,
        }),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement replay identity already consumed"
        ))
    ));
}

#[test]
fn replay_refinement_rejects_duplicate_subject_nonce_under_distinct_occurrences() {
    let pre = pre_state();
    let mut post = post_state();
    let mut effects = effect_plan();
    let first = occurrence(
        "zeno-refinement-test",
        "TRANSFER",
        11,
        3,
        pre.state_root().unwrap(),
    );
    let first_row = ReplayStateV1 {
        replay_id: first.replay_id().unwrap().to_string(),
        occurrence_id: first.occurrence_id().unwrap(),
    };
    let mut intermediate = pre.clone();
    intermediate.height = 42;
    intermediate.replay_state = vec![first_row.clone()];
    let second = occurrence(
        "zeno-refinement-test",
        "MANAGED_BURN",
        11,
        4,
        intermediate.state_root().unwrap(),
    );
    let occurrences = vec![first, second];
    effects.occurrence_consumptions = occurrences
        .iter()
        .map(|item| item.occurrence_id().unwrap())
        .collect();
    post.height = 42;
    post.replay_state = vec![first_row];
    let journals = vec![
        route_journal(&occurrences[0], intermediate.state_root().unwrap()),
        route_journal(&occurrences[1], post.state_root().unwrap()),
    ];

    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &post,
            effect_plan: &effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        }),
        Err(AbiErrorV1::InvalidBinding(
            "economic refinement duplicate replay identity"
        ))
    ));
}

#[test]
fn replay_refinement_enforces_zero_one_sixty_four_and_sixty_five_bounds() {
    for count in [0, 1, 64] {
        let (pre, post, effects, occurrences, journals) = replay_batch(count);
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &post,
            effect_plan: &effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        })
        .expect("bounded replay disclosure must refine");
    }

    let (pre, post, effects, occurrences, journals) = replay_batch(65);
    assert!(matches!(
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &post,
            effect_plan: &effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        }),
        Err(AbiErrorV1::InvalidBounds(
            "economic refinement occurrence count"
        ))
    ));
}

#[test]
fn replay_refinement_matches_two_occurrence_python_golden_and_u64_nonce_max() {
    let (pre, post, effects, occurrences, journals) = replay_batch(2);
    let refinement =
        refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &pre,
            post_state: &post,
            effect_plan: &effects,
            consumed_occurrences: &occurrences,
            route_journals: &journals,
        })
        .unwrap();
    assert_eq!(
        refinement.refinement_root().unwrap().as_str(),
        "0x04a52daea5b87169f428fc698537e115fa14330a1eea885db0e8db7a7b503517"
    );

    let (pre, post, effects, occurrences, journals) = replay_batch_for_nonces(&[u64::MAX]);
    refine_global_economic_state_effects_v1(&GlobalEconomicStateEffectRefinementCandidateV1 {
        pre_state: &pre,
        post_state: &post,
        effect_plan: &effects,
        consumed_occurrences: &occurrences,
        route_journals: &journals,
    })
    .expect("maximum u64 nonce must refine");
}

#[test]
fn global_state_rejects_one_occurrence_under_two_replay_aliases() {
    let mut state = pre_state();
    state.replay_state = vec![
        ReplayStateV1 {
            replay_id: "alias-a".to_owned(),
            occurrence_id: root(90_001),
        },
        ReplayStateV1 {
            replay_id: "alias-b".to_owned(),
            occurrence_id: root(90_001),
        },
    ];

    assert!(matches!(
        state.validate(),
        Err(AbiErrorV1::InvalidOrder("global replay occurrence ids"))
    ));
}

#[test]
fn replay_refinement_rejects_height_and_pre_root_context_mutants() {
    for mutate_height in [true, false] {
        let (pre, mut post, mut effects, mut occurrences, mut journals) = replay_batch(1);
        if mutate_height {
            occurrences[0].height -= 1;
        } else {
            occurrences[0].pre_state_root = root(91_003);
            journals[0].pre_state_root = root(91_003);
        }
        let occurrence_id = occurrences[0].occurrence_id().unwrap();
        effects.occurrence_consumptions = vec![occurrence_id.clone()];
        post.replay_state[0].occurrence_id = occurrence_id.clone();
        journals[0].command_occurrence_id = occurrence_id;
        journals[0].post_state_root = post.state_root().unwrap();

        assert!(matches!(
            refine_global_economic_state_effects_v1(
                &GlobalEconomicStateEffectRefinementCandidateV1 {
                    pre_state: &pre,
                    post_state: &post,
                    effect_plan: &effects,
                    consumed_occurrences: &occurrences,
                    route_journals: &journals,
                }
            ),
            Err(AbiErrorV1::InvalidBinding(
                "economic refinement occurrence state context mismatch"
            ))
        ));
    }
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
