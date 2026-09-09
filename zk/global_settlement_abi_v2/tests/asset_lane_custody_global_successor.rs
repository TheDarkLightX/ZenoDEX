//! The derived custody successor must be the one global post-state that refines.

#[path = "support/asset_lane_coordinator.rs"]
mod support;

use zenodex_global_settlement_abi_v2::{
    derive_asset_lane_custody_global_post_v2, refine_asset_lane_custody_global_v2,
    transition_asset_lane_custody_v2, AbiErrorV2, AbiResultV2, AssetLaneCommandV2,
    AssetLaneContextV2, AssetLaneCustodyAcceptedV2, AssetLaneCustodyResultV2,
    AssetLaneCustodyStateV2, AssetLaneStateV2, AssetSupplyV2, AssetTransferCommandV2,
    EconomicAmountV2, EconomicCommandOccurrenceV2, GlobalEconomicStateV2, LaneIdV2,
    LaneStateRootV2, ManagedAssetLifecycleCommandV2, OracleOccurrenceStateV2, OutboxStateV2,
    OutboxStatusV2, ReplayStateV2, RootV2, TerminalObligationStatusV2, TerminalObligationV2,
    ACCOUNT_CUSTODY_DOMAIN_V2, ALL_LANE_IDS_V2, ASSET_LANE_CUSTODY_STATE_SCHEMA_V2,
    GLOBAL_SETTLEMENT_ABI_V2, MANAGED_ASSET_BURN_COMMAND_KIND_V2, MAX_GLOBAL_REPLAY_ROWS_V2,
};

const CUSTODY_DOMAIN_V2: &str = "vault:primary";
const RETAINED_LANE_V2: LaneIdV2 = LaneIdV2::SPOT_LIQUIDITY;

fn root(value: u64) -> RootV2 {
    RootV2::parse(
        format!("0x{value:064x}"),
        "custody successor test root",
        false,
    )
    .expect("test root is canonical")
}

fn retained_lane_root() -> RootV2 {
    root(555)
}

fn retained_history_root() -> RootV2 {
    root(777)
}

fn retained_oracle_row() -> OracleOccurrenceStateV2 {
    OracleOccurrenceStateV2 {
        oracle_id: "usd-mark".to_owned(),
        occurrence_root: root(888),
        observed_height: 0,
        finalized: true,
    }
}

fn retained_outbox_row() -> OutboxStateV2 {
    OutboxStateV2 {
        effect_id: root(901),
        destination_id: "bridge:alpha".to_owned(),
        payload_hash: root(902),
        adapter_profile_root: root(903),
        commit_id: root(904),
        status: OutboxStatusV2::PENDING,
    }
}

fn account_row(owner: &str, amount_atoms: u128) -> EconomicAmountV2 {
    EconomicAmountV2 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
        amount_atoms,
    }
}

fn custody_row(owner: &str, amount_atoms: u128) -> EconomicAmountV2 {
    EconomicAmountV2 {
        owner: owner.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: CUSTODY_DOMAIN_V2.to_owned(),
        amount_atoms,
    }
}

fn usd_supply(amount_atoms: u128) -> Vec<AssetSupplyV2> {
    if amount_atoms == 0 {
        return Vec::new();
    }
    vec![AssetSupplyV2 {
        asset: "USD".to_owned(),
        amount_atoms,
    }]
}

/// The retained claimant frame this restricted relation must never rewrite.
fn claims(lane: &AssetLaneCustodyStateV2) -> (Vec<EconomicAmountV2>, Vec<TerminalObligationV2>) {
    if lane.custody.is_empty() {
        return (Vec::new(), Vec::new());
    }
    (
        vec![EconomicAmountV2 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms: 20,
        }],
        vec![TerminalObligationV2 {
            obligation_id: "alice-vault-claim".to_owned(),
            lane_id: LaneIdV2::ASSET_TRANSFER,
            claimant: "alice".to_owned(),
            asset: "USD".to_owned(),
            liability_domain: CUSTODY_DOMAIN_V2.to_owned(),
            amount_atoms: 20,
            status: TerminalObligationStatusV2::OPEN,
        }],
    )
}

fn lane_roots(lane: &AssetLaneCustodyStateV2, other_enabled: bool) -> Vec<LaneStateRootV2> {
    ALL_LANE_IDS_V2
        .iter()
        .copied()
        .enumerate()
        .map(|(index, lane_id)| {
            if lane_id == LaneIdV2::ASSET_TRANSFER {
                return LaneStateRootV2 {
                    lane_id,
                    module_release_id: lane.module_release_id().clone(),
                    enabled: true,
                    state_root: lane.state_root().expect("lane state root"),
                };
            }
            let retained = other_enabled && lane_id == RETAINED_LANE_V2;
            LaneStateRootV2 {
                lane_id,
                module_release_id: root(100 + index as u64),
                enabled: retained,
                state_root: if retained {
                    retained_lane_root()
                } else {
                    RootV2::zero()
                },
            }
        })
        .collect()
}

fn positive_supplies(lane: &AssetLaneCustodyStateV2) -> Vec<AssetSupplyV2> {
    lane.supplies()
        .iter()
        .filter(|row| row.amount_atoms != 0)
        .cloned()
        .collect()
}

fn custody_lane(
    case_name: &str,
    account_atoms: u128,
    custody_atoms: u128,
    supply: u128,
) -> AssetLaneCustodyStateV2 {
    let fixture = support::fixture();
    let case = &fixture.accepted[case_name];
    let aggregate: AssetLaneStateV2 = support::typed_vector(&case.vectors, "pre_state");
    let mut transfer_state = aggregate.transfer_leaf_state();
    transfer_state.balances = (account_atoms != 0)
        .then(|| account_row("alice", account_atoms))
        .into_iter()
        .collect();
    transfer_state.supplies = vec![AssetSupplyV2 {
        asset: "USD".to_owned(),
        amount_atoms: supply,
    }];
    AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state,
        origin_registry: aggregate.origin_registry,
        managed_policies: aggregate.managed_policies,
        custody: (custody_atoms != 0)
            .then(|| custody_row("vault", custody_atoms))
            .into_iter()
            .collect(),
    }
}

struct SubjectV2 {
    context: AssetLaneContextV2,
    lane: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
}

fn transfer_subject() -> SubjectV2 {
    let fixture = support::fixture();
    let case = &fixture.accepted["transfer"];
    let mut context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let mut command: AssetTransferCommandV2 = support::typed_vector(&case.vectors, "command");
    command.amount_atoms = 10;
    context
        .occurrence
        .as_mut()
        .expect("transfer occurrence")
        .command_body_hash = command.command_body_hash().expect("transfer body hash");
    SubjectV2 {
        context,
        lane: custody_lane("transfer", 80, 20, 100),
        command: AssetLaneCommandV2::Transfer(command),
    }
}

fn managed_subject(burn: bool, amount_atoms: u128, lane: AssetLaneCustodyStateV2) -> SubjectV2 {
    let fixture = support::fixture();
    let case = &fixture.accepted["managed_issue"];
    let mut context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let mut command: ManagedAssetLifecycleCommandV2 =
        support::typed_vector(&case.vectors, "command");
    command.amount_atoms = amount_atoms;
    if burn {
        let burn_root = lane.managed_policies[0]
            .burn_authorization_root
            .clone()
            .expect("managed burn authorization root");
        command.command_kind = MANAGED_ASSET_BURN_COMMAND_KIND_V2.to_owned();
        command.authorization_root = Some(burn_root.clone());
        let occurrence = context.occurrence.as_mut().expect("managed occurrence");
        occurrence.command_kind = MANAGED_ASSET_BURN_COMMAND_KIND_V2.to_owned();
        occurrence.subject_id = command.account_owner.clone();
        occurrence.grant_root = burn_root;
    }
    context
        .occurrence
        .as_mut()
        .expect("managed occurrence")
        .command_body_hash = command.command_body_hash().expect("managed body hash");
    SubjectV2 {
        context,
        lane,
        command: AssetLaneCommandV2::ManagedLifecycle(command),
    }
}

#[derive(Default)]
struct FrameOptionsV2 {
    replay_state: Vec<ReplayStateV2>,
    other_enabled: bool,
    lifecycle_rows: bool,
    height: Option<u64>,
}

fn predecessor(
    lane: &AssetLaneCustodyStateV2,
    context: &AssetLaneContextV2,
    options: &FrameOptionsV2,
) -> GlobalEconomicStateV2 {
    let occurrence = context.occurrence.as_ref().expect("subject occurrence");
    let (liabilities, terminal_obligations) = claims(lane);
    GlobalEconomicStateV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        writer_epoch: context.writer_epoch,
        height: options.height.unwrap_or(occurrence.height - 1),
        profile_root: occurrence.profile_root.clone(),
        lane_roots: lane_roots(lane, options.other_enabled),
        balances: lane.balances().to_vec(),
        supplies: positive_supplies(lane),
        custody: lane.custody.clone(),
        liabilities,
        reserves: Vec::new(),
        oracle_occurrences: if options.lifecycle_rows {
            vec![retained_oracle_row()]
        } else {
            Vec::new()
        },
        replay_state: options.replay_state.clone(),
        terminal_obligations,
        history_root: if options.lifecycle_rows {
            retained_history_root()
        } else {
            RootV2::zero()
        },
        outbox: if options.lifecycle_rows {
            vec![retained_outbox_row()]
        } else {
            Vec::new()
        },
    }
}

struct CaseV2 {
    lane: AssetLaneCustodyStateV2,
    accepted: Box<AssetLaneCustodyAcceptedV2>,
    global_pre: GlobalEconomicStateV2,
    occurrence: EconomicCommandOccurrenceV2,
}

fn bound_case(
    lane: AssetLaneCustodyStateV2,
    context: &AssetLaneContextV2,
    command: &AssetLaneCommandV2,
    global_pre: GlobalEconomicStateV2,
    nonce: u64,
) -> CaseV2 {
    let mut bound = context.clone();
    let mut occurrence = bound.occurrence.clone().expect("subject occurrence");
    occurrence.nonce = nonce;
    occurrence.pre_state_root = global_pre.state_root().expect("global pre-state root");
    bound.global_pre_state_root = occurrence.pre_state_root.clone();
    bound.occurrence = Some(occurrence.clone());
    let AssetLaneCustodyResultV2::Accepted(accepted) =
        transition_asset_lane_custody_v2(&bound, &lane, command).expect("custody lane executes")
    else {
        panic!("custody frame fixture must accept")
    };
    CaseV2 {
        lane,
        accepted,
        global_pre,
        occurrence,
    }
}

fn transfer_case(options: &FrameOptionsV2) -> CaseV2 {
    let SubjectV2 {
        context,
        lane,
        command,
    } = transfer_subject();
    let global_pre = predecessor(&lane, &context, options);
    bound_case(lane, &context, &command, global_pre, 1)
}

fn derive(case: &CaseV2) -> AbiResultV2<GlobalEconomicStateV2> {
    derive_asset_lane_custody_global_post_v2(
        &case.lane,
        &case.accepted,
        &case.global_pre,
        &case.occurrence,
    )
}

fn refine(case: &CaseV2, global_post: &GlobalEconomicStateV2) {
    refine_asset_lane_custody_global_v2(
        &case.lane,
        &case.accepted,
        &case.global_pre,
        global_post,
        &case.occurrence,
    )
    .expect("derived successor must re-pass the original relation");
}

fn inserted_replay(occurrence: &EconomicCommandOccurrenceV2) -> ReplayStateV2 {
    ReplayStateV2 {
        replay_id: occurrence.replay_id().expect("replay id").to_string(),
        occurrence_id: occurrence.occurrence_id().expect("occurrence id"),
    }
}

fn advance(
    lane: &AssetLaneCustodyStateV2,
    global_pre: &GlobalEconomicStateV2,
    subject: &SubjectV2,
    nonce: u64,
) -> (AssetLaneCustodyStateV2, GlobalEconomicStateV2) {
    let mut context = subject.context.clone();
    context
        .occurrence
        .as_mut()
        .expect("subject occurrence")
        .height = global_pre.height + 1;
    let case = bound_case(
        lane.clone(),
        &context,
        &subject.command,
        global_pre.clone(),
        nonce,
    );
    let derived = derive(&case).expect("chained successor derives");
    refine(&case, &derived);
    (case.accepted.post_state().clone(), derived)
}

#[test]
fn transfer_successor_equals_the_independently_written_admitted_post_state() {
    let case = transfer_case(&FrameOptionsV2::default());
    let derived = derive(&case).expect("lawful custody frame derives its successor");

    let post_lane_root = case
        .accepted
        .post_state()
        .state_root()
        .expect("post lane root");
    let mut expected = case.global_pre.clone();
    expected.height = case.global_pre.height + 1;
    expected.balances = vec![
        account_row("alice", 68),
        account_row("bob", 10),
        account_row("treasury", 2),
    ];
    expected
        .lane_roots
        .iter_mut()
        .find(|row| row.lane_id == LaneIdV2::ASSET_TRANSFER)
        .expect("asset lane root")
        .state_root = post_lane_root;
    expected.replay_state = vec![inserted_replay(&case.occurrence)];

    assert_eq!(derived, expected);
    assert_eq!(derived.custody, vec![custody_row("vault", 20)]);
    assert_eq!(derived.supplies, usd_supply(100));
    let owned: u128 = derived
        .balances
        .iter()
        .chain(&derived.custody)
        .map(|row| row.amount_atoms)
        .sum();
    assert_eq!(owned, 100);
    refine(&case, &derived);
}

#[test]
fn derived_successor_repasses_the_original_relation_and_is_deterministic() {
    let case = transfer_case(&FrameOptionsV2 {
        lifecycle_rows: true,
        ..FrameOptionsV2::default()
    });

    let derived = derive(&case).expect("lifecycle-bearing frame derives its successor");
    let repeated = derive(&case).expect("successor derivation replays");
    assert_eq!(derived, repeated);

    let checked = refine_asset_lane_custody_global_v2(
        &case.lane,
        &case.accepted,
        &case.global_pre,
        &derived,
        &case.occurrence,
    )
    .expect("derived successor refines");
    assert_eq!(
        checked.pre_state_root(),
        &case.global_pre.state_root().unwrap()
    );
    assert_eq!(checked.post_state_root(), &derived.state_root().unwrap());
    assert_eq!(
        checked.effect_plan_root(),
        &case.accepted.effects().effect_plan_root().unwrap()
    );
    assert_eq!(checked.production_authority(), "NONE");
}

#[test]
fn managed_issue_full_burn_and_dormant_successors_project_only_positive_supply() {
    for (burn, accounts, custody, supply, amount, post_supply, post_accounts) in [
        (false, 80_u128, 20_u128, 100_u128, 7_u128, 107_u128, 87_u128),
        (true, 80, 20, 100, 80, 20, 0),
        (false, 0, 0, 0, 1, 1, 1),
        (true, 1, 0, 1, 1, 0, 0),
    ] {
        let lane = custody_lane("managed_issue", accounts, custody, supply);
        let SubjectV2 {
            context,
            lane,
            command,
        } = managed_subject(burn, amount, lane);
        let global_pre = predecessor(&lane, &context, &FrameOptionsV2::default());
        let case = bound_case(lane, &context, &command, global_pre, 1);

        let derived = derive(&case).expect("managed custody frame derives its successor");

        assert_eq!(
            case.accepted.post_state().supply_atoms("USD").unwrap(),
            post_supply
        );
        assert_eq!(derived.supplies, usd_supply(post_supply));
        assert_eq!(
            derived.balances.as_slice(),
            case.accepted.post_state().balances()
        );
        let accounts_total: u128 = derived.balances.iter().map(|row| row.amount_atoms).sum();
        assert_eq!(accounts_total, post_accounts);
        assert_eq!(derived.custody, case.global_pre.custody);
        assert_eq!(derived.liabilities, case.global_pre.liabilities);
        assert_eq!(derived.height, case.global_pre.height + 1);
        refine(&case, &derived);
    }
}

#[test]
fn unchanged_global_frame_rows_are_carried_into_the_successor() {
    let case = transfer_case(&FrameOptionsV2 {
        lifecycle_rows: true,
        ..FrameOptionsV2::default()
    });

    let derived = derive(&case).expect("lifecycle-bearing frame derives its successor");

    let pre = &case.global_pre;
    assert_eq!(derived.schema, pre.schema);
    assert_eq!(derived.chain_id, pre.chain_id);
    assert_eq!(derived.deployment_root, pre.deployment_root);
    assert_eq!(derived.writer_epoch, pre.writer_epoch);
    assert_eq!(derived.profile_root, pre.profile_root);
    assert_eq!(derived.custody, pre.custody);
    assert_eq!(derived.liabilities, pre.liabilities);
    assert_eq!(derived.reserves, pre.reserves);
    assert_eq!(derived.oracle_occurrences, pre.oracle_occurrences);
    assert_eq!(derived.terminal_obligations, pre.terminal_obligations);
    assert_eq!(derived.history_root, pre.history_root);
    assert_eq!(derived.outbox, pre.outbox);
    assert!(derived.reserves.is_empty());
    assert_eq!(derived.oracle_occurrences, vec![retained_oracle_row()]);
    assert_eq!(derived.outbox, vec![retained_outbox_row()]);
    assert_eq!(derived.history_root, retained_history_root());
    assert_eq!(derived.terminal_obligations.len(), 1);
    assert_eq!(derived.height, pre.height + 1);
    assert_ne!(derived.balances, pre.balances);
    assert_eq!(
        derived.replay_state,
        vec![inserted_replay(&case.occurrence)]
    );
}

#[test]
fn other_enabled_lane_keeps_its_root_release_and_enabled_metadata() {
    let case = transfer_case(&FrameOptionsV2 {
        other_enabled: true,
        ..FrameOptionsV2::default()
    });

    let derived = derive(&case).expect("multi-lane frame derives its successor");

    let post_lane_root = case
        .accepted
        .post_state()
        .state_root()
        .expect("post lane root");
    for (pre_row, post_row) in case.global_pre.lane_roots.iter().zip(&derived.lane_roots) {
        assert_eq!(pre_row.lane_id, post_row.lane_id);
        assert_eq!(pre_row.module_release_id, post_row.module_release_id);
        assert_eq!(pre_row.enabled, post_row.enabled);
        if pre_row.lane_id == LaneIdV2::ASSET_TRANSFER {
            assert_eq!(post_row.state_root, post_lane_root);
        } else {
            assert_eq!(post_row.state_root, pre_row.state_root);
        }
    }
    let retained = derived
        .lane_roots
        .iter()
        .find(|row| row.lane_id == RETAINED_LANE_V2)
        .expect("retained lane root");
    assert!(retained.enabled);
    assert_eq!(retained.state_root, retained_lane_root());
    refine(&case, &derived);
}

#[test]
fn prior_replay_rows_are_retained_canonically_around_the_inserted_identity() {
    let lower = ReplayStateV2 {
        replay_id: "!prior-lower".to_owned(),
        occurrence_id: root(11),
    };
    let upper = ReplayStateV2 {
        replay_id: "zz-prior-upper".to_owned(),
        occurrence_id: root(12),
    };
    let case = transfer_case(&FrameOptionsV2 {
        replay_state: vec![lower.clone(), upper.clone()],
        ..FrameOptionsV2::default()
    });

    let derived = derive(&case).expect("prior replay rows derive a successor");

    let inserted = inserted_replay(&case.occurrence);
    assert!(lower.replay_id < inserted.replay_id);
    assert!(inserted.replay_id < upper.replay_id);
    assert_eq!(derived.replay_state, vec![lower, inserted, upper]);
    refine(&case, &derived);
}

#[test]
fn replay_identity_collisions_reject_instead_of_overwriting_a_prior_row() {
    let base = transfer_case(&FrameOptionsV2::default());
    let prior = ReplayStateV2 {
        replay_id: base.occurrence.replay_id().expect("replay id").to_string(),
        occurrence_id: root(13),
    };
    let case = transfer_case(&FrameOptionsV2 {
        replay_state: vec![prior.clone()],
        ..FrameOptionsV2::default()
    });
    assert_eq!(
        case.occurrence.replay_id().expect("replay id").to_string(),
        prior.replay_id
    );
    assert_ne!(
        case.occurrence.occurrence_id().expect("occurrence id"),
        prior.occurrence_id
    );

    let error = derive(&case).expect_err("replay overwrite must fail closed");

    assert_eq!(error, AbiErrorV2::InvalidOrder("global state replay state"));
    assert_eq!(case.global_pre.replay_state, vec![prior]);
}

#[test]
fn duplicate_occurrence_identity_rejects_before_the_relation_is_consulted() {
    let case = transfer_case(&FrameOptionsV2::default());
    let mut forged = case.global_pre.clone();
    forged.replay_state = vec![ReplayStateV2 {
        replay_id: "zz-other".to_owned(),
        occurrence_id: case.occurrence.occurrence_id().expect("occurrence id"),
    }];
    forged
        .validate()
        .expect("forged predecessor stays well formed");

    let error = derive_asset_lane_custody_global_post_v2(
        &case.lane,
        &case.accepted,
        &forged,
        &case.occurrence,
    )
    .expect_err("duplicate occurrence identity must fail closed");

    assert_eq!(
        error,
        AbiErrorV2::InvalidBinding("global state replay occurrence ids")
    );
}

#[test]
fn wrong_predecessor_lane_rejects_and_returns_no_successor() {
    let case = transfer_case(&FrameOptionsV2::default());
    let wrong_lanes = [
        custody_lane("transfer", 70, 30, 100),
        case.accepted.post_state().clone(),
    ];
    for wrong in wrong_lanes {
        assert_ne!(
            wrong.state_root().unwrap(),
            case.lane.state_root().unwrap(),
            "wrong source must differ from the committed predecessor"
        );
        let error = derive_asset_lane_custody_global_post_v2(
            &wrong,
            &case.accepted,
            &case.global_pre,
            &case.occurrence,
        )
        .expect_err("wrong predecessor lane must fail closed");
        assert_eq!(
            error,
            AbiErrorV2::InvalidBinding("custody lane/global complete projection mismatch")
        );
    }
}

#[test]
fn predecessor_that_the_occurrence_does_not_bind_is_rejected() {
    let case = transfer_case(&FrameOptionsV2::default());
    let mut stale = case.global_pre.clone();
    stale.history_root = retained_history_root();
    assert_ne!(
        stale.state_root().unwrap(),
        case.global_pre.state_root().unwrap()
    );

    let error = derive_asset_lane_custody_global_post_v2(
        &case.lane,
        &case.accepted,
        &stale,
        &case.occurrence,
    )
    .expect_err("an unbound predecessor must fail closed");

    let expected = AbiErrorV2::InvalidBinding("global refinement occurrence context mismatch");
    assert_eq!(error, expected);
}

#[test]
fn occurrence_height_that_is_not_the_successor_height_rejects() {
    let SubjectV2 {
        context,
        lane,
        command,
    } = transfer_subject();
    let stale = context
        .occurrence
        .as_ref()
        .expect("transfer occurrence")
        .height;
    let global_pre = predecessor(
        &lane,
        &context,
        &FrameOptionsV2 {
            height: Some(stale),
            ..FrameOptionsV2::default()
        },
    );
    let case = bound_case(lane, &context, &command, global_pre, 1);
    assert_eq!(case.occurrence.height, case.global_pre.height);

    let error = derive(&case).expect_err("stale occurrence height must fail closed");

    let expected = AbiErrorV2::InvalidBinding("global refinement occurrence height mismatch");
    assert_eq!(error, expected);
}

#[test]
fn height_ceiling_rejects_the_successor_at_the_maximum_predecessor_height() {
    let case = transfer_case(&FrameOptionsV2 {
        height: Some(u64::MAX),
        ..FrameOptionsV2::default()
    });
    assert_eq!(case.global_pre.height, u64::MAX);

    let error = derive(&case).expect_err("successor height must not wrap the u64 ceiling");

    assert_eq!(error, AbiErrorV2::InvalidBounds("global state height"));
}

#[test]
fn replay_row_ceiling_rejects_before_the_relation_is_consulted() {
    let case = transfer_case(&FrameOptionsV2::default());
    let mut forged = case.global_pre.clone();
    forged.replay_state = (0..MAX_GLOBAL_REPLAY_ROWS_V2)
        .map(|index| ReplayStateV2 {
            replay_id: format!("prior-{index:06}"),
            occurrence_id: root(index as u64 + 1),
        })
        .collect();
    forged
        .validate()
        .expect("the exact replay ceiling stays representable");

    let error = derive_asset_lane_custody_global_post_v2(
        &case.lane,
        &case.accepted,
        &forged,
        &case.occurrence,
    )
    .expect_err("one row past the replay ceiling must fail closed");

    assert_eq!(
        error,
        AbiErrorV2::InvalidBounds("global state replay state")
    );
}

#[test]
fn repeated_issue_burn_reissue_sequence_chains_admitted_successors() {
    let genesis_lane = custody_lane("managed_issue", 80, 20, 100);
    let issue = managed_subject(false, 7, genesis_lane.clone());
    let burn = managed_subject(true, 5, genesis_lane.clone());
    let reissue = managed_subject(false, 3, genesis_lane.clone());
    let genesis = predecessor(&genesis_lane, &issue.context, &FrameOptionsV2::default());

    let (lane_one, first) = advance(&genesis_lane, &genesis, &issue, 1);
    let (lane_two, second) = advance(&lane_one, &first, &burn, 2);
    let (lane_three, third) = advance(&lane_two, &second, &reissue, 3);

    assert_eq!(first.height, genesis.height + 1);
    assert_eq!(second.height, genesis.height + 2);
    assert_eq!(third.height, genesis.height + 3);
    assert_eq!(first.replay_state.len(), 1);
    assert_eq!(second.replay_state.len(), 2);
    assert_eq!(third.replay_state.len(), 3);
    for row in first.replay_state.iter().chain(&second.replay_state) {
        assert!(third.replay_state.contains(row), "retained replay row");
    }
    assert!(third
        .replay_state
        .windows(2)
        .all(|pair| pair[0].replay_id < pair[1].replay_id));

    assert_eq!(first.supplies, usd_supply(107));
    assert_eq!(second.supplies, usd_supply(102));
    assert_eq!(third.supplies, usd_supply(105));
    assert_eq!(third.balances, vec![account_row("alice", 85)]);
    assert_eq!(lane_three.supply_atoms("USD").unwrap(), 105);
    for state in [&first, &second, &third] {
        assert_eq!(state.custody, genesis.custody);
        assert_eq!(state.liabilities, genesis.liabilities);
        assert_eq!(state.terminal_obligations, genesis.terminal_obligations);
        assert!(state.reserves.is_empty());
        let owned: u128 = state
            .balances
            .iter()
            .chain(&state.custody)
            .map(|row| row.amount_atoms)
            .sum();
        assert_eq!(owned, state.supplies[0].amount_atoms);
    }
}
