#[path = "support/asset_lane_coordinator.rs"]
mod support;

use zenodex_global_settlement_abi_v2::{
    asset_transfer_policy_root_v2, refine_asset_lane_custody_global_v2,
    transition_asset_lane_custody_v2, AssetClassV2, AssetLaneCommandV2, AssetLaneContextV2,
    AssetLaneCustodyAcceptedV2, AssetLaneCustodyResultV2, AssetLaneCustodyStateV2,
    AssetOriginKindV2, AssetSupplyV2, AssetTransferCommandV2, EconomicAmountV2,
    EconomicCommandOccurrenceV2, GlobalEconomicStateV2, LaneIdV2, LaneStateRootV2, ReplayStateV2,
    RootV2, TerminalObligationStatusV2, TerminalObligationV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ALL_LANE_IDS_V2, ASSET_LANE_CUSTODY_STATE_SCHEMA_V2, GLOBAL_SETTLEMENT_ABI_V2,
};

fn root(value: u64) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "custody global test root", false)
        .expect("test root is canonical")
}

fn lane_subject() -> (
    AssetLaneContextV2,
    AssetLaneCustodyStateV2,
    AssetTransferCommandV2,
) {
    let fixture = support::fixture();
    let case = &fixture.accepted["transfer"];
    let mut context: AssetLaneContextV2 = support::typed_vector(&case.vectors, "context");
    let aggregate: zenodex_global_settlement_abi_v2::AssetLaneStateV2 =
        support::typed_vector(&case.vectors, "pre_state");
    let mut command: AssetTransferCommandV2 = support::typed_vector(&case.vectors, "command");
    command.amount_atoms = 10;
    context
        .occurrence
        .as_mut()
        .expect("transfer occurrence")
        .command_body_hash = command.command_body_hash().expect("transfer body hash");
    let mut transfer_state = aggregate.transfer_leaf_state();
    let eur_origin = root(50);
    let mut eur_policy = transfer_state.policies[0].clone();
    eur_policy.asset = "EUR".to_owned();
    eur_policy.transfer_fee_atoms = 0;
    eur_policy.asset_origin_root = Some(eur_origin.clone());
    eur_policy.asset_class = AssetClassV2::RegisteredOrdinaryToken;
    let eur_policy_root =
        asset_transfer_policy_root_v2(&eur_policy).expect("EUR transfer policy root");
    transfer_state.policies.push(eur_policy);
    transfer_state
        .policies
        .sort_by(|left, right| left.asset.cmp(&right.asset));
    transfer_state.balances = vec![EconomicAmountV2 {
        owner: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: ACCOUNT_CUSTODY_DOMAIN_V2.to_owned(),
        amount_atoms: 80,
    }];
    transfer_state.supplies = vec![
        AssetSupplyV2 {
            asset: "EUR".to_owned(),
            amount_atoms: 0,
        },
        AssetSupplyV2 {
            asset: "USD".to_owned(),
            amount_atoms: 100,
        },
    ];
    let mut origin_registry = aggregate.origin_registry;
    let mut eur_record = origin_registry.assets[0].clone();
    eur_record.asset = "EUR".to_owned();
    eur_record.origin_kind = AssetOriginKindV2::TAU_ORIGINATED;
    eur_record.origin_root = eur_origin;
    eur_record.transfer_policy_root = eur_policy_root;
    eur_record.issue_policy_root = RootV2::zero();
    eur_record.asset_class = AssetClassV2::RegisteredOrdinaryToken;
    origin_registry.assets.push(eur_record);
    origin_registry
        .assets
        .sort_by(|left, right| left.asset.cmp(&right.asset));
    let lane = AssetLaneCustodyStateV2 {
        schema: ASSET_LANE_CUSTODY_STATE_SCHEMA_V2.to_owned(),
        transfer_state,
        origin_registry,
        managed_policies: aggregate.managed_policies,
        custody: vec![EconomicAmountV2 {
            owner: "vault".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "vault:primary".to_owned(),
            amount_atoms: 20,
        }],
    };
    (context, lane, command)
}

fn lane_roots(lane: &AssetLaneCustodyStateV2) -> Vec<LaneStateRootV2> {
    ALL_LANE_IDS_V2
        .iter()
        .copied()
        .enumerate()
        .map(|(index, lane_id)| {
            let is_asset = lane_id == LaneIdV2::ASSET_TRANSFER;
            LaneStateRootV2 {
                lane_id,
                module_release_id: if is_asset {
                    lane.module_release_id().clone()
                } else {
                    root(100 + index as u64)
                },
                enabled: is_asset,
                state_root: if is_asset {
                    lane.state_root().expect("lane state root")
                } else {
                    RootV2::zero()
                },
            }
        })
        .collect()
}

struct GlobalCase {
    lane_pre: AssetLaneCustodyStateV2,
    accepted: Box<AssetLaneCustodyAcceptedV2>,
    global_pre: GlobalEconomicStateV2,
    global_post: GlobalEconomicStateV2,
    occurrence: EconomicCommandOccurrenceV2,
}

fn global_case() -> GlobalCase {
    let (mut context, lane, command) = lane_subject();
    let mut occurrence = context.occurrence.clone().expect("transfer occurrence");
    let global_pre = GlobalEconomicStateV2 {
        schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        writer_epoch: context.writer_epoch,
        height: occurrence.height - 1,
        profile_root: occurrence.profile_root.clone(),
        lane_roots: lane_roots(&lane),
        balances: lane.transfer_state.balances.clone(),
        supplies: lane
            .transfer_state
            .supplies
            .iter()
            .filter(|row| row.amount_atoms != 0)
            .cloned()
            .collect(),
        custody: lane.custody.clone(),
        liabilities: vec![EconomicAmountV2 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "vault:primary".to_owned(),
            amount_atoms: 20,
        }],
        reserves: Vec::new(),
        oracle_occurrences: Vec::new(),
        replay_state: Vec::new(),
        terminal_obligations: vec![TerminalObligationV2 {
            obligation_id: "alice-vault-claim".to_owned(),
            lane_id: LaneIdV2::ASSET_TRANSFER,
            claimant: "alice".to_owned(),
            asset: "USD".to_owned(),
            liability_domain: "vault:primary".to_owned(),
            amount_atoms: 20,
            status: TerminalObligationStatusV2::OPEN,
        }],
        history_root: RootV2::zero(),
        outbox: Vec::new(),
    };
    occurrence.pre_state_root = global_pre.state_root().expect("global pre-state root");
    context.global_pre_state_root = occurrence.pre_state_root.clone();
    context.occurrence = Some(occurrence.clone());
    let result =
        transition_asset_lane_custody_v2(&context, &lane, &AssetLaneCommandV2::Transfer(command))
            .expect("custody lane executes");
    let AssetLaneCustodyResultV2::Accepted(accepted) = result else {
        panic!("custody lane fixture must accept")
    };

    let mut global_post = global_pre.clone();
    global_post.height = occurrence.height;
    global_post.balances = accepted.post_state().transfer_state.balances.clone();
    global_post.supplies = accepted
        .post_state()
        .transfer_state
        .supplies
        .iter()
        .filter(|row| row.amount_atoms != 0)
        .cloned()
        .collect();
    let asset_lane = global_post
        .lane_roots
        .iter_mut()
        .find(|row| row.lane_id == LaneIdV2::ASSET_TRANSFER)
        .expect("asset lane root");
    asset_lane.state_root = accepted.post_state().state_root().expect("post lane root");
    global_post.replay_state = vec![ReplayStateV2 {
        replay_id: occurrence.replay_id().expect("replay id").to_string(),
        occurrence_id: occurrence.occurrence_id().expect("occurrence id"),
    }];

    GlobalCase {
        lane_pre: lane,
        accepted,
        global_pre,
        global_post,
        occurrence,
    }
}

#[test]
fn complete_custody_and_claimant_frame_refines_through_the_existing_global_checker() {
    let case = global_case();
    let checked = refine_asset_lane_custody_global_v2(
        &case.lane_pre,
        &case.accepted,
        &case.global_pre,
        &case.global_post,
        &case.occurrence,
    )
    .expect("complete custody global frame refines");
    assert_eq!(
        checked.pre_state_root(),
        &case.global_pre.state_root().unwrap()
    );
    assert_eq!(
        checked.post_state_root(),
        &case.global_post.state_root().unwrap()
    );
    assert_eq!(
        checked.effect_plan_root(),
        &case.accepted.effects().effect_plan_root().unwrap()
    );
    assert_eq!(case.global_pre.liabilities, case.global_post.liabilities);
    assert_eq!(case.global_pre.custody, case.global_post.custody);
    assert_eq!(case.lane_pre.supplies().len(), 2);
    assert_eq!(case.accepted.post_state().supplies().len(), 2);
    assert_eq!(case.global_pre.supplies.len(), 1);
    assert_eq!(case.global_post.supplies.len(), 1);
    assert_eq!(checked.production_authority(), "NONE");
}

#[test]
fn projection_and_claimant_mutants_fail_before_the_common_relation() {
    for mutation in 0..5 {
        let case = global_case();
        let mut forged = case.global_post.clone();
        match mutation {
            0 => forged.custody[0].owner = "mallory".to_owned(),
            1 => forged.custody[0].custody_domain = "foreign".to_owned(),
            2 => forged.custody.clear(),
            3 => {
                forged
                    .lane_roots
                    .iter_mut()
                    .find(|row| row.lane_id == LaneIdV2::ASSET_TRANSFER)
                    .expect("asset lane root")
                    .state_root = root(999)
            }
            4 => forged.liabilities[0].owner = "mallory".to_owned(),
            _ => unreachable!(),
        }
        let error = refine_asset_lane_custody_global_v2(
            &case.lane_pre,
            &case.accepted,
            &case.global_pre,
            &forged,
            &case.occurrence,
        )
        .expect_err("mutated custody global frame must fail");
        let expected = if mutation == 4 {
            "custody global claimant or custody frame changed"
        } else {
            "custody lane/global complete projection mismatch"
        };
        assert!(error.to_string().contains(expected), "{error}");
    }
}

#[test]
fn missing_replay_is_rejected_by_the_existing_global_checker() {
    let case = global_case();
    let mut forged = case.global_post.clone();
    forged.replay_state.clear();
    let error = refine_asset_lane_custody_global_v2(
        &case.lane_pre,
        &case.accepted,
        &case.global_pre,
        &forged,
        &case.occurrence,
    )
    .expect_err("missing replay must fail");
    assert!(
        error
            .to_string()
            .contains("global refinement replay post-state mismatch"),
        "{error}"
    );
}

#[test]
fn source_journal_writer_epoch_is_bound_to_the_global_pre_state() {
    let case = global_case();
    let mut forged_pre = case.global_pre.clone();
    let mut forged_post = case.global_post.clone();
    forged_pre.writer_epoch += 1;
    forged_post.writer_epoch += 1;
    let error = refine_asset_lane_custody_global_v2(
        &case.lane_pre,
        &case.accepted,
        &forged_pre,
        &forged_post,
        &case.occurrence,
    )
    .expect_err("wrong global writer epoch must fail");
    assert!(
        error
            .to_string()
            .contains("custody global source journal binding mismatch"),
        "{error}"
    );
}
