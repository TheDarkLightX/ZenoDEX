use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    decode_canonical_v2, refine_global_economic_state_effects_v2, AssetConservationRowV2,
    AssetSupplyV2, EconomicAmountV2, EconomicCommandOccurrenceV2, EconomicEffectKindV2,
    EconomicEffectRowV2, ExternalOutboxEnqueueV2, FeeConservationRowV2, GlobalEconomicEffectPlanV2,
    GlobalEconomicStateEffectRefinementCandidateV2, GlobalEconomicStateV2,
    GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2, RootV2, ValidateCanonicalV2,
    FEE_RESIDUE_CONTROL_DOMAIN_V2, FEE_RESIDUE_PRINCIPAL_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_global_core_golden.json");

#[derive(Deserialize)]
struct Fixture {
    vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
struct Vector {
    canonical: Value,
}

struct Scenario {
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
    occurrences: Vec<EconomicCommandOccurrenceV2>,
    terminal_plan: GlobalTerminalObligationPlanV2,
    oracle_plan: GlobalOracleOccurrencePlanV2,
}

impl Scenario {
    fn candidate(&self) -> GlobalEconomicStateEffectRefinementCandidateV2<'_> {
        GlobalEconomicStateEffectRefinementCandidateV2 {
            pre_state: &self.pre_state,
            post_state: &self.post_state,
            effect_plan: &self.effect_plan,
            consumed_occurrences: &self.occurrences,
            terminal_plan: &self.terminal_plan,
            oracle_plan: &self.oracle_plan,
        }
    }
}

fn typed_vector<T>(fixture: &Fixture, name: &str) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    let bytes = serde_json::to_vec(&fixture.vectors[name].canonical).expect("canonical JSON");
    decode_canonical_v2(&bytes).expect("typed global-core vector")
}

fn scenario() -> Scenario {
    let fixture: Fixture = serde_json::from_str(GOLDEN).expect("global-core fixture");
    Scenario {
        pre_state: typed_vector(&fixture, "pre_state"),
        post_state: typed_vector(&fixture, "post_state"),
        effect_plan: typed_vector(&fixture, "effect_plan"),
        occurrences: vec![typed_vector(&fixture, "occurrence")],
        terminal_plan: typed_vector(&fixture, "terminal_plan"),
        oracle_plan: typed_vector(&fixture, "oracle_plan"),
    }
}

#[test]
fn exact_global_refinement_accepts_only_the_complete_candidate() {
    let coherent = scenario();
    assert!(refine_global_economic_state_effects_v2(&coherent.candidate()).is_ok());

    let mut hidden_balance = scenario();
    hidden_balance.post_state.balances[0].amount_atoms -= 1;
    assert!(refine_global_economic_state_effects_v2(&hidden_balance.candidate()).is_err());

    let mut missing_lane = scenario();
    missing_lane
        .effect_plan
        .lane_writes
        .retain(|row| row.lane_id.as_str() != "ORACLE_MARKET");
    assert!(refine_global_economic_state_effects_v2(&missing_lane.candidate()).is_err());

    let mut missing_liability = scenario();
    missing_liability.effect_plan.rows.retain(|row| {
        row.kind != zenodex_global_settlement_abi_v2::EconomicEffectKindV2::LIABILITY
    });
    assert!(refine_global_economic_state_effects_v2(&missing_liability.candidate()).is_err());

    let mut missing_replay = scenario();
    missing_replay.post_state.replay_state.clear();
    assert!(refine_global_economic_state_effects_v2(&missing_replay.candidate()).is_err());

    let mut wrong_terminal_pre = scenario();
    wrong_terminal_pre.terminal_plan.deltas[0].pre_obligation = None;
    assert!(refine_global_economic_state_effects_v2(&wrong_terminal_pre.candidate()).is_err());

    let mut hidden_oracle = scenario();
    hidden_oracle.oracle_plan.deltas.clear();
    assert!(refine_global_economic_state_effects_v2(&hidden_oracle.candidate()).is_err());

    let mut changed_context = scenario();
    changed_context.post_state.writer_epoch += 1;
    assert!(refine_global_economic_state_effects_v2(&changed_context.candidate()).is_err());

    let mut disabled_lane_write = scenario();
    let external_index = disabled_lane_write
        .pre_state
        .lane_roots
        .iter()
        .position(|row| row.lane_id.as_str() == "EXTERNAL_CUSTODY")
        .expect("external-custody lane");
    let pre_root = disabled_lane_write.pre_state.lane_roots[external_index]
        .state_root
        .clone();
    let post_root =
        RootV2::parse(format!("0x{:064x}", 904), "disabled lane post root", false).expect("root");
    disabled_lane_write.post_state.lane_roots[external_index].state_root = post_root.clone();
    disabled_lane_write.effect_plan.lane_writes.insert(
        1,
        zenodex_global_settlement_abi_v2::LaneWriteV2 {
            lane_id: zenodex_global_settlement_abi_v2::LaneIdV2::EXTERNAL_CUSTODY,
            pre_root,
            post_root,
        },
    );
    assert!(disabled_lane_write.effect_plan.validate().is_ok());
    let disabled_error = refine_global_economic_state_effects_v2(&disabled_lane_write.candidate())
        .expect_err("disabled lane mutation must fail")
        .to_string();
    assert!(
        disabled_error.contains("global refinement disabled lane write"),
        "{disabled_error}"
    );
}

#[test]
fn global_refinement_blocks_outbox_and_nonstatic_zero_occurrence_candidates() {
    let mut outbox = scenario();
    outbox
        .effect_plan
        .external_outbox_enqueue
        .push(ExternalOutboxEnqueueV2 {
            effect_id: RootV2::parse(format!("0x{:064x}", 901), "test effect id", false)
                .expect("root"),
            destination_id: "external:adapter".to_owned(),
            payload_hash: RootV2::parse(format!("0x{:064x}", 902), "test payload hash", false)
                .expect("root"),
            adapter_profile_root: RootV2::parse(
                format!("0x{:064x}", 903),
                "test profile root",
                false,
            )
            .expect("root"),
        });
    assert!(outbox.effect_plan.validate().is_ok());
    assert!(refine_global_economic_state_effects_v2(&outbox.candidate()).is_err());

    let mut zero_occurrence = scenario();
    zero_occurrence.occurrences.clear();
    assert!(refine_global_economic_state_effects_v2(&zero_occurrence.candidate()).is_err());
}

#[test]
fn global_state_requires_all_twelve_lanes_and_bounded_canonical_tables() {
    let coherent = scenario();
    assert_eq!(coherent.pre_state.lane_roots.len(), 12);
    assert!(coherent.pre_state.validate().is_ok());

    let mut missing_lane = coherent.pre_state.clone();
    missing_lane.lane_roots.pop();
    assert!(missing_lane.validate().is_err());

    let mut wrong_order = coherent.pre_state.clone();
    wrong_order.lane_roots.swap(0, 1);
    assert!(wrong_order.validate().is_err());

    let mut zero_sparse_row = coherent.pre_state.clone();
    zero_sparse_row.balances[0].amount_atoms = 0;
    assert!(zero_sparse_row.validate().is_err());

    let mut too_many_oracles = coherent.pre_state.clone();
    too_many_oracles.oracle_occurrences =
        vec![coherent.pre_state.oracle_occurrences[0].clone(); 4_097];
    assert!(too_many_oracles.validate().is_err());
}

#[test]
fn replay_and_lifecycle_mutants_fail_closed() {
    let coherent = scenario();

    let mut duplicate_occurrence = coherent.post_state.clone();
    let mut second_replay = duplicate_occurrence.replay_state[0].clone();
    second_replay.replay_id = "second-replay".to_owned();
    duplicate_occurrence.replay_state.push(second_replay);
    assert!(duplicate_occurrence.validate().is_err());

    let mut finality_regression = coherent.oracle_plan.clone();
    finality_regression.deltas[0]
        .pre_occurrence
        .as_mut()
        .expect("pre Oracle")
        .finalized = true;
    finality_regression.deltas[0].post_occurrence.finalized = false;
    let finality_error = finality_regression
        .validate()
        .expect_err("finality regression must fail")
        .to_string();
    assert!(
        finality_error.contains("Oracle occurrence finality cannot regress"),
        "{finality_error}"
    );

    let mut too_many_oracle_deltas = coherent.oracle_plan.clone();
    too_many_oracle_deltas.deltas = vec![too_many_oracle_deltas.deltas[0].clone(); 65];
    assert!(too_many_oracle_deltas.validate().is_err());

    let mut too_many_terminal_deltas = coherent.terminal_plan.clone();
    too_many_terminal_deltas.deltas = vec![too_many_terminal_deltas.deltas[0].clone(); 65];
    assert!(too_many_terminal_deltas.validate().is_err());

    let mut future_oracle = coherent.pre_state.clone();
    future_oracle.oracle_occurrences[0].observed_height = future_oracle.height + 1;
    let future_error = future_oracle
        .validate()
        .expect_err("future Oracle occurrence must fail")
        .to_string();
    assert!(
        future_error.contains("Oracle observed height exceeds global state height"),
        "{future_error}"
    );

    let mut zero_open = coherent.pre_state.clone();
    zero_open.terminal_obligations[0].amount_atoms = 0;
    let zero_open_error = zero_open
        .validate()
        .expect_err("zero OPEN obligation must fail")
        .to_string();
    assert!(
        zero_open_error.contains("open terminal obligation amount must be positive"),
        "{zero_open_error}"
    );

    let mut unbacked_aggregate = scenario();
    let mut second = unbacked_aggregate.pre_state.terminal_obligations[0].clone();
    second.obligation_id = "terminal-2".to_owned();
    second.amount_atoms = 1;
    unbacked_aggregate
        .pre_state
        .terminal_obligations
        .push(second);
    assert!(unbacked_aggregate.pre_state.validate().is_ok());
    let aggregate_error = refine_global_economic_state_effects_v2(&unbacked_aggregate.candidate())
        .expect_err("unbacked OPEN aggregate must fail")
        .to_string();
    assert!(
        aggregate_error
            .contains("global refinement open terminal obligations exceed exact liability row"),
        "{aggregate_error}"
    );
}

#[test]
fn fee_annotations_and_carried_residue_require_exact_state_bearing_mirrors() {
    let mut mirrored_fee = scenario();
    mirrored_fee.effect_plan.rows.insert(
        2,
        EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::FEE_ALLOCATION,
            principal: "bob".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            delta_atoms: 10,
        },
    );
    mirrored_fee.effect_plan.fee_conservation = vec![FeeConservationRowV2 {
        asset: "USD".to_owned(),
        fee_charged_atoms: 10,
        current_allocations_atoms: 10,
        carried_residue_atoms: 0,
    }];
    assert!(mirrored_fee.effect_plan.validate().is_ok());
    assert!(refine_global_economic_state_effects_v2(&mirrored_fee.candidate()).is_ok());

    let mut insufficient_credit = mirrored_fee;
    insufficient_credit.effect_plan.rows[2].delta_atoms = 11;
    insufficient_credit.effect_plan.fee_conservation[0].fee_charged_atoms = 11;
    insufficient_credit.effect_plan.fee_conservation[0].current_allocations_atoms = 11;
    assert!(insufficient_credit.effect_plan.validate().is_ok());
    let credit_error = refine_global_economic_state_effects_v2(&insufficient_credit.candidate())
        .expect_err("insufficient same-key fee credit must fail")
        .to_string();
    assert!(
        credit_error.contains("global refinement fee allocation is not mirrored"),
        "{credit_error}"
    );

    let mut zero_fee = scenario();
    zero_fee.effect_plan.fee_conservation = vec![FeeConservationRowV2 {
        asset: "USD".to_owned(),
        fee_charged_atoms: 0,
        current_allocations_atoms: 0,
        carried_residue_atoms: 0,
    }];
    assert!(zero_fee.effect_plan.validate().is_ok());
    let zero_fee_error = refine_global_economic_state_effects_v2(&zero_fee.candidate())
        .expect_err("zero fee row must fail")
        .to_string();
    assert!(
        zero_fee_error.contains("global refinement zero fee conservation row is noncanonical"),
        "{zero_fee_error}"
    );

    let mut residue = scenario();
    residue.post_state.balances[0].amount_atoms = 87;
    residue.post_state.reserves[0].amount_atoms = 53;
    residue.effect_plan.rows[0].delta_atoms = -13;
    residue.effect_plan.rows.push(EconomicEffectRowV2 {
        kind: EconomicEffectKindV2::RESERVE,
        principal: FEE_RESIDUE_PRINCIPAL_V2.to_owned(),
        asset: "USD".to_owned(),
        custody_domain: FEE_RESIDUE_CONTROL_DOMAIN_V2.to_owned(),
        delta_atoms: 3,
    });
    residue.effect_plan.fee_conservation = vec![FeeConservationRowV2 {
        asset: "USD".to_owned(),
        fee_charged_atoms: 3,
        current_allocations_atoms: 0,
        carried_residue_atoms: 3,
    }];
    assert!(residue.effect_plan.validate().is_ok());
    assert!(refine_global_economic_state_effects_v2(&residue.candidate()).is_ok());

    let mut wrong_residue_principal = residue;
    wrong_residue_principal
        .effect_plan
        .rows
        .last_mut()
        .expect("reserve effect")
        .principal = "protocol:wrong-reserve".to_owned();
    wrong_residue_principal.pre_state.reserves[0].owner = "protocol:wrong-reserve".to_owned();
    wrong_residue_principal.post_state.reserves[0].owner = "protocol:wrong-reserve".to_owned();
    assert!(wrong_residue_principal.effect_plan.validate().is_ok());
    let residue_error =
        refine_global_economic_state_effects_v2(&wrong_residue_principal.candidate())
            .expect_err("wrong residue principal must fail")
            .to_string();
    assert!(
        residue_error.contains("global refinement fee residue state mapping mismatch"),
        "{residue_error}"
    );
}

#[test]
fn global_refinement_preserves_full_u128_supply_delta_parity() {
    let mut maximum_issue = scenario();
    let max_signed = i128::MAX;
    let account_rows = [("big-0", max_signed), ("big-1", max_signed), ("big-2", 1)];
    maximum_issue.post_state.balances.splice(
        0..0,
        account_rows.map(|(owner, amount)| EconomicAmountV2 {
            owner: owner.to_owned(),
            asset: "BIG".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: amount as u128,
        }),
    );
    maximum_issue.post_state.supplies.insert(
        0,
        AssetSupplyV2 {
            asset: "BIG".to_owned(),
            amount_atoms: u128::MAX,
        },
    );
    maximum_issue.effect_plan.rows.splice(
        0..0,
        account_rows.map(|(principal, delta_atoms)| EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ACCOUNT_MOVEMENT,
            principal: principal.to_owned(),
            asset: "BIG".to_owned(),
            custody_domain: "accounts".to_owned(),
            delta_atoms,
        }),
    );
    maximum_issue.effect_plan.rows.splice(
        5..5,
        account_rows.map(|(principal, delta_atoms)| EconomicEffectRowV2 {
            kind: EconomicEffectKindV2::ISSUE,
            principal: principal.to_owned(),
            asset: "BIG".to_owned(),
            custody_domain: "issuance".to_owned(),
            delta_atoms,
        }),
    );
    maximum_issue.effect_plan.asset_conservation.insert(
        0,
        AssetConservationRowV2 {
            asset: "BIG".to_owned(),
            owned_and_custodied_pre_atoms: 0,
            owned_and_custodied_post_atoms: u128::MAX,
            supply_pre_atoms: 0,
            supply_post_atoms: u128::MAX,
            authorized_issue_atoms: u128::MAX,
            authorized_burn_atoms: 0,
        },
    );

    assert!(maximum_issue.effect_plan.validate().is_ok());
    assert!(refine_global_economic_state_effects_v2(&maximum_issue.candidate()).is_ok());
}
