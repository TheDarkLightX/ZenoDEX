use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    classify_global_economic_refinement_error_v2, decode_canonical_v2, hash_global_v2,
    refine_global_economic_state_effects_outcome_v2, AbiErrorV2, ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2, GlobalEconomicRefinementOutcomeV2,
    GlobalEconomicRefinementRejectCodeV2, GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateV2, GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2, RootV2,
    ValidateCanonicalV2, ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2,
    GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2,
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct Scenario {
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
    occurrences: Vec<zenodex_global_settlement_abi_v2::EconomicCommandOccurrenceV2>,
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

fn root(value: u64, field: &'static str) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), field, false).expect("test root")
}

#[test]
fn golden_candidate_returns_existing_opaque_witness() {
    let candidate_values = scenario();
    let expected_pre_root = candidate_values
        .pre_state
        .state_root()
        .expect("pre-state root");

    let outcome = refine_global_economic_state_effects_outcome_v2(&candidate_values.candidate())
        .expect("deterministic outcome");

    let GlobalEconomicRefinementOutcomeV2::Accepted(accepted) = outcome else {
        panic!("golden candidate must be accepted");
    };
    assert_eq!(accepted.witness().pre_state_root(), &expected_pre_root);
    assert_eq!(
        accepted.production_authority(),
        GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2
    );
}

#[test]
fn cross_domain_liability_backing_is_an_exact_no_op_reject() {
    let same_domain = scenario();
    assert!(matches!(
        refine_global_economic_state_effects_outcome_v2(&same_domain.candidate())
            .expect("deterministic outcome"),
        GlobalEconomicRefinementOutcomeV2::Accepted(_)
    ));

    let mut cross_domain = scenario();
    for row in &mut cross_domain.pre_state.custody {
        row.custody_domain = "unrelated-custody".to_owned();
    }
    for row in &mut cross_domain.post_state.custody {
        row.custody_domain = "unrelated-custody".to_owned();
    }
    cross_domain.pre_state.validate().expect("valid pre-state");
    cross_domain
        .post_state
        .validate()
        .expect("valid post-state");
    let before = cross_domain.clone();
    let pre_root = cross_domain.pre_state.state_root().expect("pre-state root");

    let outcome = refine_global_economic_state_effects_outcome_v2(&cross_domain.candidate())
        .expect("deterministic rejection");

    let GlobalEconomicRefinementOutcomeV2::Rejected(rejected) = outcome else {
        panic!("cross-domain custody must not back a liability");
    };
    assert_eq!(
        rejected.reject_code(),
        GlobalEconomicRefinementRejectCodeV2::LIABILITIES_EXCEED_BACKING
    );
    assert_eq!(rejected.pre_state_root(), &pre_root);
    assert_eq!(rejected.post_state_root(), &pre_root);
    assert_eq!(rejected.effect_plan(), GlobalEconomicEffectPlanV2::empty());
    assert_eq!(
        rejected.terminal_plan(),
        GlobalTerminalObligationPlanV2::empty()
    );
    assert_eq!(
        rejected.oracle_plan(),
        GlobalOracleOccurrencePlanV2::empty()
    );
    assert!(rejected.consumed_occurrences().is_empty());
    assert!(rejected.outbox().is_empty());
    assert_eq!(rejected.production_authority(), "NONE");
    assert_eq!(cross_domain, before);
    assert_eq!(
        classify_global_economic_refinement_error_v2(&AbiErrorV2::Conservation(
            "global refinement liabilities exceed same-domain accounting backing",
        )),
        GlobalEconomicRefinementRejectCodeV2::LIABILITIES_EXCEED_BACKING
    );
}

#[test]
fn representative_reject_is_exact_no_op_and_does_not_mutate_candidate() {
    let mut candidate_values = scenario();
    candidate_values
        .effect_plan
        .external_outbox_enqueue
        .push(ExternalOutboxEnqueueV2 {
            effect_id: root(901, "test effect id"),
            destination_id: "external:adapter".to_owned(),
            payload_hash: root(902, "test payload hash"),
            adapter_profile_root: root(903, "test adapter profile root"),
        });
    candidate_values
        .effect_plan
        .validate()
        .expect("valid outbox row before publisher gate");
    let before = candidate_values.clone();
    let pre_root = candidate_values
        .pre_state
        .state_root()
        .expect("pre-state root");

    let outcome = refine_global_economic_state_effects_outcome_v2(&candidate_values.candidate())
        .expect("deterministic rejection");

    let GlobalEconomicRefinementOutcomeV2::Rejected(rejected) = outcome else {
        panic!("unpublished outbox must be rejected");
    };
    assert_eq!(
        rejected.reject_code(),
        GlobalEconomicRefinementRejectCodeV2::EXTERNAL_OUTBOX_REQUIRES_PUBLISHER
    );
    assert_eq!(rejected.pre_state_root(), &pre_root);
    assert_eq!(rejected.post_state_root(), &pre_root);
    assert_eq!(rejected.effect_plan(), GlobalEconomicEffectPlanV2::empty());
    assert_eq!(
        rejected.terminal_plan(),
        GlobalTerminalObligationPlanV2::empty()
    );
    assert_eq!(
        rejected.oracle_plan(),
        GlobalOracleOccurrencePlanV2::empty()
    );
    assert!(rejected.consumed_occurrences().is_empty());
    assert!(rejected.outbox().is_empty());
    assert_eq!(rejected.production_authority(), "NONE");
    assert_eq!(candidate_values, before);
}

#[test]
fn external_outbox_rejection_has_precedence_over_zero_occurrence_rejection() {
    let mut candidate_values = scenario();
    candidate_values.occurrences.clear();
    candidate_values
        .effect_plan
        .external_outbox_enqueue
        .push(ExternalOutboxEnqueueV2 {
            effect_id: root(911, "test effect id"),
            destination_id: "external:adapter".to_owned(),
            payload_hash: root(912, "test payload hash"),
            adapter_profile_root: root(913, "test adapter profile root"),
        });

    let outcome = refine_global_economic_state_effects_outcome_v2(&candidate_values.candidate())
        .expect("deterministic rejection");

    let GlobalEconomicRefinementOutcomeV2::Rejected(rejected) = outcome else {
        panic!("unpublished outbox must be rejected first");
    };
    assert_eq!(
        rejected.reject_code(),
        GlobalEconomicRefinementRejectCodeV2::EXTERNAL_OUTBOX_REQUIRES_PUBLISHER
    );
}

#[test]
fn malformed_public_rust_candidate_is_bound_and_rejected() {
    let mut candidate_values = scenario();
    candidate_values.post_state.schema = "future/schema".to_owned();
    let expected_pre_root =
        hash_global_v2("global-economic-state-root-v2", &candidate_values.pre_state)
            .expect("submitted pre-state content root");

    let outcome = refine_global_economic_state_effects_outcome_v2(&candidate_values.candidate())
        .expect("deterministic rejection");

    let GlobalEconomicRefinementOutcomeV2::Rejected(rejected) = outcome else {
        panic!("malformed candidate must be rejected");
    };
    assert_eq!(
        rejected.reject_code(),
        GlobalEconomicRefinementRejectCodeV2::MALFORMED_CANDIDATE
    );
    assert_eq!(rejected.pre_state_root(), &expected_pre_root);
    assert_eq!(rejected.post_state_root(), &expected_pre_root);
}

#[test]
fn signed_state_delta_overflow_has_the_shared_python_rust_code() {
    let mut candidate_values = scenario();
    let pre_row = candidate_values
        .pre_state
        .balances
        .first()
        .expect("golden pre-state balance");
    let key = (
        pre_row.asset.clone(),
        pre_row.owner.clone(),
        pre_row.custody_domain.clone(),
    );
    let pre_atoms = pre_row.amount_atoms;
    let post_row = candidate_values
        .post_state
        .balances
        .iter_mut()
        .find(|row| {
            (
                row.asset.as_str(),
                row.owner.as_str(),
                row.custody_domain.as_str(),
            ) == (key.0.as_str(), key.1.as_str(), key.2.as_str())
        })
        .expect("matching golden post-state balance");
    post_row.amount_atoms = pre_atoms + (1_u128 << 127);

    let outcome = refine_global_economic_state_effects_outcome_v2(&candidate_values.candidate())
        .expect("deterministic rejection");

    let GlobalEconomicRefinementOutcomeV2::Rejected(rejected) = outcome else {
        panic!("out-of-i128 state delta must be rejected");
    };
    assert_eq!(
        rejected.reject_code(),
        GlobalEconomicRefinementRejectCodeV2::SIGNED_STATE_DELTA_OVERFLOW
    );
    assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
}

#[test]
fn exact_known_messages_classify_and_unknown_text_is_contract_drift() {
    assert_eq!(
        classify_global_economic_refinement_error_v2(&AbiErrorV2::InvalidBinding(
            "global refinement Oracle occurrence plan mismatch",
        )),
        GlobalEconomicRefinementRejectCodeV2::ORACLE_PLAN_MISMATCH
    );
    assert_eq!(
        classify_global_economic_refinement_error_v2(&AbiErrorV2::InvalidSchema(
            "global economic effect plan",
        )),
        GlobalEconomicRefinementRejectCodeV2::MALFORMED_CANDIDATE
    );
    assert_eq!(
        classify_global_economic_refinement_error_v2(&AbiErrorV2::InvalidBinding(
            "unmapped future validation text",
        )),
        GlobalEconomicRefinementRejectCodeV2::INTERNAL_CONTRACT_DRIFT
    );
}

#[test]
fn reject_code_registry_is_closed_unique_and_wire_stable() {
    let wire_codes = ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2
        .iter()
        .map(|code| code.as_str())
        .collect::<Vec<_>>();
    let unique = wire_codes
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();

    assert_eq!(wire_codes.len(), unique.len());
    for code in ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2 {
        assert_eq!(
            serde_json::to_string(&code).expect("reject code wire JSON"),
            format!("\"{}\"", code.as_str())
        );
    }
    assert_eq!(wire_codes.first(), Some(&"MALFORMED_CANDIDATE"));
    assert_eq!(wire_codes.last(), Some(&"INTERNAL_CONTRACT_DRIFT"));
}
