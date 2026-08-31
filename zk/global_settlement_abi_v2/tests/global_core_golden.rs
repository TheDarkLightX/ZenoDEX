use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, hash_bytes_sha256_v2,
    refine_global_economic_state_effects_v2, EconomicCommandOccurrenceV2,
    GlobalEconomicEffectPlanV2, GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateV2, GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2, RootV2,
    ValidateCanonicalV2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_global_core_golden.json");

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    authority: String,
    expected_refinement_root: RootV2,
    expected_replay_id: RootV2,
    expected_state_delta_root: RootV2,
    fixture_schema: String,
    nonclaims: Vec<String>,
    vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Vector {
    canonical: Value,
    canonical_bytes_sha256: String,
    expected_root: RootV2,
}

fn fixture() -> Fixture {
    serde_json::from_str(GOLDEN).expect("committed global-core fixture must parse")
}

fn vector_bytes(fixture: &Fixture, name: &str) -> Vec<u8> {
    let vector = fixture
        .vectors
        .get(name)
        .expect("named global-core vector must exist");
    let bytes = serde_json::to_vec(&vector.canonical).expect("canonical vector JSON");
    assert_eq!(hash_bytes_sha256_v2(&bytes), vector.canonical_bytes_sha256);
    bytes
}

fn typed_vector<T>(fixture: &Fixture, name: &str) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&vector_bytes(fixture, name)).expect("typed global-core vector")
}

#[test]
fn python_and_rust_share_exact_v2_global_core_bytes_roots_and_refinement() {
    let fixture = fixture();
    assert_eq!(
        fixture.fixture_schema,
        "zenodex/global-settlement-abi-v2-global-core-golden/v1"
    );
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(
        fixture.nonclaims,
        ["RISC0", "runtime", "publisher", "migration", "production"]
    );

    let pre_state: GlobalEconomicStateV2 = typed_vector(&fixture, "pre_state");
    let post_state: GlobalEconomicStateV2 = typed_vector(&fixture, "post_state");
    let effect_plan: GlobalEconomicEffectPlanV2 = typed_vector(&fixture, "effect_plan");
    let occurrence: EconomicCommandOccurrenceV2 = typed_vector(&fixture, "occurrence");
    let terminal_plan: GlobalTerminalObligationPlanV2 = typed_vector(&fixture, "terminal_plan");
    let oracle_plan: GlobalOracleOccurrencePlanV2 = typed_vector(&fixture, "oracle_plan");

    assert_eq!(
        pre_state.state_root().expect("pre-state root"),
        fixture.vectors["pre_state"].expected_root
    );
    assert_eq!(
        post_state.state_root().expect("post-state root"),
        fixture.vectors["post_state"].expected_root
    );
    assert_eq!(
        effect_plan.effect_plan_root().expect("effect-plan root"),
        fixture.vectors["effect_plan"].expected_root
    );
    assert_eq!(
        occurrence.occurrence_id().expect("occurrence root"),
        fixture.vectors["occurrence"].expected_root
    );
    assert_eq!(
        occurrence.replay_id().expect("replay root"),
        fixture.expected_replay_id
    );
    assert_eq!(
        terminal_plan.plan_root().expect("terminal plan root"),
        fixture.vectors["terminal_plan"].expected_root
    );
    assert_eq!(
        oracle_plan.plan_root().expect("Oracle plan root"),
        fixture.vectors["oracle_plan"].expected_root
    );

    let candidate = GlobalEconomicStateEffectRefinementCandidateV2 {
        pre_state: &pre_state,
        post_state: &post_state,
        effect_plan: &effect_plan,
        consumed_occurrences: &[occurrence],
        terminal_plan: &terminal_plan,
        oracle_plan: &oracle_plan,
    };
    let witness = refine_global_economic_state_effects_v2(&candidate)
        .expect("Python global-core vector must refine in Rust");
    assert_eq!(witness.production_authority(), "NONE");
    assert_eq!(
        witness.pre_state_root(),
        &fixture.vectors["pre_state"].expected_root
    );
    assert_eq!(
        witness.post_state_root(),
        &fixture.vectors["post_state"].expected_root
    );
    assert_eq!(
        witness.effect_plan_root(),
        &fixture.vectors["effect_plan"].expected_root
    );
    assert_eq!(
        witness.terminal_plan_root(),
        &fixture.vectors["terminal_plan"].expected_root
    );
    assert_eq!(
        witness.oracle_plan_root(),
        &fixture.vectors["oracle_plan"].expected_root
    );
    assert_eq!(
        witness.state_delta_root(),
        &fixture.expected_state_delta_root
    );
    assert_eq!(
        witness.refinement_root().expect("refinement root"),
        fixture.expected_refinement_root
    );

    for (name, bytes) in [
        (
            "pre_state",
            canonical_bytes_v2(&pre_state).expect("pre-state bytes"),
        ),
        (
            "post_state",
            canonical_bytes_v2(&post_state).expect("post-state bytes"),
        ),
        (
            "effect_plan",
            canonical_bytes_v2(&effect_plan).expect("effect-plan bytes"),
        ),
        (
            "occurrence",
            canonical_bytes_v2(&candidate.consumed_occurrences[0]).expect("occurrence bytes"),
        ),
        (
            "terminal_plan",
            canonical_bytes_v2(&terminal_plan).expect("terminal-plan bytes"),
        ),
        (
            "oracle_plan",
            canonical_bytes_v2(&oracle_plan).expect("Oracle-plan bytes"),
        ),
    ] {
        assert_eq!(bytes, vector_bytes(&fixture, name), "{name} byte drift");
    }
}

#[test]
fn global_core_decoders_reject_unknown_fields_and_cross_version_schema() {
    let fixture = fixture();
    let mut state = fixture.vectors["pre_state"].canonical.clone();
    state
        .as_object_mut()
        .expect("state object")
        .insert("unknown".to_owned(), Value::Bool(true));
    assert!(decode_canonical_v2::<GlobalEconomicStateV2>(
        &serde_json::to_vec(&state).expect("unknown-field state")
    )
    .is_err());

    let mut plan = fixture.vectors["oracle_plan"].canonical.clone();
    plan["schema"] = Value::String("zenodex/global-settlement-abi/v1".to_owned());
    assert!(decode_canonical_v2::<GlobalOracleOccurrencePlanV2>(
        &serde_json::to_vec(&plan).expect("old-schema plan")
    )
    .is_err());
}
