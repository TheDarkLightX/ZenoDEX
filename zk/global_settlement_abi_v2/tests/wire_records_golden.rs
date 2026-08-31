#[path = "support/asset_lane_coordinator.rs"]
mod asset_lane_support;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, canonical_wire_bytes_v2, decode_canonical_v2, hash_bytes_sha256_v2,
    refine_global_economic_state_effects_v2, transition_asset_lane_v2,
    transition_asset_origin_registration_v2, transition_managed_asset_lifecycle_v2, AbiErrorV2,
    AssetLaneAcceptedWireV2, AssetLaneContextV2, AssetLaneContextWireV2, AssetLaneRejectedWireV2,
    AssetLaneResultV2, AssetLaneRouteV2, AssetLaneStateV2, AssetOriginRegistrationAcceptedWireV2,
    AssetOriginRegistrationCommandV2, AssetOriginRegistrationContextV2,
    AssetOriginRegistrationRejectCodeV2, AssetOriginRegistrationRejectedWireV2,
    AssetOriginRegistrationResultV2, AssetOriginRegistryStateV2, GlobalEconomicEffectPlanV2,
    GlobalEconomicRefinementAcceptedWireV2, GlobalEconomicRefinementRejectCodeV2,
    GlobalEconomicRefinementRejectedWireV2, GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementCandidateWireV2, GlobalEconomicStateEffectRefinementWireV2,
    GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2,
    ManagedAssetLifecycleAcceptedWireV2, ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2, ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedWireV2, ManagedAssetLifecycleResultV2,
    ManagedAssetLifecycleStateV2, RootV2, ValidateCanonicalV2, ASSET_LANE_PRODUCTION_AUTHORITY_V2,
    ASSET_LANE_PROFILE_AUTHENTICATION_V2, GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2,
    MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2, MAX_CANONICAL_INPUT_BYTES_V2,
};

const GLOBAL_CORE_GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_global_core_golden.json");
const MANAGED_GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_managed_asset_golden.json");
const ORIGIN_GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_asset_origin_golden.json");
const PYTHON_WIRE_GOLDEN_REPOSITORY_PATH: &str =
    "tests/data/global_settlement_abi_v2_wire_records_golden.json";
const REQUIRED_PYTHON_WIRE_GOLDEN_SHA256: &str =
    "1355ef7a23f039e9884b720a60c16787350814e84287134194646fae7636b4c8";

#[derive(Clone, Copy)]
struct WireDtoSpec {
    name: &'static str,
    required_field: &'static str,
}

const WIRE_DTO_SPECS: [WireDtoSpec; 11] = [
    WireDtoSpec {
        name: "GlobalEconomicRefinementAcceptedWireV2",
        required_field: "witness",
    },
    WireDtoSpec {
        name: "GlobalEconomicRefinementRejectedWireV2",
        required_field: "reject_code",
    },
    WireDtoSpec {
        name: "ManagedAssetLifecycleAcceptedWireV2",
        required_field: "post_state",
    },
    WireDtoSpec {
        name: "ManagedAssetLifecycleRejectedWireV2",
        required_field: "code",
    },
    WireDtoSpec {
        name: "AssetOriginRegistrationAcceptedWireV2",
        required_field: "post_state",
    },
    WireDtoSpec {
        name: "AssetOriginRegistrationRejectedWireV2",
        required_field: "code",
    },
    WireDtoSpec {
        name: "AssetLaneContextWireV2",
        required_field: "occurrence",
    },
    WireDtoSpec {
        name: "AssetLaneAcceptedWireV2",
        required_field: "route",
    },
    WireDtoSpec {
        name: "AssetLaneRejectedWireV2",
        required_field: "code",
    },
    WireDtoSpec {
        name: "GlobalEconomicStateEffectRefinementCandidateWireV2",
        required_field: "pre_state",
    },
    WireDtoSpec {
        name: "GlobalEconomicStateEffectRefinementWireV2",
        required_field: "pre_state_root",
    },
];

#[derive(Deserialize)]
struct Vector {
    canonical: Value,
}

#[derive(Deserialize)]
struct GlobalFixture {
    vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
struct Case {
    vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
struct ManagedFixture {
    cases: BTreeMap<String, Case>,
}

#[derive(Deserialize)]
struct OriginFixture {
    accepted: Case,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireGoldenRecord {
    canonical: Value,
    canonical_bytes_sha256: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireGoldenFixture {
    authority: String,
    fixture_schema: String,
    nonclaims: Vec<String>,
    profile_authentication: String,
    records: BTreeMap<String, WireGoldenRecord>,
}

#[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
struct WireByteBoundaryProbe(String);

impl ValidateCanonicalV2 for WireByteBoundaryProbe {
    fn validate_canonical_v2(&self) -> Result<(), AbiErrorV2> {
        Ok(())
    }
}

fn decode_value<T>(value: &Value) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&serde_json::to_vec(value).expect("fixture canonical JSON"))
        .expect("fixture value must decode canonically")
}

fn canonical_round_trip<T>(value: &T)
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    let bytes = canonical_wire_bytes_v2(value).expect("wire canonical bytes");
    let decoded: T = decode_canonical_v2(&bytes).expect("wire canonical decode");
    assert_eq!(
        canonical_wire_bytes_v2(&decoded).expect("round-trip bytes"),
        bytes,
        "canonical wire bytes must be stable"
    );
}

fn verify_required_python_wire_fixture_digest(bytes: &[u8]) -> Result<(), String> {
    let actual = hash_bytes_sha256_v2(bytes);
    if actual == REQUIRED_PYTHON_WIRE_GOLDEN_SHA256 {
        Ok(())
    } else {
        Err(actual)
    }
}

fn required_python_wire_fixture_bytes() -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(PYTHON_WIRE_GOLDEN_REPOSITORY_PATH);
    let bytes = fs::read(&path).unwrap_or_else(|error| {
        panic!(
            "required Python wire golden fixture {}: {error}",
            path.display()
        )
    });
    verify_required_python_wire_fixture_digest(&bytes).unwrap_or_else(|actual| {
        panic!(
            "required Python wire golden fixture SHA-256 {}: expected {}, got {actual}",
            path.display(),
            REQUIRED_PYTHON_WIRE_GOLDEN_SHA256
        )
    });
    bytes
}

fn required_python_wire_fixture() -> WireGoldenFixture {
    let bytes = required_python_wire_fixture_bytes();
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("required Python wire golden fixture JSON: {error}"))
}

fn wire_fixture_record<'a>(fixture: &'a WireGoldenFixture, name: &str) -> &'a WireGoldenRecord {
    fixture
        .records
        .get(name)
        .unwrap_or_else(|| panic!("required Python wire record {name}"))
}

fn assert_wire_golden_record<T>(name: &str, record: &WireGoldenRecord)
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    let python_bytes = serde_json::to_vec(&record.canonical)
        .unwrap_or_else(|error| panic!("Python wire record {name} canonical JSON: {error}"));
    assert_eq!(
        hash_bytes_sha256_v2(&python_bytes),
        record.canonical_bytes_sha256,
        "Python fixture canonical-byte SHA-256 for {name}"
    );
    let rust_value: T = decode_canonical_v2(&python_bytes)
        .unwrap_or_else(|error| panic!("Rust wire decode for {name}: {error}"));
    let rust_bytes = canonical_wire_bytes_v2(&rust_value)
        .unwrap_or_else(|error| panic!("Rust wire canonical bytes for {name}: {error}"));
    assert_eq!(
        rust_bytes, python_bytes,
        "Rust canonical bytes must preserve Python bytes for {name}"
    );
    assert_eq!(
        hash_bytes_sha256_v2(&rust_bytes),
        record.canonical_bytes_sha256,
        "Rust canonical-byte SHA-256 for {name}"
    );
    canonical_round_trip(&rust_value);
}

fn assert_wire_decode_rejected(name: &str, bytes: &[u8]) {
    let rejected = match name {
        "GlobalEconomicRefinementAcceptedWireV2" => {
            decode_canonical_v2::<GlobalEconomicRefinementAcceptedWireV2>(bytes).is_err()
        }
        "GlobalEconomicRefinementRejectedWireV2" => {
            decode_canonical_v2::<GlobalEconomicRefinementRejectedWireV2>(bytes).is_err()
        }
        "ManagedAssetLifecycleAcceptedWireV2" => {
            decode_canonical_v2::<ManagedAssetLifecycleAcceptedWireV2>(bytes).is_err()
        }
        "ManagedAssetLifecycleRejectedWireV2" => {
            decode_canonical_v2::<ManagedAssetLifecycleRejectedWireV2>(bytes).is_err()
        }
        "AssetOriginRegistrationAcceptedWireV2" => {
            decode_canonical_v2::<AssetOriginRegistrationAcceptedWireV2>(bytes).is_err()
        }
        "AssetOriginRegistrationRejectedWireV2" => {
            decode_canonical_v2::<AssetOriginRegistrationRejectedWireV2>(bytes).is_err()
        }
        "AssetLaneContextWireV2" => decode_canonical_v2::<AssetLaneContextWireV2>(bytes).is_err(),
        "AssetLaneAcceptedWireV2" => decode_canonical_v2::<AssetLaneAcceptedWireV2>(bytes).is_err(),
        "AssetLaneRejectedWireV2" => decode_canonical_v2::<AssetLaneRejectedWireV2>(bytes).is_err(),
        "GlobalEconomicStateEffectRefinementCandidateWireV2" => {
            decode_canonical_v2::<GlobalEconomicStateEffectRefinementCandidateWireV2>(bytes)
                .is_err()
        }
        "GlobalEconomicStateEffectRefinementWireV2" => {
            decode_canonical_v2::<GlobalEconomicStateEffectRefinementWireV2>(bytes).is_err()
        }
        _ => panic!("unregistered wire DTO {name}"),
    };
    assert!(rejected, "{name} must reject wire mutant");
}

fn root(value: u64) -> RootV2 {
    RootV2::parse(format!("0x{value:064x}"), "wire-record test root", false)
        .expect("test roots are canonical")
}

fn global_candidate() -> GlobalEconomicStateEffectRefinementCandidateWireV2 {
    let fixture: GlobalFixture = serde_json::from_str(GLOBAL_CORE_GOLDEN).expect("global fixture");
    GlobalEconomicStateEffectRefinementCandidateWireV2 {
        pre_state: decode_value(&fixture.vectors["pre_state"].canonical),
        post_state: decode_value(&fixture.vectors["post_state"].canonical),
        effect_plan: decode_value(&fixture.vectors["effect_plan"].canonical),
        consumed_occurrences: vec![decode_value(&fixture.vectors["occurrence"].canonical)],
        terminal_plan: decode_value(&fixture.vectors["terminal_plan"].canonical),
        oracle_plan: decode_value(&fixture.vectors["oracle_plan"].canonical),
    }
}

fn valid_oversized_candidate_wire() -> GlobalEconomicStateEffectRefinementCandidateWireV2 {
    let mut candidate = global_candidate();
    let asset = "wire-codec-bound-asset".to_owned();
    let balances = (0..10_000)
        .map(|index| zenodex_global_settlement_abi_v2::EconomicAmountV2 {
            owner: format!("owner-{index:05}"),
            asset: asset.clone(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: 1,
        })
        .collect::<Vec<_>>();
    let mut state = candidate.pre_state.clone();
    state.balances = balances;
    state.supplies = vec![zenodex_global_settlement_abi_v2::AssetSupplyV2 {
        asset,
        amount_atoms: 10_000,
    }];
    state.custody.clear();
    state.liabilities.clear();
    state.reserves.clear();
    state.oracle_occurrences.clear();
    state.replay_state.clear();
    state.terminal_obligations.clear();
    state.outbox.clear();
    state.history_root = RootV2::zero();

    candidate.pre_state = state.clone();
    candidate.post_state = state;
    candidate.effect_plan = GlobalEconomicEffectPlanV2::empty();
    candidate.consumed_occurrences.clear();
    candidate.terminal_plan = GlobalTerminalObligationPlanV2::empty();
    candidate.oracle_plan = GlobalOracleOccurrencePlanV2::empty();
    candidate
}

#[test]
fn canonical_wire_encoder_has_exact_one_mib_boundary() {
    assert_eq!(MAX_CANONICAL_INPUT_BYTES_V2, 1_048_576);

    let exact = WireByteBoundaryProbe("x".repeat(MAX_CANONICAL_INPUT_BYTES_V2 - 2));
    assert_eq!(
        canonical_wire_bytes_v2(&exact)
            .expect("exact-bound canonical wire value")
            .len(),
        MAX_CANONICAL_INPUT_BYTES_V2
    );

    let oversized = WireByteBoundaryProbe("x".repeat(MAX_CANONICAL_INPUT_BYTES_V2 - 1));
    assert_eq!(
        canonical_wire_bytes_v2(&oversized),
        Err(AbiErrorV2::InvalidBounds("canonical wire bytes"))
    );
}

#[test]
fn valid_oversized_candidate_wire_is_rejected_only_by_transport_encoder() {
    let candidate = valid_oversized_candidate_wire();
    candidate
        .validate()
        .expect("oversized candidate remains a valid typed wire value");
    let unbounded = canonical_bytes_v2(&candidate).expect("internal canonical candidate bytes");
    assert!(unbounded.len() > MAX_CANONICAL_INPUT_BYTES_V2);
    assert_eq!(
        canonical_wire_bytes_v2(&candidate),
        Err(AbiErrorV2::InvalidBounds("canonical wire bytes"))
    );
    assert_eq!(
        canonical_bytes_v2(&candidate).expect("internal canonical bytes remain available"),
        unbounded
    );
}

#[test]
fn context_and_candidate_wires_have_exact_existing_canonical_parity() {
    let fixture = asset_lane_support::fixture();
    let case = &fixture.accepted["transfer"];
    let context_bytes = asset_lane_support::vector_bytes(&case.vectors, "context");
    let context: AssetLaneContextV2 =
        decode_canonical_v2(&context_bytes).expect("existing context golden bytes");
    let wire: AssetLaneContextWireV2 =
        decode_canonical_v2(&context_bytes).expect("context wire parity decode");
    wire.validate().expect("wire context validates");
    assert_eq!(
        canonical_wire_bytes_v2(&wire).expect("wire context bytes"),
        context_bytes,
        "wire field order must preserve the existing context bytes"
    );
    let domain = wire
        .clone()
        .validated_into_domain()
        .expect("validated context conversion");
    assert_eq!(domain, context);
    assert_eq!(
        canonical_bytes_v2(&domain).expect("domain context bytes"),
        canonical_wire_bytes_v2(&wire).expect("wire context bytes")
    );

    let candidate = global_candidate();
    candidate
        .validate()
        .expect("golden candidate wire validates");
    canonical_round_trip(&candidate);
    let domain_candidate = candidate
        .validated_into_domain()
        .expect("candidate conversion after validation");
    let witness = refine_global_economic_state_effects_v2(&domain_candidate)
        .expect("candidate wire remains refinable after validation");
    assert_eq!(witness.production_authority(), "NONE");
}

#[test]
fn refinement_occurrence_count_precedes_candidate_deep_validation() {
    let mut candidate = global_candidate();
    candidate.pre_state.schema = "wrong-schema".to_owned();
    let poison = candidate.consumed_occurrences[0].clone();
    candidate.consumed_occurrences = vec![poison; 65];
    assert_eq!(
        candidate.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "global refinement consumed occurrences"
        ))
    );

    let domain_candidate = GlobalEconomicStateEffectRefinementCandidateV2 {
        pre_state: &candidate.pre_state,
        post_state: &candidate.post_state,
        effect_plan: &candidate.effect_plan,
        consumed_occurrences: &candidate.consumed_occurrences,
        terminal_plan: &candidate.terminal_plan,
        oracle_plan: &candidate.oracle_plan,
    };
    assert_eq!(
        refine_global_economic_state_effects_v2(&domain_candidate),
        Err(AbiErrorV2::InvalidBounds(
            "global refinement consumed occurrences"
        ))
    );
}

#[test]
fn global_refinement_wires_validate_opaque_observables_and_no_op_rejections() {
    let candidate = global_candidate();
    let domain_candidate = candidate
        .validated_into_domain()
        .expect("candidate conversion");
    let witness = refine_global_economic_state_effects_v2(&domain_candidate)
        .expect("fixture must yield a refinement witness");
    let refinement = GlobalEconomicStateEffectRefinementWireV2 {
        pre_state_root: witness.pre_state_root().clone(),
        post_state_root: witness.post_state_root().clone(),
        effect_plan_root: witness.effect_plan_root().clone(),
        terminal_plan_root: witness.terminal_plan_root().clone(),
        oracle_plan_root: witness.oracle_plan_root().clone(),
        state_delta_root: witness.state_delta_root().clone(),
        production_authority: witness.production_authority().to_owned(),
        refinement_root: witness.refinement_root().expect("derived refinement root"),
    };
    refinement.validate().expect("derived refinement wire");
    canonical_round_trip(&refinement);

    let accepted = GlobalEconomicRefinementAcceptedWireV2 {
        witness: refinement.clone(),
        production_authority: GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2.to_owned(),
    };
    accepted.validate().expect("accepted wire validates");
    canonical_round_trip(&accepted);

    let mut wrong_root = refinement.clone();
    wrong_root.refinement_root = root(700);
    assert_eq!(
        wrong_root.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "global refinement wire refinement root"
        ))
    );

    let rejected = GlobalEconomicRefinementRejectedWireV2 {
        reject_code: GlobalEconomicRefinementRejectCodeV2::MALFORMED_CANDIDATE,
        pre_state_root: witness.pre_state_root().clone(),
        post_state_root: witness.pre_state_root().clone(),
        effect_plan: GlobalEconomicEffectPlanV2::empty(),
        terminal_plan: GlobalTerminalObligationPlanV2::empty(),
        oracle_plan: GlobalOracleOccurrencePlanV2::empty(),
        consumed_occurrences: Vec::new(),
        outbox: Vec::new(),
        production_authority: GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2.to_owned(),
    };
    rejected
        .validate()
        .expect("rejected wire is an exact no-op");
    canonical_round_trip(&rejected);
    let mut no_op_mutant = rejected;
    no_op_mutant.post_state_root = root(701);
    assert_eq!(
        no_op_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "global refinement rejected wire is not a no-op"
        ))
    );
}

#[test]
fn refinement_wire_allows_zero_empty_plan_roots() {
    let pre_state = global_candidate().pre_state;
    let candidate = GlobalEconomicStateEffectRefinementCandidateWireV2 {
        pre_state: pre_state.clone(),
        post_state: pre_state,
        effect_plan: GlobalEconomicEffectPlanV2::empty(),
        consumed_occurrences: Vec::new(),
        terminal_plan: GlobalTerminalObligationPlanV2::empty(),
        oracle_plan: GlobalOracleOccurrencePlanV2::empty(),
    };
    let domain_candidate = candidate
        .validated_into_domain()
        .expect("static zero-plan candidate conversion");
    let witness = refine_global_economic_state_effects_v2(&domain_candidate)
        .expect("static zero-plan candidate refinement");
    assert!(witness.terminal_plan_root().is_zero());
    assert!(witness.oracle_plan_root().is_zero());

    let refinement = GlobalEconomicStateEffectRefinementWireV2 {
        pre_state_root: witness.pre_state_root().clone(),
        post_state_root: witness.post_state_root().clone(),
        effect_plan_root: witness.effect_plan_root().clone(),
        terminal_plan_root: witness.terminal_plan_root().clone(),
        oracle_plan_root: witness.oracle_plan_root().clone(),
        state_delta_root: witness.state_delta_root().clone(),
        production_authority: witness.production_authority().to_owned(),
        refinement_root: witness
            .refinement_root()
            .expect("zero-plan refinement root"),
    };
    refinement
        .validate()
        .expect("wire permits zero empty-plan roots");
    canonical_round_trip(&refinement);
}

#[test]
fn managed_and_origin_wire_observables_recompute_from_existing_golden_transitions() {
    let managed: ManagedFixture = serde_json::from_str(MANAGED_GOLDEN).expect("managed fixture");
    let managed_case = &managed.cases["issue"];
    let managed_context: ManagedAssetLifecycleContextV2 =
        decode_value(&managed_case.vectors["context"].canonical);
    let managed_pre_state: ManagedAssetLifecycleStateV2 =
        decode_value(&managed_case.vectors["pre_state"].canonical);
    let managed_command: ManagedAssetLifecycleCommandV2 =
        decode_value(&managed_case.vectors["command"].canonical);
    let managed_result = transition_managed_asset_lifecycle_v2(
        &managed_context,
        &managed_pre_state,
        &managed_command,
    )
    .expect("managed golden transition");
    let ManagedAssetLifecycleResultV2::Accepted(managed_accepted) = managed_result else {
        panic!("managed golden transition unexpectedly rejected");
    };
    let managed_wire = ManagedAssetLifecycleAcceptedWireV2 {
        post_state: managed_accepted.post_state.clone(),
        effects: managed_accepted.effects.clone(),
        module_journal: managed_accepted.module_journal.clone(),
        receipt_root: managed_accepted.receipt_root().clone(),
        production_authority: managed_accepted.production_authority().to_owned(),
    };
    managed_wire
        .validate()
        .expect("managed derived observables validate");
    canonical_round_trip(&managed_wire);
    let mut managed_receipt_mutant = managed_wire.clone();
    managed_receipt_mutant.receipt_root = root(710);
    assert_eq!(
        managed_receipt_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "managed asset accepted wire bindings"
        ))
    );

    let managed_rejected = ManagedAssetLifecycleRejectedWireV2 {
        code: ManagedAssetLifecycleRejectCodeV2::MISSING_OCCURRENCE,
        pre_state_root: root(711),
        post_state_root: root(711),
        effects: GlobalEconomicEffectPlanV2::empty(),
        terminal_obligations_root: RootV2::zero(),
        oracle_occurrence_plan_root: RootV2::zero(),
        production_authority: MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2.to_owned(),
    };
    managed_rejected
        .validate()
        .expect("managed rejected wire no-op");
    canonical_round_trip(&managed_rejected);
    let mut managed_no_op_mutant = managed_rejected;
    managed_no_op_mutant.post_state_root = root(714);
    assert_eq!(
        managed_no_op_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "managed asset rejected wire is not a no-op"
        ))
    );

    let origin: OriginFixture = serde_json::from_str(ORIGIN_GOLDEN).expect("origin fixture");
    let origin_context: AssetOriginRegistrationContextV2 =
        decode_value(&origin.accepted.vectors["context"].canonical);
    let origin_pre_state: AssetOriginRegistryStateV2 =
        decode_value(&origin.accepted.vectors["pre_state"].canonical);
    let origin_command: AssetOriginRegistrationCommandV2 =
        decode_value(&origin.accepted.vectors["command"].canonical);
    let origin_result = transition_asset_origin_registration_v2(
        &origin_context,
        &origin_pre_state,
        &origin_command,
    )
    .expect("origin golden transition");
    let AssetOriginRegistrationResultV2::Accepted(origin_accepted) = origin_result else {
        panic!("origin golden transition unexpectedly rejected");
    };
    let origin_wire = AssetOriginRegistrationAcceptedWireV2 {
        post_state: origin_accepted.post_state.clone(),
        effects: origin_accepted.effects.clone(),
        module_journal: origin_accepted.module_journal.clone(),
        production_authority: origin_accepted.production_authority().to_owned(),
    };
    origin_wire
        .validate()
        .expect("origin derived observables validate");
    canonical_round_trip(&origin_wire);
    let mut origin_release_mutant = origin_wire.clone();
    origin_release_mutant.module_journal.module_release_id = root(713);
    assert_eq!(
        origin_release_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset origin accepted wire bindings"
        ))
    );

    let origin_rejected = AssetOriginRegistrationRejectedWireV2 {
        code: AssetOriginRegistrationRejectCodeV2::MISSING_OCCURRENCE,
        pre_state_root: root(712),
        post_state_root: root(712),
        effects: GlobalEconomicEffectPlanV2::empty(),
    };
    origin_rejected
        .validate()
        .expect("origin rejected wire no-op");
    canonical_round_trip(&origin_rejected);
    let mut origin_no_op_mutant = origin_rejected;
    origin_no_op_mutant.post_state_root = root(715);
    assert_eq!(
        origin_no_op_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset origin rejected wire is not a no-op"
        ))
    );
}

#[test]
fn lane_wires_reject_unknown_fields_profile_root_and_route_mutants() {
    let fixture = asset_lane_support::fixture();
    let case = &fixture.accepted["transfer"];
    let context: AssetLaneContextV2 = asset_lane_support::typed_vector(&case.vectors, "context");
    let pre_state: AssetLaneStateV2 = asset_lane_support::typed_vector(&case.vectors, "pre_state");
    let command = asset_lane_support::command(&case.vectors, &case.command_type);
    let result = transition_asset_lane_v2(&context, &pre_state, &command)
        .expect("asset lane golden transition");
    let AssetLaneResultV2::Accepted(accepted) = result else {
        panic!("asset lane golden transition unexpectedly rejected");
    };
    let accepted_wire = AssetLaneAcceptedWireV2 {
        route: accepted.route(),
        source_leaf_journal_root: accepted.source_leaf_journal_root().clone(),
        post_state: accepted.post_state().clone(),
        effects: accepted.effects().clone(),
        module_journal: accepted.module_journal().clone(),
        receipt_root: accepted.receipt_root().clone(),
        production_authority: accepted.production_authority().to_owned(),
        profile_authentication: accepted.profile_authentication().to_owned(),
    };
    accepted_wire.validate().expect("accepted lane wire");
    canonical_round_trip(&accepted_wire);

    let mut profile_mutant = accepted_wire.clone();
    profile_mutant.profile_authentication = "LIVE".to_owned();
    assert_eq!(
        profile_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset lane accepted wire profile authentication"
        ))
    );
    let mut receipt_mutant = accepted_wire.clone();
    receipt_mutant.receipt_root = root(720);
    assert_eq!(
        receipt_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset lane accepted wire bindings"
        ))
    );

    let context_wire = AssetLaneContextWireV2 {
        writer_epoch: context.writer_epoch,
        module_release_id: context.module_release_id.clone(),
        global_pre_state_root: context.global_pre_state_root.clone(),
        occurrence: context.occurrence.clone(),
    };
    let mut unknown = serde_json::to_value(&context_wire).expect("wire context JSON");
    unknown
        .as_object_mut()
        .expect("wire context object")
        .insert("unknown".to_owned(), Value::Bool(true));
    assert!(decode_canonical_v2::<AssetLaneContextWireV2>(
        &serde_json::to_vec(&unknown).expect("unknown-field bytes")
    )
    .is_err());
    let mut missing = serde_json::to_value(&context_wire).expect("wire context JSON");
    missing
        .as_object_mut()
        .expect("wire context object")
        .remove("occurrence");
    assert!(decode_canonical_v2::<AssetLaneContextWireV2>(
        &serde_json::to_vec(&missing).expect("missing-field bytes")
    )
    .is_err());

    let rejected = AssetLaneRejectedWireV2 {
        route: AssetLaneRouteV2::COORDINATOR,
        code: "REGISTRY_BINDING_MISMATCH".to_owned(),
        pre_state_root: root(721),
        post_state_root: root(721),
        effects: GlobalEconomicEffectPlanV2::empty(),
        production_authority: ASSET_LANE_PRODUCTION_AUTHORITY_V2.to_owned(),
        profile_authentication: ASSET_LANE_PROFILE_AUTHENTICATION_V2.to_owned(),
    };
    rejected.validate().expect("closed coordinator code");
    canonical_round_trip(&rejected);
    let mut route_mutant = rejected.clone();
    route_mutant.route = AssetLaneRouteV2::TRANSFER;
    assert_eq!(
        route_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset lane rejected wire route code"
        ))
    );
    assert_eq!(
        canonical_wire_bytes_v2(&route_mutant),
        Err(AbiErrorV2::InvalidBinding(
            "asset lane rejected wire route code"
        ))
    );
    let mut no_op_mutant = rejected;
    no_op_mutant.post_state_root = root(722);
    assert_eq!(
        no_op_mutant.validate(),
        Err(AbiErrorV2::InvalidBinding(
            "asset lane rejected wire is not a no-op"
        ))
    );
}

#[test]
fn required_python_wire_golden_has_all_records_and_rust_canonical_parity() {
    let fixture = required_python_wire_fixture();
    assert_eq!(
        fixture.fixture_schema,
        "zenodex/global-settlement-abi-v2-wire-records-golden/v1"
    );
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(fixture.profile_authentication, "SHADOW");
    assert!(
        !fixture.nonclaims.is_empty(),
        "Python wire fixture must declare its nonclaims"
    );
    assert_eq!(WIRE_DTO_SPECS.len(), 11);
    assert_eq!(fixture.records.len(), WIRE_DTO_SPECS.len());
    for spec in WIRE_DTO_SPECS {
        assert!(
            fixture.records.contains_key(spec.name),
            "required Python wire record {}",
            spec.name
        );
    }
    for name in fixture.records.keys() {
        assert!(
            WIRE_DTO_SPECS.iter().any(|spec| spec.name == name),
            "unregistered Python wire record {name}"
        );
    }

    assert_wire_golden_record::<GlobalEconomicRefinementAcceptedWireV2>(
        "GlobalEconomicRefinementAcceptedWireV2",
        wire_fixture_record(&fixture, "GlobalEconomicRefinementAcceptedWireV2"),
    );
    assert_wire_golden_record::<GlobalEconomicRefinementRejectedWireV2>(
        "GlobalEconomicRefinementRejectedWireV2",
        wire_fixture_record(&fixture, "GlobalEconomicRefinementRejectedWireV2"),
    );
    assert_wire_golden_record::<ManagedAssetLifecycleAcceptedWireV2>(
        "ManagedAssetLifecycleAcceptedWireV2",
        wire_fixture_record(&fixture, "ManagedAssetLifecycleAcceptedWireV2"),
    );
    assert_wire_golden_record::<ManagedAssetLifecycleRejectedWireV2>(
        "ManagedAssetLifecycleRejectedWireV2",
        wire_fixture_record(&fixture, "ManagedAssetLifecycleRejectedWireV2"),
    );
    assert_wire_golden_record::<AssetOriginRegistrationAcceptedWireV2>(
        "AssetOriginRegistrationAcceptedWireV2",
        wire_fixture_record(&fixture, "AssetOriginRegistrationAcceptedWireV2"),
    );
    assert_wire_golden_record::<AssetOriginRegistrationRejectedWireV2>(
        "AssetOriginRegistrationRejectedWireV2",
        wire_fixture_record(&fixture, "AssetOriginRegistrationRejectedWireV2"),
    );
    assert_wire_golden_record::<AssetLaneContextWireV2>(
        "AssetLaneContextWireV2",
        wire_fixture_record(&fixture, "AssetLaneContextWireV2"),
    );
    assert_wire_golden_record::<AssetLaneAcceptedWireV2>(
        "AssetLaneAcceptedWireV2",
        wire_fixture_record(&fixture, "AssetLaneAcceptedWireV2"),
    );
    assert_wire_golden_record::<AssetLaneRejectedWireV2>(
        "AssetLaneRejectedWireV2",
        wire_fixture_record(&fixture, "AssetLaneRejectedWireV2"),
    );
    assert_wire_golden_record::<GlobalEconomicStateEffectRefinementCandidateWireV2>(
        "GlobalEconomicStateEffectRefinementCandidateWireV2",
        wire_fixture_record(
            &fixture,
            "GlobalEconomicStateEffectRefinementCandidateWireV2",
        ),
    );
    assert_wire_golden_record::<GlobalEconomicStateEffectRefinementWireV2>(
        "GlobalEconomicStateEffectRefinementWireV2",
        wire_fixture_record(&fixture, "GlobalEconomicStateEffectRefinementWireV2"),
    );
}

#[test]
fn required_python_wire_golden_digest_rejects_one_byte_mutation() {
    let mut bytes = required_python_wire_fixture_bytes();
    let first = bytes
        .first_mut()
        .expect("required Python wire fixture is nonempty");
    *first ^= 1;
    assert!(verify_required_python_wire_fixture_digest(&bytes).is_err());
}

#[test]
fn required_python_wire_golden_rejects_unknown_and_missing_fields_for_all_wire_dtos() {
    let fixture = required_python_wire_fixture();
    assert_eq!(WIRE_DTO_SPECS.len(), 11);
    assert_eq!(fixture.records.len(), WIRE_DTO_SPECS.len());
    for spec in WIRE_DTO_SPECS {
        let record = wire_fixture_record(&fixture, spec.name);
        let mut unknown = record.canonical.clone();
        unknown
            .as_object_mut()
            .expect("canonical wire record object")
            .insert("unexpected_wire_field".to_owned(), Value::Bool(true));
        let unknown_bytes =
            serde_json::to_vec(&unknown).expect("unknown-field wire mutant canonical bytes");
        assert_wire_decode_rejected(spec.name, &unknown_bytes);

        let mut missing = record.canonical.clone();
        assert!(
            missing
                .as_object_mut()
                .expect("canonical wire record object")
                .remove(spec.required_field)
                .is_some(),
            "{} must include required field {}",
            spec.name,
            spec.required_field
        );
        let missing_bytes =
            serde_json::to_vec(&missing).expect("missing-field wire mutant canonical bytes");
        assert_wire_decode_rejected(spec.name, &missing_bytes);
    }
}
