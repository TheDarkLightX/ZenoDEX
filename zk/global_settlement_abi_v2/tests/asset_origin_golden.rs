use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, hash_bytes_sha256_v2, hash_global_v2,
    managed_asset_policy_root_v2, transition_asset_origin_registration_v2,
    validate_asset_transfer_policy_origin_v2, validate_managed_asset_policy_origin_v2,
    AssetOriginRecordV2, AssetOriginRegistrationCommandV2, AssetOriginRegistrationContextV2,
    AssetOriginRegistrationRejectCodeV2, AssetOriginRegistrationResultV2,
    AssetOriginRegistryStateV2, AssetTransferPolicyV2, EconomicCommandOccurrenceV2,
    GlobalEconomicEffectPlanV2, LaneModuleTransitionJournalV2, ManagedAssetLifecyclePolicyV2,
    RootV2, ValidateCanonicalV2, ALL_ASSET_ORIGIN_REGISTRATION_REJECT_CODES_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_asset_origin_golden.json");

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    authority: String,
    fixture_schema: String,
    profile_authentication: String,
    python_source_sha256: BTreeMap<String, String>,
    reject_codes: Vec<String>,
    accepted: AcceptedCase,
    rejections: BTreeMap<String, RejectCase>,
    nonclaims: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AcceptedCase {
    receipt_root: RootV2,
    vectors: BTreeMap<String, Vector>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RejectCase {
    expected_code: AssetOriginRegistrationRejectCodeV2,
    context: Vector,
    pre_state: Vector,
    command: Vector,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Vector {
    canonical: Value,
    canonical_bytes_sha256: String,
    expected_root: RootV2,
}

fn fixture() -> Fixture {
    serde_json::from_str(GOLDEN).expect("committed asset-origin fixture must parse")
}

fn vector_bytes(vector: &Vector) -> Vec<u8> {
    let bytes = serde_json::to_vec(&vector.canonical).expect("golden value must serialize");
    assert_eq!(hash_bytes_sha256_v2(&bytes), vector.canonical_bytes_sha256);
    bytes
}

fn typed_vector<T>(vector: &Vector) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&vector_bytes(vector)).expect("golden vector must decode canonically")
}

struct AcceptedValues {
    transfer_policy: AssetTransferPolicyV2,
    managed_policy: ManagedAssetLifecyclePolicyV2,
    command: AssetOriginRegistrationCommandV2,
    occurrence: EconomicCommandOccurrenceV2,
    context: AssetOriginRegistrationContextV2,
    pre_state: AssetOriginRegistryStateV2,
    post_state: AssetOriginRegistryStateV2,
    record: AssetOriginRecordV2,
    effects: GlobalEconomicEffectPlanV2,
    journal: LaneModuleTransitionJournalV2,
}

fn accepted_values(vectors: &BTreeMap<String, Vector>) -> AcceptedValues {
    AcceptedValues {
        transfer_policy: typed_vector(&vectors["transfer_policy"]),
        managed_policy: typed_vector(&vectors["managed_policy"]),
        command: typed_vector(&vectors["command"]),
        occurrence: typed_vector(&vectors["occurrence"]),
        context: typed_vector(&vectors["context"]),
        pre_state: typed_vector(&vectors["pre_state"]),
        post_state: typed_vector(&vectors["post_state"]),
        record: typed_vector(&vectors["record"]),
        effects: typed_vector(&vectors["effect_plan"]),
        journal: typed_vector(&vectors["module_journal"]),
    }
}

fn assert_accepted_roots(vectors: &BTreeMap<String, Vector>, values: &AcceptedValues) {
    assert_eq!(
        values.command.command_body_hash().expect("command root"),
        vectors["command"].expected_root
    );
    assert_eq!(
        values.occurrence.occurrence_id().expect("occurrence root"),
        vectors["occurrence"].expected_root
    );
    assert_eq!(
        hash_global_v2(
            "asset-origin-registration-context-vector-v2",
            &values.context
        )
        .expect("context root"),
        vectors["context"].expected_root
    );
    assert_eq!(
        values.pre_state.state_root().expect("pre-state root"),
        vectors["pre_state"].expected_root
    );
    assert_eq!(
        values.post_state.state_root().expect("post-state root"),
        vectors["post_state"].expected_root
    );
    assert_eq!(
        values.record.record_root().expect("record root"),
        vectors["record"].expected_root
    );
    assert_eq!(
        values.effects.effect_plan_root().expect("effect root"),
        vectors["effect_plan"].expected_root
    );
    assert_eq!(
        values.journal.journal_root().expect("journal root"),
        vectors["module_journal"].expected_root
    );
}

fn assert_accepted_bytes(vectors: &BTreeMap<String, Vector>, values: &AcceptedValues) {
    for (name, bytes) in [
        (
            "transfer_policy",
            canonical_bytes_v2(&values.transfer_policy).expect("transfer policy bytes"),
        ),
        (
            "managed_policy",
            canonical_bytes_v2(&values.managed_policy).expect("managed policy bytes"),
        ),
        (
            "command",
            canonical_bytes_v2(&values.command).expect("command bytes"),
        ),
        (
            "occurrence",
            canonical_bytes_v2(&values.occurrence).expect("occurrence bytes"),
        ),
        (
            "context",
            canonical_bytes_v2(&values.context).expect("context bytes"),
        ),
        (
            "pre_state",
            canonical_bytes_v2(&values.pre_state).expect("pre-state bytes"),
        ),
        (
            "post_state",
            canonical_bytes_v2(&values.post_state).expect("post-state bytes"),
        ),
        (
            "record",
            canonical_bytes_v2(&values.record).expect("record bytes"),
        ),
        (
            "effect_plan",
            canonical_bytes_v2(&values.effects).expect("effect bytes"),
        ),
        (
            "module_journal",
            canonical_bytes_v2(&values.journal).expect("journal bytes"),
        ),
    ] {
        assert_eq!(bytes, vector_bytes(&vectors[name]), "{name}");
    }
}

fn assert_accepted_transition(case: &AcceptedCase, values: &AcceptedValues) {
    let result = transition_asset_origin_registration_v2(
        &values.context,
        &values.pre_state,
        &values.command,
    )
    .expect("golden asset-origin transition must execute");
    let AssetOriginRegistrationResultV2::Accepted(accepted) = result else {
        panic!("golden asset-origin transition unexpectedly rejected");
    };
    assert_eq!(accepted.post_state, values.post_state);
    assert_eq!(accepted.effects, values.effects);
    assert_eq!(accepted.module_journal, values.journal);
    assert_eq!(accepted.receipt_root(), &case.receipt_root);
    assert_eq!(accepted.production_authority(), "NONE");
    assert_eq!(
        validate_asset_transfer_policy_origin_v2(&accepted.post_state, &values.transfer_policy)
            .expect("transfer origin binding"),
        values.record
    );
    assert_eq!(
        validate_managed_asset_policy_origin_v2(&accepted.post_state, &values.managed_policy)
            .expect("managed origin binding"),
        values.record
    );
}

#[test]
fn python_and_rust_share_asset_origin_bytes_roots_policy_bindings_and_transition() {
    let fixture = fixture();
    assert_eq!(
        fixture.fixture_schema,
        "zenodex/global-settlement-abi-v2-asset-origin-golden/v1"
    );
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(fixture.profile_authentication, "SHADOW");
    assert_eq!(fixture.python_source_sha256.len(), 5);
    assert!(fixture
        .python_source_sha256
        .values()
        .all(|digest| digest.len() == 64));
    assert_eq!(
        fixture.reject_codes,
        ALL_ASSET_ORIGIN_REGISTRATION_REJECT_CODES_V2.map(|code| code.as_str().to_owned())
    );
    assert_eq!(fixture.rejections.len(), 12);
    assert_eq!(
        fixture.nonclaims,
        [
            "no RISC0 circuit or receipt",
            "no runtime mount or migration",
            "no UI, release, settlement, or production authority"
        ]
    );
    let values = accepted_values(&fixture.accepted.vectors);
    assert_eq!(
        managed_asset_policy_root_v2(&values.managed_policy).expect("managed policy root"),
        fixture.accepted.vectors["managed_policy"].expected_root
    );
    assert_accepted_roots(&fixture.accepted.vectors, &values);
    assert_accepted_transition(&fixture.accepted, &values);
    assert_accepted_bytes(&fixture.accepted.vectors, &values);
}

#[test]
fn all_python_rejection_vectors_preserve_adjacent_precedence_and_exact_noop() {
    let fixture = fixture();
    for (name, case) in fixture.rejections {
        let context: AssetOriginRegistrationContextV2 = typed_vector(&case.context);
        let state: AssetOriginRegistryStateV2 = typed_vector(&case.pre_state);
        let command: AssetOriginRegistrationCommandV2 = typed_vector(&case.command);
        assert_eq!(
            hash_global_v2("asset-origin-registration-context-vector-v2", &context)
                .expect("context root"),
            case.context.expected_root,
            "{name} context"
        );
        assert_eq!(
            state.state_root().expect("state root"),
            case.pre_state.expected_root,
            "{name} state"
        );
        assert_eq!(
            command.command_body_hash().expect("command root"),
            case.command.expected_root,
            "{name} command"
        );
        let original = state.clone();

        let result = transition_asset_origin_registration_v2(&context, &state, &command)
            .expect("valid rejection vector must execute");
        let AssetOriginRegistrationResultV2::Rejected(rejected) = result else {
            panic!("{name} unexpectedly accepted");
        };
        assert_eq!(rejected.code, case.expected_code, "{name}");
        assert_eq!(rejected.pre_state_root, rejected.post_state_root, "{name}");
        assert!(rejected.effects.is_empty(), "{name}");
        assert_eq!(state, original, "{name}");
    }
}

#[test]
fn asset_origin_command_decoder_rejects_shape_scalar_and_root_mutants() {
    let fixture = fixture();
    let vectors = &fixture.accepted.vectors;
    let command_value = vectors["command"].canonical.clone();
    let mut unknown = command_value.clone();
    unknown
        .as_object_mut()
        .expect("command object")
        .insert("unknown".to_owned(), Value::Bool(true));
    let mut missing = command_value.clone();
    missing
        .as_object_mut()
        .expect("command object")
        .remove("issue_policy_root");
    let mut bool_decimal = command_value.clone();
    bool_decimal["decimals"] = Value::Bool(true);
    let mut numeric_string = command_value.clone();
    numeric_string["decimals"] = Value::String("8".to_owned());
    let mut wrong_enum = command_value.clone();
    wrong_enum["origin_kind"] = Value::String("tau_originated".to_owned());
    let mut uppercase_root = command_value.clone();
    uppercase_root["origin_root"] = Value::String(
        uppercase_root["origin_root"]
            .as_str()
            .expect("origin root")
            .to_uppercase(),
    );
    for mutant in [
        unknown,
        missing,
        bool_decimal,
        numeric_string,
        wrong_enum,
        uppercase_root,
    ] {
        assert!(decode_canonical_v2::<AssetOriginRegistrationCommandV2>(
            &serde_json::to_vec(&mutant).expect("mutant bytes")
        )
        .is_err());
    }
}

#[test]
fn asset_origin_command_decoder_rejects_duplicate_and_trailing_bytes() {
    let fixture = fixture();
    let raw = vector_bytes(&fixture.accepted.vectors["command"]);
    let mut duplicate = vec![123_u8];
    duplicate.extend_from_slice(br#""asset":"USD","#);
    duplicate.extend_from_slice(&raw[1..]);
    assert!(decode_canonical_v2::<AssetOriginRegistrationCommandV2>(&duplicate).is_err());
    let mut trailing = raw.clone();
    trailing.push(b'\n');
    assert!(decode_canonical_v2::<AssetOriginRegistrationCommandV2>(&trailing).is_err());
}

#[test]
fn asset_origin_context_and_state_decoders_reject_shape_order_and_schema_mutants() {
    let fixture = fixture();
    let vectors = &fixture.accepted.vectors;
    let mut missing_occurrence = vectors["context"].canonical.clone();
    missing_occurrence
        .as_object_mut()
        .expect("context object")
        .remove("occurrence");
    assert!(decode_canonical_v2::<AssetOriginRegistrationContextV2>(
        &serde_json::to_vec(&missing_occurrence).expect("missing occurrence bytes")
    )
    .is_err());
    let mut null_occurrence = vectors["context"].canonical.clone();
    null_occurrence["occurrence"] = Value::Null;
    let decoded: AssetOriginRegistrationContextV2 =
        decode_canonical_v2(&serde_json::to_vec(&null_occurrence).expect("null occurrence bytes"))
            .expect("explicit null occurrence is canonical");
    assert_eq!(decoded.occurrence, None);

    let mut reversed = vectors["post_state"].canonical.clone();
    reversed["assets"]
        .as_array_mut()
        .expect("asset rows")
        .reverse();
    assert!(decode_canonical_v2::<AssetOriginRegistryStateV2>(
        &serde_json::to_vec(&reversed).expect("reversed state bytes")
    )
    .is_err());
    let mut old_schema = vectors["post_state"].canonical.clone();
    old_schema["schema"] = Value::String("zenodex/asset-origin-registry/v1".to_owned());
    assert!(decode_canonical_v2::<AssetOriginRegistryStateV2>(
        &serde_json::to_vec(&old_schema).expect("old schema bytes")
    )
    .is_err());
}

#[test]
fn asset_origin_command_decoder_preserves_width_and_token_boundaries() {
    let fixture = fixture();
    let command_value = fixture.accepted.vectors["command"].canonical.clone();
    let mut max_u64 = command_value.clone();
    max_u64["decimals"] = Value::from(u64::MAX);
    let decoded: AssetOriginRegistrationCommandV2 =
        decode_canonical_v2(&serde_json::to_vec(&max_u64).expect("max u64 bytes"))
            .expect("max u64 command width must decode");
    assert_eq!(decoded.decimals, u64::MAX);
    let mut over_u64 = command_value.clone();
    over_u64["decimals"] =
        serde_json::from_str("18446744073709551616").expect("arbitrary-precision JSON integer");
    assert!(decode_canonical_v2::<AssetOriginRegistrationCommandV2>(
        &serde_json::to_vec(&over_u64).expect("over u64 bytes")
    )
    .is_err());
    let mut max_token = command_value.clone();
    max_token["asset"] = Value::String("x".repeat(160));
    assert!(decode_canonical_v2::<AssetOriginRegistrationCommandV2>(
        &serde_json::to_vec(&max_token).expect("max token bytes")
    )
    .is_ok());
    max_token["asset"] = Value::String("x".repeat(161));
    assert!(decode_canonical_v2::<AssetOriginRegistrationCommandV2>(
        &serde_json::to_vec(&max_token).expect("over token bytes")
    )
    .is_err());
}

#[test]
fn transition_validates_public_rust_construction_before_dispatch() {
    let fixture = fixture();
    let vectors = &fixture.accepted.vectors;
    let context: AssetOriginRegistrationContextV2 = typed_vector(&vectors["context"]);
    let state: AssetOriginRegistryStateV2 = typed_vector(&vectors["pre_state"]);
    let command: AssetOriginRegistrationCommandV2 = typed_vector(&vectors["command"]);

    let mut malformed_context = context.clone();
    malformed_context.global_pre_state_root = RootV2::zero();
    assert!(transition_asset_origin_registration_v2(&malformed_context, &state, &command).is_err());

    let mut malformed_command = command.clone();
    malformed_command.asset = "TAU".to_owned();
    assert!(transition_asset_origin_registration_v2(&context, &state, &malformed_command).is_err());

    let mut malformed_state: AssetOriginRegistryStateV2 = typed_vector(&vectors["post_state"]);
    malformed_state.assets.reverse();
    assert!(transition_asset_origin_registration_v2(&context, &malformed_state, &command).is_err());
}
