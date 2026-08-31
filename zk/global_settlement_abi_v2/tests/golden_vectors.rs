use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, hash_bytes_sha256_v2, hash_global_v2,
    transition_asset_transfer_v2, AssetTransferCommandV2, AssetTransferContextV2,
    AssetTransferResultV2, AssetTransferStateV2, EconomicCommandOccurrenceV2,
    GlobalEconomicEffectPlanV2, LaneModuleTransitionJournalV2, RootV2, ValidateCanonicalV2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_asset_transfer_golden.json");

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    authority: String,
    fixture_schema: String,
    frozen_v1_golden_sha256: String,
    receipt_root: RootV2,
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
    serde_json::from_str(GOLDEN).expect("committed V2 golden fixture must parse")
}

fn vector_bytes(fixture: &Fixture, name: &str) -> Vec<u8> {
    let vector = fixture
        .vectors
        .get(name)
        .expect("named V2 golden vector must exist");
    let bytes =
        serde_json::to_vec(&vector.canonical).expect("V2 golden canonical value must serialize");
    assert_eq!(hash_bytes_sha256_v2(&bytes), vector.canonical_bytes_sha256);
    bytes
}

fn typed_vector<T>(fixture: &Fixture, name: &str) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&vector_bytes(fixture, name))
        .expect("V2 golden typed vector must decode canonically")
}

#[test]
fn python_and_rust_share_exact_v2_asset_transfer_roots_and_bytes() {
    let fixture = fixture();
    assert_eq!(
        fixture.fixture_schema,
        "zenodex/global-settlement-abi-v2-asset-transfer-golden/v1"
    );
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(
        fixture.frozen_v1_golden_sha256,
        "9e2b233076a0724635dffb3d7f06f1cb26b7b4ac3c79b3ae4f02420e5877c9e4"
    );

    let command: AssetTransferCommandV2 = typed_vector(&fixture, "command");
    let occurrence: EconomicCommandOccurrenceV2 = typed_vector(&fixture, "occurrence");
    let context: AssetTransferContextV2 = typed_vector(&fixture, "context");
    let pre_state: AssetTransferStateV2 = typed_vector(&fixture, "pre_state");
    let expected_post_state: AssetTransferStateV2 = typed_vector(&fixture, "post_state");
    let expected_effects: GlobalEconomicEffectPlanV2 = typed_vector(&fixture, "effect_plan");
    let expected_journal: LaneModuleTransitionJournalV2 = typed_vector(&fixture, "module_journal");

    occurrence
        .validate()
        .expect("golden occurrence must validate");
    context.validate().expect("golden context must validate");
    pre_state.validate().expect("golden state must validate");
    expected_effects
        .validate()
        .expect("golden effect plan must validate");
    expected_journal
        .validate()
        .expect("golden journal must validate");

    assert_eq!(
        command.command_body_hash().expect("command hash"),
        fixture.vectors["command"].expected_root
    );
    assert_eq!(
        occurrence.occurrence_id().expect("occurrence root"),
        fixture.vectors["occurrence"].expected_root
    );
    assert_eq!(
        hash_global_v2("asset-transfer-context-vector-v2", &context).expect("context vector root"),
        fixture.vectors["context"].expected_root
    );
    assert_eq!(
        pre_state.state_root().expect("pre-state root"),
        fixture.vectors["pre_state"].expected_root
    );
    assert_eq!(
        expected_post_state.state_root().expect("post-state root"),
        fixture.vectors["post_state"].expected_root
    );
    assert_eq!(
        expected_effects.effect_plan_root().expect("effect root"),
        fixture.vectors["effect_plan"].expected_root
    );
    assert_eq!(
        expected_journal.journal_root().expect("journal root"),
        fixture.vectors["module_journal"].expected_root
    );

    let result = transition_asset_transfer_v2(&context, &pre_state, &command)
        .expect("golden V2 transfer must execute");
    let AssetTransferResultV2::Accepted(accepted) = result else {
        panic!("golden V2 transfer unexpectedly rejected");
    };
    assert_eq!(accepted.post_state, expected_post_state);
    assert_eq!(accepted.effects, expected_effects);
    assert_eq!(accepted.module_journal, expected_journal);
    assert_eq!(accepted.receipt_root(), &fixture.receipt_root);

    for (name, value) in [
        (
            "command",
            canonical_bytes_v2(&command).expect("command bytes"),
        ),
        (
            "occurrence",
            canonical_bytes_v2(&occurrence).expect("occurrence bytes"),
        ),
        (
            "context",
            canonical_bytes_v2(&context).expect("context bytes"),
        ),
        (
            "pre_state",
            canonical_bytes_v2(&pre_state).expect("pre-state bytes"),
        ),
        (
            "post_state",
            canonical_bytes_v2(&accepted.post_state).expect("post-state bytes"),
        ),
        (
            "effect_plan",
            canonical_bytes_v2(&accepted.effects).expect("effect-plan bytes"),
        ),
        (
            "module_journal",
            canonical_bytes_v2(&accepted.module_journal).expect("journal bytes"),
        ),
    ] {
        assert_eq!(value, vector_bytes(&fixture, name), "{name} byte drift");
    }
}

#[test]
fn closed_decoders_reject_unknown_missing_and_cross_version_fields() {
    let fixture = fixture();
    let mut command = fixture.vectors["command"].canonical.clone();
    command
        .as_object_mut()
        .expect("command object")
        .insert("unknown".to_owned(), Value::Bool(true));
    let unknown = serde_json::to_vec(&command).expect("unknown-field value");
    assert!(decode_canonical_v2::<AssetTransferCommandV2>(&unknown).is_err());

    let mut unknown_policy = fixture.vectors["pre_state"].canonical.clone();
    unknown_policy["policies"][0]
        .as_object_mut()
        .expect("policy object")
        .insert("unknown".to_owned(), Value::Bool(true));
    assert!(decode_canonical_v2::<AssetTransferStateV2>(
        &serde_json::to_vec(&unknown_policy).expect("unknown policy bytes")
    )
    .is_err());

    let mut missing_origin = fixture.vectors["command"].canonical.clone();
    missing_origin
        .as_object_mut()
        .expect("command object")
        .remove("asset_origin_root");
    let missing = serde_json::to_vec(&missing_origin).expect("missing-field value");
    assert!(decode_canonical_v2::<AssetTransferCommandV2>(&missing).is_err());

    let mut missing_occurrence = fixture.vectors["context"].canonical.clone();
    missing_occurrence
        .as_object_mut()
        .expect("context object")
        .remove("occurrence");
    assert!(decode_canonical_v2::<AssetTransferContextV2>(
        &serde_json::to_vec(&missing_occurrence).expect("missing occurrence bytes")
    )
    .is_err());

    let mut missing_policy_origin = fixture.vectors["pre_state"].canonical.clone();
    missing_policy_origin["policies"][0]
        .as_object_mut()
        .expect("policy object")
        .remove("asset_origin_root");
    assert!(decode_canonical_v2::<AssetTransferStateV2>(
        &serde_json::to_vec(&missing_policy_origin).expect("missing policy origin bytes")
    )
    .is_err());

    let mut explicit_null_origin = fixture.vectors["command"].canonical.clone();
    explicit_null_origin["asset_origin_root"] = Value::Null;
    let null_command: AssetTransferCommandV2 = decode_canonical_v2(
        &serde_json::to_vec(&explicit_null_origin).expect("explicit null origin bytes"),
    )
    .expect("required nullable origin accepts explicit null");
    assert_eq!(null_command.asset_origin_root, None);

    let mut old_occurrence = fixture.vectors["occurrence"].canonical.clone();
    old_occurrence["schema"] = Value::String("zenodex/global-settlement-abi/v1".to_owned());
    assert!(decode_canonical_v2::<EconomicCommandOccurrenceV2>(
        &serde_json::to_vec(&old_occurrence).expect("old occurrence bytes")
    )
    .is_err());

    let mut old_state = fixture.vectors["pre_state"].canonical.clone();
    old_state["schema"] = Value::String("zenodex/asset-transfer-module/v1".to_owned());
    assert!(decode_canonical_v2::<AssetTransferStateV2>(
        &serde_json::to_vec(&old_state).expect("old state bytes")
    )
    .is_err());
}
