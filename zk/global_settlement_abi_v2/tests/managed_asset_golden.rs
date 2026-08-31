use std::collections::BTreeMap;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, hash_bytes_sha256_v2, hash_global_v2,
    transition_managed_asset_lifecycle_v2, EconomicCommandOccurrenceV2, GlobalEconomicEffectPlanV2,
    LaneModuleTransitionJournalV2, ManagedAssetLifecycleCommandV2, ManagedAssetLifecycleContextV2,
    ManagedAssetLifecycleResultV2, ManagedAssetLifecycleStateV2, RootV2, ValidateCanonicalV2,
    ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_managed_asset_golden.json");

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    authority: String,
    fixture_schema: String,
    profile_authentication: String,
    python_source_sha256: BTreeMap<String, String>,
    reject_codes: Vec<String>,
    constructor_or_invariant_unreachable_reject_codes: Vec<String>,
    cases: BTreeMap<String, Case>,
    nonclaims: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
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
    serde_json::from_str(GOLDEN).expect("committed managed-asset fixture must parse")
}

fn vector_bytes(case: &Case, name: &str) -> Vec<u8> {
    let vector = case.vectors.get(name).expect("golden vector must exist");
    let bytes = serde_json::to_vec(&vector.canonical).expect("golden value must serialize");
    assert_eq!(hash_bytes_sha256_v2(&bytes), vector.canonical_bytes_sha256);
    bytes
}

fn typed_vector<T>(case: &Case, name: &str) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&vector_bytes(case, name)).expect("golden vector must decode canonically")
}

#[test]
fn python_and_rust_share_exact_managed_issue_and_burn_bytes_roots_and_transitions() {
    let fixture = fixture();
    assert_eq!(
        fixture.fixture_schema,
        "zenodex/global-settlement-abi-v2-managed-asset-golden/v1"
    );
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(fixture.profile_authentication, "SHADOW");
    assert_eq!(fixture.python_source_sha256.len(), 3);
    assert!(fixture
        .python_source_sha256
        .values()
        .all(|digest| digest.len() == 64));
    assert_eq!(
        fixture.reject_codes,
        ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2.map(|code| code.as_str().to_owned())
    );
    assert_eq!(
        fixture.constructor_or_invariant_unreachable_reject_codes,
        ["ASSET_DECIMALS_MISMATCH", "BALANCE_OVERFLOW"]
    );
    assert_eq!(
        fixture.nonclaims,
        [
            "no registry or profile authentication",
            "no runtime route or RISC0 receipt",
            "no settlement, publication, or production authority",
        ]
    );
    assert_eq!(
        fixture.cases.keys().map(String::as_str).collect::<Vec<_>>(),
        ["burn", "issue"]
    );

    for (name, case) in &fixture.cases {
        let command: ManagedAssetLifecycleCommandV2 = typed_vector(case, "command");
        let occurrence: EconomicCommandOccurrenceV2 = typed_vector(case, "occurrence");
        let context: ManagedAssetLifecycleContextV2 = typed_vector(case, "context");
        let pre_state: ManagedAssetLifecycleStateV2 = typed_vector(case, "pre_state");
        let expected_post_state: ManagedAssetLifecycleStateV2 = typed_vector(case, "post_state");
        let expected_effects: GlobalEconomicEffectPlanV2 = typed_vector(case, "effect_plan");
        let expected_journal: LaneModuleTransitionJournalV2 = typed_vector(case, "module_journal");

        assert_eq!(
            command.command_body_hash().expect("command root"),
            case.vectors["command"].expected_root
        );
        assert_eq!(
            occurrence.occurrence_id().expect("occurrence root"),
            case.vectors["occurrence"].expected_root
        );
        assert_eq!(
            hash_global_v2("managed-asset-lifecycle-context-vector-v2", &context)
                .expect("context root"),
            case.vectors["context"].expected_root
        );
        assert_eq!(
            pre_state.state_root().expect("pre-state root"),
            case.vectors["pre_state"].expected_root
        );
        assert_eq!(
            expected_post_state.state_root().expect("post-state root"),
            case.vectors["post_state"].expected_root
        );
        assert_eq!(
            expected_effects.effect_plan_root().expect("effect root"),
            case.vectors["effect_plan"].expected_root
        );
        assert_eq!(
            expected_journal.journal_root().expect("journal root"),
            case.vectors["module_journal"].expected_root
        );

        let result = transition_managed_asset_lifecycle_v2(&context, &pre_state, &command)
            .expect("golden managed transition must execute");
        let ManagedAssetLifecycleResultV2::Accepted(accepted) = result else {
            panic!("golden {name} unexpectedly rejected");
        };
        assert_eq!(accepted.post_state, expected_post_state);
        assert_eq!(accepted.effects, expected_effects);
        assert_eq!(accepted.module_journal, expected_journal);
        assert_eq!(accepted.receipt_root(), &case.receipt_root);

        for (vector_name, value) in [
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
                canonical_bytes_v2(&accepted.effects).expect("effect bytes"),
            ),
            (
                "module_journal",
                canonical_bytes_v2(&accepted.module_journal).expect("journal bytes"),
            ),
        ] {
            assert_eq!(
                value,
                vector_bytes(case, vector_name),
                "{name} {vector_name}"
            );
        }
    }
}

#[test]
fn managed_decoders_reject_unknown_missing_and_cross_version_fields() {
    let fixture = fixture();
    let case = &fixture.cases["issue"];

    let mut unknown = case.vectors["command"].canonical.clone();
    unknown
        .as_object_mut()
        .expect("command object")
        .insert("unknown".to_owned(), Value::Bool(true));
    assert!(decode_canonical_v2::<ManagedAssetLifecycleCommandV2>(
        &serde_json::to_vec(&unknown).expect("unknown-field bytes")
    )
    .is_err());

    for nullable in ["asset_origin_root", "authorization_root"] {
        let mut missing = case.vectors["command"].canonical.clone();
        missing
            .as_object_mut()
            .expect("command object")
            .remove(nullable);
        assert!(decode_canonical_v2::<ManagedAssetLifecycleCommandV2>(
            &serde_json::to_vec(&missing).expect("missing nullable bytes")
        )
        .is_err());
    }

    let mut missing_occurrence = case.vectors["context"].canonical.clone();
    missing_occurrence
        .as_object_mut()
        .expect("context object")
        .remove("occurrence");
    assert!(decode_canonical_v2::<ManagedAssetLifecycleContextV2>(
        &serde_json::to_vec(&missing_occurrence).expect("missing occurrence bytes")
    )
    .is_err());

    for nullable in [
        "asset_origin_root",
        "issue_authority_subject",
        "issue_authorization_root",
        "burn_authorization_root",
    ] {
        let mut missing = case.vectors["pre_state"].canonical.clone();
        missing["policies"][0]
            .as_object_mut()
            .expect("policy object")
            .remove(nullable);
        assert!(decode_canonical_v2::<ManagedAssetLifecycleStateV2>(
            &serde_json::to_vec(&missing).expect("missing policy nullable bytes")
        )
        .is_err());
    }

    let mut null_origin = case.vectors["command"].canonical.clone();
    null_origin["asset_origin_root"] = Value::Null;
    let decoded: ManagedAssetLifecycleCommandV2 =
        decode_canonical_v2(&serde_json::to_vec(&null_origin).expect("nullable origin bytes"))
            .expect("explicit nullable origin must decode");
    assert_eq!(decoded.asset_origin_root, None);

    let mut nullable_policy = case.vectors["pre_state"].canonical.clone();
    nullable_policy["policies"][0]["asset_origin_root"] = Value::Null;
    nullable_policy["policies"][0]["issue_authority_subject"] = Value::Null;
    nullable_policy["policies"][0]["issue_authorization_root"] = Value::Null;
    nullable_policy["policies"][0]["burn_authorization_root"] = Value::Null;
    let decoded_state: ManagedAssetLifecycleStateV2 =
        decode_canonical_v2(&serde_json::to_vec(&nullable_policy).expect("nullable policy bytes"))
            .expect("explicit nullable policy fields must decode");
    assert_eq!(decoded_state.policies[0].asset_origin_root, None);
    assert_eq!(decoded_state.policies[0].issue_authority_subject, None);
    assert_eq!(decoded_state.policies[0].issue_authorization_root, None);
    assert_eq!(decoded_state.policies[0].burn_authorization_root, None);

    let mut invalid_decimals = case.vectors["command"].canonical.clone();
    invalid_decimals["atom_decimals"] = Value::from(7);
    assert!(decode_canonical_v2::<ManagedAssetLifecycleCommandV2>(
        &serde_json::to_vec(&invalid_decimals).expect("invalid decimal bytes")
    )
    .is_err());

    let mut old_state = case.vectors["pre_state"].canonical.clone();
    old_state["schema"] = Value::String("zenodex/managed-asset-lifecycle-module/v1".to_owned());
    assert!(decode_canonical_v2::<ManagedAssetLifecycleStateV2>(
        &serde_json::to_vec(&old_state).expect("old-state bytes")
    )
    .is_err());
}
