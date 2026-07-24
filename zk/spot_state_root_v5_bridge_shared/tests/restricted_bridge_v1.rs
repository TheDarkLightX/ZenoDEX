use serde_json::Value;
use tau_state_proof_risc0_shared::{
    sha256_canonical_dex_snapshot_v1, DexSnapshotV1, FeeAccumulatorV1, NonceEntryV1,
};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    verify_restricted_spot_state_root_v5_transition_v1, ExpectedLegacySpotCommitmentsV1,
    ExpectedSpotStateRootsV5, RestrictedSpotStateRootV5BridgeError,
    RestrictedSpotStateRootV5ProfileV1, RestrictedSpotStateRootV5TransitionInputV1,
    RESTRICTED_SPOT_STATE_ROOT_V5_PROFILE_RULES_V1,
};

const FIXTURE_BYTES: &str =
    include_str!("../../../tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json");

fn fixture() -> Value {
    serde_json::from_str(FIXTURE_BYTES).expect("fixture is valid JSON")
}

fn snapshot(document: &Value, field: &str) -> DexSnapshotV1 {
    serde_json::from_value(document[field].clone()).expect("fixture snapshot decodes")
}

fn pre_nonces(document: &Value) -> Vec<NonceEntryV1> {
    serde_json::from_value(document["pre_nonces"].clone()).expect("fixture nonces decode")
}

fn hex32(value: &str) -> [u8; 32] {
    let body = value.strip_prefix("0x").expect("hex value is 0x-prefixed");
    assert_eq!(body.len(), 64);
    let mut output = [0_u8; 32];
    for (index, pair) in body.as_bytes().chunks_exact(2).enumerate() {
        output[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    output
}

fn nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => panic!("fixture contains noncanonical hex"),
    }
}

fn expected_roots(document: &Value) -> ExpectedSpotStateRootsV5 {
    ExpectedSpotStateRootsV5::new(
        hex32(document["expected"]["pre_state_root_v5"].as_str().unwrap()),
        hex32(document["expected"]["post_state_root_v5"].as_str().unwrap()),
    )
}

fn expected_source(document: &Value) -> ExpectedLegacySpotCommitmentsV1 {
    let expected = &document["expected"];
    ExpectedLegacySpotCommitmentsV1::new(
        hex32(expected["source_pre_app_hash"].as_str().unwrap()),
        hex32(expected["source_post_app_hash"].as_str().unwrap()),
        hex32(expected["source_pre_nonce_root"].as_str().unwrap()),
        hex32(expected["source_post_nonce_root"].as_str().unwrap()),
    )
}

fn nonce_one_source(document: &Value, app_hash: [u8; 32]) -> ExpectedLegacySpotCommitmentsV1 {
    let expected = &document["nonce_one_mapping"];
    ExpectedLegacySpotCommitmentsV1::new(
        app_hash,
        app_hash,
        hex32(expected["source_pre_nonce_root"].as_str().unwrap()),
        hex32(expected["source_post_nonce_root"].as_str().unwrap()),
    )
}

fn empty_snapshot() -> DexSnapshotV1 {
    DexSnapshotV1 {
        version: 1,
        balances: Vec::new(),
        pools: Vec::new(),
        lp_balances: Vec::new(),
        fee_accumulator: FeeAccumulatorV1 { dust: 0 },
        vault: None,
        oracle: None,
    }
}

#[test]
fn profile_id_binds_the_complete_shared_acceptance_descriptor() {
    let document = fixture();
    let fixture_rules: Vec<&str> = document["compatibility_profile_rules"]
        .as_array()
        .unwrap()
        .iter()
        .map(|rule| rule.as_str().unwrap())
        .collect();
    assert_eq!(
        fixture_rules.as_slice(),
        RESTRICTED_SPOT_STATE_ROOT_V5_PROFILE_RULES_V1
    );
    assert_eq!(
        RestrictedSpotStateRootV5ProfileV1::governed().profile_id(),
        hex32(
            document["expected"]["compatibility_profile_id"]
                .as_str()
                .unwrap()
        )
    );
}

#[test]
fn shared_vector_matches_exact_v5_roots_and_source_commitments() {
    let document = fixture();
    let pre = snapshot(&document, "pre_state");
    let post = snapshot(&document, "post_state");
    let nonces = pre_nonces(&document);
    let facts = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            document["sender_pubkey"].as_str().unwrap(),
            document["ingress_nonce"].as_u64().unwrap(),
            expected_source(&document),
            expected_roots(&document),
        ),
    )
    .unwrap();
    let expected = &document["expected"];
    assert_eq!(
        facts.compatibility_profile_id(),
        hex32(expected["compatibility_profile_id"].as_str().unwrap())
    );
    assert_eq!(
        facts.state_root_scheme_id(),
        hex32(expected["state_root_scheme_id"].as_str().unwrap())
    );
    assert_eq!(
        facts.source_pre_app_hash(),
        hex32(expected["source_pre_app_hash"].as_str().unwrap())
    );
    assert_eq!(
        facts.source_post_app_hash(),
        hex32(expected["source_post_app_hash"].as_str().unwrap())
    );
    assert_eq!(
        facts.source_pre_nonce_root(),
        hex32(expected["source_pre_nonce_root"].as_str().unwrap())
    );
    assert_eq!(
        facts.source_post_nonce_root(),
        hex32(expected["source_post_nonce_root"].as_str().unwrap())
    );
    assert_eq!(facts.ingress_nonce(), 7);
}

#[test]
fn nonce_zero_and_extra_nonce_entries_reject() {
    let document = fixture();
    let pre = snapshot(&document, "pre_state");
    let post = snapshot(&document, "post_state");
    let sender = document["sender_pubkey"].as_str().unwrap();
    let zero = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &[],
            sender,
            0,
            expected_source(&document),
            expected_roots(&document),
        ),
    );
    assert_eq!(
        zero.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::IngressNonceZero
    );

    let mut extra = pre_nonces(&document);
    extra.push(NonceEntryV1 {
        pubkey: "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
        next_nonce: 1,
    });
    let result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &extra,
            sender,
            7,
            expected_source(&document),
            expected_roots(&document),
        ),
    );
    assert_eq!(
        result.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::NonCanonicalNonceSet
    );
}

#[test]
fn ingress_one_maps_from_omitted_runtime_zero_to_runtime_last_one() {
    let document = fixture();
    let state = empty_snapshot();
    let sender = document["sender_pubkey"].as_str().unwrap();
    let nonces = [NonceEntryV1 {
        pubkey: sender.into(),
        next_nonce: 1,
    }];
    let expected = &document["nonce_one_mapping"];
    let facts = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &state,
            &state,
            &nonces,
            sender,
            1,
            nonce_one_source(
                &document,
                hex32(expected["source_app_hash"].as_str().unwrap()),
            ),
            ExpectedSpotStateRootsV5::new(
                hex32(expected["pre_state_root_v5"].as_str().unwrap()),
                hex32(expected["post_state_root_v5"].as_str().unwrap()),
            ),
        ),
    )
    .unwrap();
    assert_eq!(
        facts.pre_state_root_v5(),
        hex32(expected["pre_state_root_v5"].as_str().unwrap())
    );
    assert_eq!(
        facts.post_state_root_v5(),
        hex32(expected["post_state_root_v5"].as_str().unwrap())
    );
}

#[test]
fn ingress_u32_max_maps_without_narrowing_or_successor_overflow() {
    let document = fixture();
    let state = empty_snapshot();
    let sender = document["sender_pubkey"].as_str().unwrap();
    let mapping = &document["nonce_u32_max_mapping"];
    let ingress_nonce = mapping["ingress_nonce"].as_u64().unwrap();
    let nonces = [NonceEntryV1 {
        pubkey: sender.into(),
        next_nonce: ingress_nonce,
    }];
    let app_hash = hex32(mapping["source_app_hash"].as_str().unwrap());
    let facts = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &state,
            &state,
            &nonces,
            sender,
            ingress_nonce,
            ExpectedLegacySpotCommitmentsV1::new(
                app_hash,
                app_hash,
                hex32(mapping["source_pre_nonce_root"].as_str().unwrap()),
                hex32(mapping["source_post_nonce_root"].as_str().unwrap()),
            ),
            ExpectedSpotStateRootsV5::new(
                hex32(mapping["pre_state_root_v5"].as_str().unwrap()),
                hex32(mapping["post_state_root_v5"].as_str().unwrap()),
            ),
        ),
    )
    .unwrap();
    assert_eq!(facts.ingress_nonce(), u32::MAX);

    let too_large = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &state,
            &state,
            &nonces,
            sender,
            u64::from(u32::MAX) + 1,
            ExpectedLegacySpotCommitmentsV1::new(app_hash, app_hash, [0; 32], [0; 32]),
            ExpectedSpotStateRootsV5::new([0; 32], [0; 32]),
        ),
    );
    assert_eq!(
        too_large.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::IngressNonceTooLarge
    );
}

#[test]
fn reordered_multi_entry_snapshots_and_nonzero_fee_match_exact_commitments() {
    let document = fixture();
    let mut pre = snapshot(&document, "pre_state");
    let mut post = snapshot(&document, "post_state");
    pre.balances.reverse();
    post.balances.reverse();
    let nonces = pre_nonces(&document);
    verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            document["sender_pubkey"].as_str().unwrap(),
            7,
            expected_source(&document),
            expected_roots(&document),
        ),
    )
    .unwrap();

    let mapping = &document["nonzero_fee_mapping"];
    pre.fee_accumulator.dust = mapping["dust"].as_u64().unwrap().into();
    post.fee_accumulator.dust = mapping["dust"].as_u64().unwrap().into();
    verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            document["sender_pubkey"].as_str().unwrap(),
            7,
            ExpectedLegacySpotCommitmentsV1::new(
                hex32(mapping["source_pre_app_hash"].as_str().unwrap()),
                hex32(mapping["source_post_app_hash"].as_str().unwrap()),
                hex32(
                    document["expected"]["source_pre_nonce_root"]
                        .as_str()
                        .unwrap(),
                ),
                hex32(
                    document["expected"]["source_post_nonce_root"]
                        .as_str()
                        .unwrap(),
                ),
            ),
            ExpectedSpotStateRootsV5::new(
                hex32(mapping["pre_state_root_v5"].as_str().unwrap()),
                hex32(mapping["post_state_root_v5"].as_str().unwrap()),
            ),
        ),
    )
    .unwrap();
}

#[test]
fn duplicate_balance_and_unknown_lp_pool_reject_before_commitment_binding() {
    let document = fixture();
    let post = snapshot(&document, "post_state");
    let nonces = pre_nonces(&document);
    let sender = document["sender_pubkey"].as_str().unwrap();

    let mut duplicate = snapshot(&document, "pre_state");
    duplicate.balances.push(duplicate.balances[0].clone());
    let duplicate_result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &duplicate,
            &post,
            &nonces,
            sender,
            7,
            expected_source(&document),
            expected_roots(&document),
        ),
    );
    assert_eq!(
        duplicate_result.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::DuplicateKey("balances")
    );

    let mut unknown_pool = snapshot(&document, "pre_state");
    unknown_pool.lp_balances[0].pool_id = format!("0x{}", "dd".repeat(32));
    let unknown_result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &unknown_pool,
            &post,
            &nonces,
            sender,
            7,
            expected_source(&document),
            expected_roots(&document),
        ),
    );
    assert_eq!(
        unknown_result.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::UnknownLpPool
    );
}

#[test]
fn nonempty_curve_configuration_cannot_enter_the_implicit_cpmm_profile() {
    let document = fixture();
    let mut pre = snapshot(&document, "pre_state");
    let post = snapshot(&document, "post_state");
    let nonces = pre_nonces(&document);
    pre.pools[0].pool_id =
        "0x0ab5965596eae4d536248f142f2dc413de9d9abf61b5d548a6bc1d7893962ffa".into();
    let result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            document["sender_pubkey"].as_str().unwrap(),
            7,
            expected_source(&document),
            expected_roots(&document),
        ),
    );
    assert_eq!(
        result.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::PoolIdentityMismatch
    );
}

#[test]
fn lp_duration_ambiguity_rejects_the_nonempty_header_root() {
    let document = fixture();
    let mut state = snapshot(&document, "pre_state");
    state.balances.clear();
    let ambiguity = &document["lp_duration_ambiguity"];
    assert_eq!(
        sha256_canonical_dex_snapshot_v1(&state),
        hex32(ambiguity["legacy_app_hash"].as_str().unwrap())
    );
    let sender = document["sender_pubkey"].as_str().unwrap();
    let nonces = [NonceEntryV1 {
        pubkey: sender.into(),
        next_nonce: 1,
    }];
    let result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &state,
            &state,
            &nonces,
            sender,
            1,
            nonce_one_source(
                &document,
                hex32(ambiguity["legacy_app_hash"].as_str().unwrap()),
            ),
            ExpectedSpotStateRootsV5::new(
                hex32(
                    ambiguity["last_mint_timestamp_7_state_root_v5"]
                        .as_str()
                        .unwrap(),
                ),
                [0_u8; 32],
            ),
        ),
    );
    assert_eq!(
        result.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::PreStateRootMismatch {
            expected: hex32(
                ambiguity["last_mint_timestamp_7_state_root_v5"]
                    .as_str()
                    .unwrap()
            ),
            actual: hex32(ambiguity["empty_duration_state_root_v5"].as_str().unwrap()),
        }
    );
}

#[test]
fn wrong_pre_and_wrong_post_roots_reject_independently() {
    let document = fixture();
    let pre = snapshot(&document, "pre_state");
    let post = snapshot(&document, "post_state");
    let nonces = pre_nonces(&document);
    let sender = document["sender_pubkey"].as_str().unwrap();
    let mut wrong_pre = hex32(document["expected"]["pre_state_root_v5"].as_str().unwrap());
    wrong_pre[0] ^= 1;
    let pre_result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            sender,
            7,
            expected_source(&document),
            ExpectedSpotStateRootsV5::new(
                wrong_pre,
                hex32(document["expected"]["post_state_root_v5"].as_str().unwrap()),
            ),
        ),
    );
    assert!(matches!(
        pre_result,
        Err(RestrictedSpotStateRootV5BridgeError::PreStateRootMismatch { .. })
    ));

    let mut wrong_post = hex32(document["expected"]["post_state_root_v5"].as_str().unwrap());
    wrong_post[0] ^= 1;
    let post_result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            sender,
            7,
            expected_source(&document),
            ExpectedSpotStateRootsV5::new(
                hex32(document["expected"]["pre_state_root_v5"].as_str().unwrap()),
                wrong_post,
            ),
        ),
    );
    assert!(matches!(
        post_result,
        Err(RestrictedSpotStateRootV5BridgeError::PostStateRootMismatch { .. })
    ));
}

#[test]
fn wrong_expected_source_commitment_rejects_before_header_binding() {
    let document = fixture();
    let pre = snapshot(&document, "pre_state");
    let post = snapshot(&document, "post_state");
    let nonces = pre_nonces(&document);
    let expected = &document["expected"];
    let mut wrong_pre_app = hex32(expected["source_pre_app_hash"].as_str().unwrap());
    wrong_pre_app[0] ^= 1;
    let result = verify_restricted_spot_state_root_v5_transition_v1(
        RestrictedSpotStateRootV5ProfileV1::governed(),
        RestrictedSpotStateRootV5TransitionInputV1::new(
            &pre,
            &post,
            &nonces,
            document["sender_pubkey"].as_str().unwrap(),
            7,
            ExpectedLegacySpotCommitmentsV1::new(
                wrong_pre_app,
                hex32(expected["source_post_app_hash"].as_str().unwrap()),
                hex32(expected["source_pre_nonce_root"].as_str().unwrap()),
                hex32(expected["source_post_nonce_root"].as_str().unwrap()),
            ),
            expected_roots(&document),
        ),
    );
    assert_eq!(
        result.unwrap_err(),
        RestrictedSpotStateRootV5BridgeError::SourcePreAppHashMismatch
    );
}
