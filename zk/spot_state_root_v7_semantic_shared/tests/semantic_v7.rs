use serde_json::Value;
use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{DexSnapshotV1, OracleV1, VaultV1};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    ExpectedLegacySpotCommitmentsV1, RestrictedSpotStateRootV5BridgeError,
};
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1,
    decode_exact_bounded_spot_state_root_v7_host_input_v1,
    decode_exact_spot_state_root_v7_semantic_journal_v1,
    encode_bounded_spot_state_root_v7_host_input_v1, encode_spot_state_root_v7_semantic_journal_v1,
    BoundedSpotStateRootV7HostInputV1, LegacySpotSourceProjectionV7,
    SpotStateRootV7SemanticErrorV1, MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1,
    SPOT_STATE_ROOT_V7_RECEIPT_AUTHORITY, SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1,
    SPOT_STATE_ROOT_V7_SETTLEMENT_AUTHORITY, SPOT_STATE_ROOT_V7_SOURCE_AUTHENTICATION_VERIFIED,
};

const V5_FIXTURE_BYTES: &str =
    include_str!("../../../tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json");
const V7_FIXTURE_BYTES: &str =
    include_str!("../../../tests/fixtures/zrpf_spot_state_root_v7_semantic_v1.json");

fn fixture(bytes: &str) -> Value {
    serde_json::from_str(bytes).unwrap()
}

fn snapshot(document: &Value, field: &str) -> DexSnapshotV1 {
    serde_json::from_value(document[field].clone()).unwrap()
}

fn hex32(value: &str) -> [u8; 32] {
    decode_hex(value).try_into().unwrap()
}

fn decode_hex(value: &str) -> Vec<u8> {
    let body = value.strip_prefix("0x").unwrap();
    assert_eq!(body.len() % 2, 0);
    body.as_bytes()
        .chunks_exact(2)
        .map(|pair| (nibble(pair[0]) << 4) | nibble(pair[1]))
        .collect()
}

fn nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => panic!("fixture contains noncanonical hex"),
    }
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

fn host_input(document: &Value) -> BoundedSpotStateRootV7HostInputV1 {
    BoundedSpotStateRootV7HostInputV1::new(
        snapshot(document, "post_state"),
        hex32(document["expected"]["pre_state_root_v5"].as_str().unwrap()),
        hex32(document["expected"]["post_state_root_v5"].as_str().unwrap()),
    )
    .unwrap()
}

#[test]
fn exact_host_and_journal_vectors_roundtrip_and_compose() {
    let v5 = fixture(V5_FIXTURE_BYTES);
    let v7 = fixture(V7_FIXTURE_BYTES);
    let host = host_input(&v5);
    let host_bytes = encode_bounded_spot_state_root_v7_host_input_v1(&host).unwrap();
    assert_eq!(
        host_bytes,
        decode_hex(v7["host_input_hex"].as_str().unwrap())
    );
    assert_eq!(
        host_bytes.len(),
        v7["host_input_bytes"].as_u64().unwrap() as usize
    );
    assert_eq!(
        Sha256::digest(&host_bytes).to_vec(),
        decode_hex(v7["host_input_sha256"].as_str().unwrap())
    );
    let decoded_host = decode_exact_bounded_spot_state_root_v7_host_input_v1(&host_bytes).unwrap();
    assert_eq!(
        encode_bounded_spot_state_root_v7_host_input_v1(&decoded_host).unwrap(),
        host_bytes
    );

    let pre = snapshot(&v5, "pre_state");
    let source = LegacySpotSourceProjectionV7::new(
        &pre,
        v5["sender_pubkey"].as_str().unwrap(),
        v5["ingress_nonce"].as_u64().unwrap(),
        expected_source(&v5),
    );
    let journal = compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
        &source,
        &decoded_host,
    )
    .unwrap();
    let journal_bytes = encode_spot_state_root_v7_semantic_journal_v1(&journal);
    assert_eq!(
        journal_bytes,
        decode_hex(v7["journal_hex"].as_str().unwrap())
    );
    assert_eq!(
        journal_bytes.len(),
        v7["journal_bytes"].as_u64().unwrap() as usize
    );
    assert_eq!(
        Sha256::digest(&journal_bytes).to_vec(),
        decode_hex(v7["journal_sha256"].as_str().unwrap())
    );
    assert_eq!(
        decode_exact_spot_state_root_v7_semantic_journal_v1(&journal_bytes).unwrap(),
        journal
    );
    assert_eq!(journal.ingress_nonce(), 7);
}

#[test]
fn host_encoding_canonicalizes_order_and_omits_fixed_profile_fields() {
    let v5 = fixture(V5_FIXTURE_BYTES);
    let canonical = encode_bounded_spot_state_root_v7_host_input_v1(&host_input(&v5)).unwrap();
    let mut reordered = snapshot(&v5, "post_state");
    reordered.balances.reverse();
    let reordered = BoundedSpotStateRootV7HostInputV1::new(
        reordered,
        hex32(v5["expected"]["pre_state_root_v5"].as_str().unwrap()),
        hex32(v5["expected"]["post_state_root_v5"].as_str().unwrap()),
    )
    .unwrap();
    assert_eq!(
        encode_bounded_spot_state_root_v7_host_input_v1(&reordered).unwrap(),
        canonical
    );

    let mut unsupported_version = snapshot(&v5, "post_state");
    unsupported_version.version = 2;
    assert!(matches!(
        BoundedSpotStateRootV7HostInputV1::new(unsupported_version, [1; 32], [2; 32]),
        Err(SpotStateRootV7SemanticErrorV1::UnsupportedSnapshotVersion)
    ));

    let mut unsupported_status = snapshot(&v5, "post_state");
    unsupported_status.pools[0].status = "FROZEN".into();
    assert!(matches!(
        BoundedSpotStateRootV7HostInputV1::new(unsupported_status, [1; 32], [2; 32]),
        Err(SpotStateRootV7SemanticErrorV1::UnsupportedPoolStatus)
    ));

    let mut vault = snapshot(&v5, "post_state");
    vault.vault = Some(VaultV1 {
        acc_reward_per_share: 0,
        last_update_acc: 0,
        pending_rewards: 0,
        reward_balance: 0,
        staked_lp_shares: 0,
    });
    assert!(matches!(
        BoundedSpotStateRootV7HostInputV1::new(vault, [1; 32], [2; 32]),
        Err(SpotStateRootV7SemanticErrorV1::VaultStatePresent)
    ));

    let mut oracle = snapshot(&v5, "post_state");
    oracle.oracle = Some(OracleV1 {
        max_staleness_seconds: 0,
        price_timestamp: 0,
    });
    assert!(matches!(
        BoundedSpotStateRootV7HostInputV1::new(oracle, [1; 32], [2; 32]),
        Err(SpotStateRootV7SemanticErrorV1::OracleStatePresent)
    ));
}

#[test]
fn exact_host_decoder_rejects_prefix_trailing_version_count_and_order_mutations() {
    let v5 = fixture(V5_FIXTURE_BYTES);
    let encoded = encode_bounded_spot_state_root_v7_host_input_v1(&host_input(&v5)).unwrap();
    for end in 0..encoded.len() {
        assert!(decode_exact_bounded_spot_state_root_v7_host_input_v1(&encoded[..end]).is_err());
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_bounded_spot_state_root_v7_host_input_v1(&trailing).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::TrailingBytes
    );
    let mut version = encoded.clone();
    version[1] = 2;
    assert_eq!(
        decode_exact_bounded_spot_state_root_v7_host_input_v1(&version).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::InvalidVersion(2)
    );
    let mut excessive_count = encoded.clone();
    excessive_count[2..6].copy_from_slice(&16_385_u32.to_be_bytes());
    assert!(matches!(
        decode_exact_bounded_spot_state_root_v7_host_input_v1(&excessive_count),
        Err(SpotStateRootV7SemanticErrorV1::CountTooLarge {
            section: "balances",
            actual: 16_385,
            maximum: 16_384,
        })
    ));

    let first_balance_offset = 2 + 4;
    let second_balance_offset = first_balance_offset + 96;
    let mut reordered = encoded.clone();
    let first = reordered[first_balance_offset..second_balance_offset].to_vec();
    let second = reordered[second_balance_offset..second_balance_offset + 96].to_vec();
    reordered[first_balance_offset..second_balance_offset].copy_from_slice(&second);
    reordered[second_balance_offset..second_balance_offset + 96].copy_from_slice(&first);
    assert_eq!(
        decode_exact_bounded_spot_state_root_v7_host_input_v1(&reordered).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::NonCanonicalOrder("balances")
    );

    let too_large = vec![0; MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1 + 1];
    assert!(matches!(
        decode_exact_bounded_spot_state_root_v7_host_input_v1(&too_large),
        Err(SpotStateRootV7SemanticErrorV1::InputTooLarge { .. })
    ));
}

#[test]
fn kernel_rejects_wrong_source_header_and_implicit_cpmm_commitments() {
    let v5 = fixture(V5_FIXTURE_BYTES);
    let pre = snapshot(&v5, "pre_state");
    let expected = &v5["expected"];
    let mut wrong_post_app = hex32(expected["source_post_app_hash"].as_str().unwrap());
    wrong_post_app[0] ^= 1;
    let wrong_source = LegacySpotSourceProjectionV7::new(
        &pre,
        v5["sender_pubkey"].as_str().unwrap(),
        7,
        ExpectedLegacySpotCommitmentsV1::new(
            hex32(expected["source_pre_app_hash"].as_str().unwrap()),
            wrong_post_app,
            hex32(expected["source_pre_nonce_root"].as_str().unwrap()),
            hex32(expected["source_post_nonce_root"].as_str().unwrap()),
        ),
    );
    assert_eq!(
        compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
            &wrong_source,
            &host_input(&v5),
        )
        .unwrap_err(),
        SpotStateRootV7SemanticErrorV1::Bridge(
            RestrictedSpotStateRootV5BridgeError::SourcePostAppHashMismatch
        )
    );

    let source = LegacySpotSourceProjectionV7::new(
        &pre,
        v5["sender_pubkey"].as_str().unwrap(),
        7,
        expected_source(&v5),
    );
    let mut wrong_pre_root = hex32(expected["pre_state_root_v5"].as_str().unwrap());
    wrong_pre_root[0] ^= 1;
    let wrong_header = BoundedSpotStateRootV7HostInputV1::new(
        snapshot(&v5, "post_state"),
        wrong_pre_root,
        hex32(expected["post_state_root_v5"].as_str().unwrap()),
    )
    .unwrap();
    assert!(matches!(
        compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
            &source,
            &wrong_header,
        ),
        Err(SpotStateRootV7SemanticErrorV1::Bridge(
            RestrictedSpotStateRootV5BridgeError::PreStateRootMismatch { .. }
        ))
    ));

    let mut wrong_post_root = hex32(expected["post_state_root_v5"].as_str().unwrap());
    wrong_post_root[0] ^= 1;
    let wrong_post_header = BoundedSpotStateRootV7HostInputV1::new(
        snapshot(&v5, "post_state"),
        hex32(expected["pre_state_root_v5"].as_str().unwrap()),
        wrong_post_root,
    )
    .unwrap();
    assert!(matches!(
        compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
            &source,
            &wrong_post_header,
        ),
        Err(SpotStateRootV7SemanticErrorV1::Bridge(
            RestrictedSpotStateRootV5BridgeError::PostStateRootMismatch { .. }
        ))
    ));

    let mut wrong_pool = snapshot(&v5, "post_state");
    wrong_pool.pools[0].pool_id = format!("0x{}", "dd".repeat(32));
    let wrong_pool = BoundedSpotStateRootV7HostInputV1::new(
        wrong_pool,
        hex32(expected["pre_state_root_v5"].as_str().unwrap()),
        hex32(expected["post_state_root_v5"].as_str().unwrap()),
    )
    .unwrap();
    assert_eq!(
        compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
            &source,
            &wrong_pool,
        )
        .unwrap_err(),
        SpotStateRootV7SemanticErrorV1::Bridge(
            RestrictedSpotStateRootV5BridgeError::PoolIdentityMismatch
        )
    );
}

#[test]
fn journal_decoder_is_exact_profile_bound_and_authority_neutral() {
    let v7 = fixture(V7_FIXTURE_BYTES);
    let encoded = decode_hex(v7["journal_hex"].as_str().unwrap());
    assert_eq!(encoded.len(), SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1);
    for end in 0..encoded.len() {
        assert!(decode_exact_spot_state_root_v7_semantic_journal_v1(&encoded[..end]).is_err());
    }
    let mut profile = encoded.clone();
    profile[2] ^= 1;
    assert_eq!(
        decode_exact_spot_state_root_v7_semantic_journal_v1(&profile).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::UnexpectedProfileId
    );
    let mut scheme = encoded.clone();
    scheme[34] ^= 1;
    assert_eq!(
        decode_exact_spot_state_root_v7_semantic_journal_v1(&scheme).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::UnexpectedStateRootSchemeId
    );
    let mut zero_nonce = encoded.clone();
    let end = zero_nonce.len();
    zero_nonce[end - 4..].fill(0);
    assert_eq!(
        decode_exact_spot_state_root_v7_semantic_journal_v1(&zero_nonce).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::IngressNonceZero
    );
    let mut trailing = encoded;
    trailing.push(0);
    assert_eq!(
        decode_exact_spot_state_root_v7_semantic_journal_v1(&trailing).unwrap_err(),
        SpotStateRootV7SemanticErrorV1::TrailingBytes
    );

    let fixture_boundary = &v7["claim_boundary"];
    assert_eq!(
        (
            SPOT_STATE_ROOT_V7_SOURCE_AUTHENTICATION_VERIFIED,
            SPOT_STATE_ROOT_V7_RECEIPT_AUTHORITY,
            SPOT_STATE_ROOT_V7_SETTLEMENT_AUTHORITY,
        ),
        (
            fixture_boundary["source_authentication_verified"]
                .as_bool()
                .unwrap(),
            fixture_boundary["receipt_authority"].as_bool().unwrap(),
            fixture_boundary["settlement_authority"].as_bool().unwrap(),
        )
    );
    assert_eq!(
        MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1,
        v7["maximum_host_input_bytes"].as_u64().unwrap() as usize
    );
}
