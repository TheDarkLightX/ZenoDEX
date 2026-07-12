use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, NodeLevelV3, ProfileIdV3};
use zenodex_zrpf_risc0_value_aggregate_root_policy::{
    pinned_value_aggregate_level_two_root_identity_v5,
    value_aggregate_level_two_root_manifest_root_v5, value_aggregate_level_two_root_profile_id_v5,
    PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
};

const PINNED_L2_IMAGE_HEX: [u8; 32] = [
    0x49, 0xc9, 0x4d, 0xc5, 0x61, 0x8c, 0x5e, 0x82, 0x37, 0x22, 0x65, 0xcc, 0x75, 0xee, 0x77, 0xd0,
    0x98, 0x5d, 0x9a, 0xb1, 0xb7, 0xb2, 0x23, 0xf0, 0x36, 0xe5, 0x13, 0x87, 0x0d, 0x67, 0x42, 0xf8,
];

fn hash_framed(domain: &[u8], fields: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    for field in fields {
        hasher.update(u32::try_from(field.len()).unwrap().to_be_bytes());
        hasher.update(field);
    }
    hasher.finalize().into()
}

#[test]
fn pinned_image_words_are_the_reviewed_cycle_free_l2_digest() {
    let mut decoded = [0u8; 32];
    for (chunk, word) in decoded
        .chunks_exact_mut(4)
        .zip(PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    assert_eq!(decoded, PINNED_L2_IMAGE_HEX);
}

#[test]
fn governed_l2_root_profile_and_manifest_match_independent_derivation() {
    let expected_profile = ProfileIdV3::new(hash_framed(
        b"zenodex.zrpf.profile_id.v3",
        &[b"zrpf_value_aggregate_level_two_root_v5"],
    ))
    .unwrap();
    let identity = pinned_value_aggregate_level_two_root_identity_v5().unwrap();
    let expected_manifest = CommitmentV3::new(hash_framed(
        b"zenodex.zrpf.value_aggregate_l2_root_manifest.v5",
        &[
            identity.expected_program_id().as_bytes(),
            expected_profile.as_bytes(),
            b"experimental_bounded_value_aggregate_level_two_root_v5",
        ],
    ))
    .unwrap();

    assert_eq!(identity.aggregate_level(), NodeLevelV3::new(2).unwrap());
    assert_eq!(
        identity.expected_image_id(),
        PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5
    );
    assert_eq!(
        identity.expected_program_id().as_bytes(),
        &PINNED_L2_IMAGE_HEX
    );
    assert_eq!(identity.expected_profile_id(), expected_profile);
    assert_eq!(identity.expected_manifest_root(), expected_manifest);
    assert_eq!(
        value_aggregate_level_two_root_profile_id_v5().unwrap(),
        expected_profile
    );
    assert_eq!(
        value_aggregate_level_two_root_manifest_root_v5(identity.expected_program_id()).unwrap(),
        expected_manifest
    );
}

#[test]
fn root_manifest_is_program_specific_and_source_grants_no_authority_flag() {
    let identity = pinned_value_aggregate_level_two_root_identity_v5().unwrap();
    let mut changed_words = PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5;
    changed_words[0] ^= 1;
    let changed_program =
        zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3(changed_words).unwrap();
    assert_ne!(
        value_aggregate_level_two_root_manifest_root_v5(changed_program).unwrap(),
        identity.expected_manifest_root()
    );

    let source = include_str!("../src/lib.rs");
    for forbidden in [
        "data_availability_verified",
        "ledger_admission_authority",
        "settlement_authority",
        "release_authority",
        "production_authority",
    ] {
        assert!(!source.contains(forbidden));
    }
}
