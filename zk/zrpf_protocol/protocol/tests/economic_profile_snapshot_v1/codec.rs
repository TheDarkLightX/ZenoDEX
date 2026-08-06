use serde::Serialize;
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_economic_profile_snapshot_v1, encode_economic_profile_snapshot_v1,
    EconomicProfileIdV1, EconomicProfileSnapshotContentV1, EconomicProfileSnapshotErrorV1,
    EconomicProfileSnapshotV1, EconomicProfileTransitionModeV1,
    ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1, MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1,
};

use super::support::{hex32, profile, profile_id, registry_roots};

#[derive(Serialize)]
struct ProfileWireV1 {
    profile_version: u16,
    profile_id: EconomicProfileIdV1,
    content: EconomicProfileSnapshotContentV1,
}

#[test]
fn exact_codec_roundtrips_with_fixed_digest() {
    // Arrange
    let profile = codec_profile();

    // Act
    let encoded = encode_economic_profile_snapshot_v1(&profile).unwrap();
    let decoded = decode_exact_economic_profile_snapshot_v1(&encoded).unwrap();
    let digest: [u8; 32] = Sha256::digest(&encoded).into();

    // Assert
    assert_eq!(decoded, profile);
    assert_eq!(
        hex32(digest),
        "8ec33e007c885c7964a0bc729d646331901d110d6bad0b9183e3c4445e7843bf"
    );
}

#[test]
fn exact_codec_rejects_stale_counterfeit_nonminimal_trailing_empty_and_oversized_input() {
    // Arrange
    let profile = codec_profile();
    let encoded = encode_economic_profile_snapshot_v1(&profile).unwrap();
    let mut stale = encoded.clone();
    stale[0] = 2;
    let counterfeit = postcard::to_allocvec(&ProfileWireV1 {
        profile_version: ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1,
        profile_id: profile_id(99),
        content: profile.content().clone(),
    })
    .unwrap();
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&encoded[1..]);
    let mut trailing = encoded;
    trailing.push(0);
    let oversized = vec![0; MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1 + 1];

    // Act / Assert
    assert_eq!(
        decode_exact_economic_profile_snapshot_v1(&stale),
        Err(EconomicProfileSnapshotErrorV1::InvalidProfileVersion(2))
    );
    assert_eq!(
        decode_exact_economic_profile_snapshot_v1(&counterfeit),
        Err(EconomicProfileSnapshotErrorV1::CounterfeitProfileId)
    );
    assert_eq!(
        decode_exact_economic_profile_snapshot_v1(&nonminimal),
        Err(EconomicProfileSnapshotErrorV1::NonCanonicalEncoding)
    );
    assert_eq!(
        decode_exact_economic_profile_snapshot_v1(&trailing),
        Err(EconomicProfileSnapshotErrorV1::TrailingBytes)
    );
    assert_eq!(
        decode_exact_economic_profile_snapshot_v1(&[]),
        Err(EconomicProfileSnapshotErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_economic_profile_snapshot_v1(&oversized),
        Err(EconomicProfileSnapshotErrorV1::InputTooLarge {
            actual: MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1 + 1,
            maximum: MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1,
        })
    );
}

#[test]
fn json_decode_rejects_unknown_profile_content_and_registry_root_fields() {
    // Arrange
    let canonical = serde_json::to_value(codec_profile()).unwrap();

    // Act / Assert
    for pointer in ["", "/content", "/content/registry_roots"] {
        let mut mutated = canonical.clone();
        mutated
            .pointer_mut(pointer)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("unknown_profile_field".to_owned(), serde_json::json!(1));
        assert!(serde_json::from_value::<EconomicProfileSnapshotV1>(mutated).is_err());
    }
}

fn codec_profile() -> EconomicProfileSnapshotV1 {
    profile(
        10,
        20,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(profile_id(1)),
        registry_roots(10),
    )
}
