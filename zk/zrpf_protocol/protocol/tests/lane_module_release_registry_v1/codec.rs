use serde::Serialize;
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_lane_module_release_registry_v1, encode_lane_module_release_registry_v1,
    EconomicLaneIdV1, LaneModuleReleaseRegistryErrorV1, LaneModuleReleaseRegistryV1,
    LaneModuleReleaseStatusV1, LaneModuleReleaseV1, LANE_MODULE_RELEASE_REGISTRY_VERSION_V1,
    MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1, MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1,
};

use super::support::{canonical, hex32, registry, release};

#[derive(Serialize)]
struct RegistryWireV1 {
    registry_version: u16,
    lane_id: EconomicLaneIdV1,
    releases: Vec<LaneModuleReleaseV1>,
}

#[test]
fn exact_codec_roundtrips_with_a_fixed_digest() {
    // Arrange
    let registry = codec_registry();

    // Act
    let encoded = encode_lane_module_release_registry_v1(&registry).unwrap();
    let digest: [u8; 32] = Sha256::digest(&encoded).into();
    let decoded = decode_exact_lane_module_release_registry_v1(&encoded).unwrap();

    // Assert
    assert_eq!(decoded, registry);
    assert_eq!(
        hex32(digest),
        "7ed91130146db720c18b7613f29135376e32f06511308c1bded99a52fc14a375"
    );
}

#[test]
fn exact_codec_rejects_stale_trailing_oversized_empty_and_reordered_input() {
    // Arrange
    let registry = codec_registry();
    let encoded = encode_lane_module_release_registry_v1(&registry).unwrap();
    let mut counterfeit_release = encoded.clone();
    counterfeit_release[4] ^= 1;
    let mut stale = encoded.clone();
    stale[0] = 2;
    let mut trailing = encoded;
    trailing.push(0);
    let oversized = vec![0; MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1 + 1];
    let reordered = reordered_bytes(&registry);
    let too_many = too_many_release_bytes();

    // Act / Assert
    assert!(matches!(
        decode_exact_lane_module_release_registry_v1(&stale),
        Err(LaneModuleReleaseRegistryErrorV1::InvalidRegistryVersion(2))
    ));
    assert_eq!(
        decode_exact_lane_module_release_registry_v1(&trailing),
        Err(LaneModuleReleaseRegistryErrorV1::TrailingBytes)
    );
    assert_eq!(
        decode_exact_lane_module_release_registry_v1(&oversized),
        Err(LaneModuleReleaseRegistryErrorV1::InputTooLarge {
            actual: MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1 + 1,
            maximum: MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1,
        })
    );
    assert!(matches!(
        decode_exact_lane_module_release_registry_v1(&reordered),
        Err(LaneModuleReleaseRegistryErrorV1::NonCanonicalReleaseOrder { .. })
    ));
    assert_eq!(
        decode_exact_lane_module_release_registry_v1(&counterfeit_release),
        Err(LaneModuleReleaseRegistryErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_lane_module_release_registry_v1(&too_many),
        Err(LaneModuleReleaseRegistryErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_lane_module_release_registry_v1(&[]),
        Err(LaneModuleReleaseRegistryErrorV1::EmptyInput)
    );
}

fn codec_registry() -> LaneModuleReleaseRegistryV1 {
    registry(vec![
        release(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            LaneModuleReleaseStatusV1::Candidate,
            None,
        ),
        release(
            EconomicLaneIdV1::SpotLiquidity,
            2,
            LaneModuleReleaseStatusV1::ActiveNew,
            None,
        ),
    ])
}

fn reordered_bytes(registry: &LaneModuleReleaseRegistryV1) -> Vec<u8> {
    let mut releases = registry.releases().to_vec();
    releases.reverse();
    postcard::to_allocvec(&RegistryWireV1 {
        registry_version: LANE_MODULE_RELEASE_REGISTRY_VERSION_V1,
        lane_id: registry.lane_id(),
        releases,
    })
    .unwrap()
}

fn too_many_release_bytes() -> Vec<u8> {
    let releases = canonical(
        (1..=u8::try_from(MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1 + 1).unwrap())
            .map(|seed| {
                release(
                    EconomicLaneIdV1::SpotLiquidity,
                    seed,
                    LaneModuleReleaseStatusV1::Candidate,
                    None,
                )
            })
            .collect(),
    );
    postcard::to_allocvec(&RegistryWireV1 {
        registry_version: LANE_MODULE_RELEASE_REGISTRY_VERSION_V1,
        lane_id: EconomicLaneIdV1::SpotLiquidity,
        releases,
    })
    .unwrap()
}
