use sha2::{Digest as _, Sha256};
use zenodex_zrpf_spot_v7_firecracker_runtime::{
    SpotV7FirecrackerAuthorityInputErrorV1, SpotV7FirecrackerAuthorityInputManifestV1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
};

const V7_IMAGE_ID: [u32; 8] = [
    0x0102_0304,
    0x1112_1314,
    0x2122_2324,
    0x3132_3334,
    0x4142_4344,
    0x5152_5354,
    0x6162_6364,
    0x7172_7374,
];
const V6_IMAGE_ID: [u32; 8] = [
    0x8182_8384,
    0x9192_9394,
    0xa1a2_a3a4,
    0xb1b2_b3b4,
    0xc1c2_c3c4,
    0xd1d2_d3d4,
    0xe1e2_e3e4,
    0xf1f2_f3f4,
];

#[test]
fn authority_manifest_is_fixed_canonical_and_profile_bound() {
    let (v7_receipt, guest_input, v6_receipt) = artifacts();
    let manifest = SpotV7FirecrackerAuthorityInputManifestV1::new(
        V7_IMAGE_ID,
        V6_IMAGE_ID,
        &v7_receipt,
        &guest_input,
        &v6_receipt,
    )
    .expect("valid authority manifest");
    let encoded = manifest.encode();

    assert_eq!(
        encoded.len(),
        SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1
    );
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::decode(&encoded),
        Ok(manifest)
    );
    assert_eq!(manifest.v7_image_id(), V7_IMAGE_ID);
    assert_eq!(manifest.v6_image_id(), V6_IMAGE_ID);
    assert_eq!(
        manifest.runtime_profile_sha256(),
        SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    );
    assert_eq!(
        Sha256::digest(SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1).as_slice(),
        SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1
    );
    let encoded_sha256: [u8; 32] = Sha256::digest(encoded).into();
    assert_eq!(manifest.sha256(), encoded_sha256);
    assert_eq!(
        manifest.validate_artifacts(&v7_receipt, &guest_input, &v6_receipt),
        Ok(())
    );
}

#[test]
fn malformed_manifest_bits_reject_at_stable_boundaries() {
    let manifest = manifest();

    let mut magic = manifest.encode();
    magic[0] ^= 1;
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::decode(&magic),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestMagic)
    );

    let mut profile = manifest.encode();
    profile[16] ^= 1;
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::decode(&profile),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestProfile)
    );

    let mut reserved = manifest.encode();
    reserved[255] = 1;
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::decode(&reserved),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestReserved)
    );
}

#[test]
fn wrong_image_and_wrong_child_identity_reject_before_verification() {
    let manifest = manifest();
    let mut wrong_v7 = V7_IMAGE_ID;
    wrong_v7[3] ^= 1;
    assert_eq!(
        manifest.require_governed_image_ids(wrong_v7, V6_IMAGE_ID),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdMismatch)
    );

    let mut wrong_v6 = V6_IMAGE_ID;
    wrong_v6[5] ^= 1;
    assert_eq!(
        manifest.require_governed_image_ids(V7_IMAGE_ID, wrong_v6),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdMismatch)
    );
}

#[test]
fn wrong_input_and_mutated_receipts_reject_exact_hash_binding() {
    let manifest = manifest();
    let (v7_receipt, guest_input, v6_receipt) = artifacts();

    for (expected, actual) in [
        (
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptBinding,
            manifest.validate_artifacts(&one_bit_mutation(&v7_receipt), &guest_input, &v6_receipt),
        ),
        (
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
            manifest.validate_artifacts(&v7_receipt, &one_bit_mutation(&guest_input), &v6_receipt),
        ),
        (
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptBinding,
            manifest.validate_artifacts(&v7_receipt, &guest_input, &one_bit_mutation(&v6_receipt)),
        ),
    ] {
        assert_eq!(actual, Err(expected));
    }
}

#[test]
fn zero_image_identity_cannot_enter_an_authority_manifest() {
    let (v7_receipt, guest_input, v6_receipt) = artifacts();
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::new(
            [0; 8],
            V6_IMAGE_ID,
            &v7_receipt,
            &guest_input,
            &v6_receipt,
        ),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdUnmaterialized)
    );
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::new(
            V7_IMAGE_ID,
            [0; 8],
            &v7_receipt,
            &guest_input,
            &v6_receipt,
        ),
        Err(SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdUnmaterialized)
    );
}

fn manifest() -> SpotV7FirecrackerAuthorityInputManifestV1 {
    let (v7_receipt, guest_input, v6_receipt) = artifacts();
    SpotV7FirecrackerAuthorityInputManifestV1::new(
        V7_IMAGE_ID,
        V6_IMAGE_ID,
        &v7_receipt,
        &guest_input,
        &v6_receipt,
    )
    .expect("valid fixture")
}

fn artifacts() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    (
        b"canonical-v7-succinct-receipt\n".to_vec(),
        b"exact-v7-guest-input\0with-binary".to_vec(),
        b"canonical-v6-child-succinct-receipt\n".to_vec(),
    )
}

fn one_bit_mutation(bytes: &[u8]) -> Vec<u8> {
    let mut mutated = bytes.to_vec();
    let index = mutated.len() / 2;
    mutated[index] ^= 1;
    mutated
}
