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
// Pairwise-distinct non-palindromic lengths actively witness field order and
// big-endian length encoding across the Python/Rust boundary.
const V7_RECEIPT_BYTES: usize = 603;
const GUEST_INPUT_BYTES: usize = 607;
const V6_RECEIPT_BYTES: usize = 611;
const CANONICAL_MANIFEST_SHA256_HEX: &str =
    "228938334def692fb13e58c69c80e632e7291144eec106f338744a842a6d8a39";

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

    assert_eq!(v7_receipt.len(), V7_RECEIPT_BYTES);
    assert_eq!(guest_input.len(), GUEST_INPUT_BYTES);
    assert_eq!(v6_receipt.len(), V6_RECEIPT_BYTES);
    assert!(!is_palindrome(&v7_receipt));
    assert!(!is_palindrome(&guest_input));
    assert!(!is_palindrome(&v6_receipt));
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
    assert_eq!(manifest.sha256(), sha256(&encoded));
    assert_eq!(
        hex::encode(manifest.sha256()),
        CANONICAL_MANIFEST_SHA256_HEX
    );
    assert_eq!(
        manifest.validate_artifacts(&v7_receipt, &guest_input, &v6_receipt),
        Ok(())
    );
}

#[test]
fn exact_layout_distinguishes_every_field_position_and_byte_order() {
    let (v7_receipt, guest_input, v6_receipt) = artifacts();
    let encoded = manifest().encode();
    let v7_receipt_sha256 = sha256(&v7_receipt);
    let guest_input_sha256 = sha256(&guest_input);
    let v6_receipt_sha256 = sha256(&v6_receipt);

    assert_eq!(&encoded[0..8], b"ZSV7AIM1");
    assert_eq!(&encoded[8..10], &1_u16.to_be_bytes());
    assert_eq!(&encoded[10..12], &256_u16.to_be_bytes());
    assert_eq!(&encoded[12..16], &[0_u8; 4]);
    assert_eq!(
        &encoded[16..48],
        &SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1
    );
    assert_eq!(
        &encoded[48..80],
        &SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    );
    assert_image_words(&encoded, 80, V7_IMAGE_ID);
    assert_image_words(&encoded, 112, V6_IMAGE_ID);
    assert_eq!(
        &encoded[144..148],
        &u32::try_from(V7_RECEIPT_BYTES)
            .expect("fixture length fits u32")
            .to_be_bytes()
    );
    assert_eq!(&encoded[148..180], &v7_receipt_sha256);
    assert_eq!(
        &encoded[180..184],
        &u32::try_from(GUEST_INPUT_BYTES)
            .expect("fixture length fits u32")
            .to_be_bytes()
    );
    assert_eq!(&encoded[184..216], &guest_input_sha256);
    assert_eq!(
        &encoded[216..220],
        &u32::try_from(V6_RECEIPT_BYTES)
            .expect("fixture length fits u32")
            .to_be_bytes()
    );
    assert_eq!(&encoded[220..252], &v6_receipt_sha256);
    assert_eq!(&encoded[252..256], &[0_u8; 4]);
}

#[test]
fn every_guarded_header_and_flag_choice_rejects() {
    let encoded = manifest().encode();
    for (range, error) in [
        (0..8, SpotV7FirecrackerAuthorityInputErrorV1::ManifestMagic),
        (
            8..12,
            SpotV7FirecrackerAuthorityInputErrorV1::ManifestVersion,
        ),
        (
            16..48,
            SpotV7FirecrackerAuthorityInputErrorV1::ManifestProfile,
        ),
        (
            48..80,
            SpotV7FirecrackerAuthorityInputErrorV1::ManifestRuntimeProfile,
        ),
    ] {
        for offset in range {
            assert_decode_error(xor_byte(encoded, offset), error);
        }
    }

    for bit in 0..32 {
        let mut mutated = encoded;
        mutated[12..16].copy_from_slice(&(1_u32 << bit).to_be_bytes());
        assert_decode_error(
            mutated,
            SpotV7FirecrackerAuthorityInputErrorV1::ManifestFlags,
        );
    }
    for bit in 0..32 {
        let mut mutated = encoded;
        mutated[252 + bit / 8] = 1_u8 << (bit % 8);
        assert_decode_error(
            mutated,
            SpotV7FirecrackerAuthorityInputErrorV1::ManifestReserved,
        );
    }
}

#[test]
fn every_bound_field_byte_changes_identity_or_rejects() {
    let authority_manifest = manifest();
    let encoded = authority_manifest.encode();
    let original_sha256 = authority_manifest.sha256();
    let (v7_receipt, guest_input, v6_receipt) = artifacts();

    for offset in 80..112 {
        let mutated = xor_byte(encoded, offset);
        assert_ne!(sha256(&mutated), original_sha256);
        let decoded = SpotV7FirecrackerAuthorityInputManifestV1::decode(&mutated)
            .expect("one-byte image mutation remains structurally valid");
        assert_eq!(
            decoded.require_governed_image_ids(V7_IMAGE_ID, V6_IMAGE_ID),
            Err(SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdMismatch)
        );
    }
    for offset in 112..144 {
        let mutated = xor_byte(encoded, offset);
        assert_ne!(sha256(&mutated), original_sha256);
        let decoded = SpotV7FirecrackerAuthorityInputManifestV1::decode(&mutated)
            .expect("one-byte image mutation remains structurally valid");
        assert_eq!(
            decoded.require_governed_image_ids(V7_IMAGE_ID, V6_IMAGE_ID),
            Err(SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdMismatch)
        );
    }

    for (start, length_error, binding_error) in [
        (
            144,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptLength,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptBinding,
        ),
        (
            180,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputLength,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
        ),
        (
            216,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptLength,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptBinding,
        ),
    ] {
        for offset in start..start + 4 {
            let mutated = xor_byte(encoded, offset);
            assert_ne!(sha256(&mutated), original_sha256);
            match SpotV7FirecrackerAuthorityInputManifestV1::decode(&mutated) {
                Err(actual) => assert_eq!(actual, length_error),
                Ok(decoded) => assert_eq!(
                    decoded.validate_artifacts(&v7_receipt, &guest_input, &v6_receipt),
                    Err(binding_error)
                ),
            }
        }
    }

    for (range, binding_error) in [
        (
            148..180,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptBinding,
        ),
        (
            184..216,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
        ),
        (
            220..252,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptBinding,
        ),
    ] {
        for offset in range {
            let mutated = xor_byte(encoded, offset);
            assert_ne!(sha256(&mutated), original_sha256);
            let decoded = SpotV7FirecrackerAuthorityInputManifestV1::decode(&mutated)
                .expect("one-byte digest mutation remains structurally valid");
            assert_eq!(
                decoded.validate_artifacts(&v7_receipt, &guest_input, &v6_receipt),
                Err(binding_error)
            );
        }
    }
}

#[test]
fn all_multibyte_fields_actively_distinguish_byte_order() {
    let encoded = manifest().encode();
    let original_sha256 = sha256(&encoded);
    let (v7_receipt, guest_input, v6_receipt) = artifacts();

    for start in [8, 10] {
        assert_decode_error(
            reverse_field(encoded, start, 2),
            SpotV7FirecrackerAuthorityInputErrorV1::ManifestVersion,
        );
    }
    for (start, error) in [
        (144, SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptLength),
        (
            180,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputLength,
        ),
        (216, SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptLength),
    ] {
        assert_decode_error(reverse_field(encoded, start, 4), error);
    }

    for (start, governed_error) in [
        (
            80,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdMismatch,
        ),
        (
            112,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdMismatch,
        ),
    ] {
        for index in 0..8 {
            let mutated = reverse_field(encoded, start + index * 4, 4);
            assert_ne!(sha256(&mutated), original_sha256);
            let decoded = SpotV7FirecrackerAuthorityInputManifestV1::decode(&mutated)
                .expect("reversed non-palindromic image word remains structurally valid");
            assert_eq!(
                decoded.require_governed_image_ids(V7_IMAGE_ID, V6_IMAGE_ID),
                Err(governed_error)
            );
        }
    }

    for (start, binding_error) in [
        (
            148,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptBinding,
        ),
        (
            184,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
        ),
        (
            220,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptBinding,
        ),
    ] {
        let mutated = reverse_field(encoded, start, 32);
        assert_ne!(sha256(&mutated), original_sha256);
        let decoded = SpotV7FirecrackerAuthorityInputManifestV1::decode(&mutated)
            .expect("reversed non-palindromic digest remains structurally valid");
        assert_eq!(
            decoded.validate_artifacts(&v7_receipt, &guest_input, &v6_receipt),
            Err(binding_error)
        );
    }
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
        distinguishing_artifact(V7_RECEIPT_BYTES, 8),
        distinguishing_artifact(GUEST_INPUT_BYTES, 30),
        distinguishing_artifact(V6_RECEIPT_BYTES, 54),
    )
}

fn distinguishing_artifact(length: usize, start: u8) -> Vec<u8> {
    let mut output = Vec::with_capacity(length);
    let mut value = start;
    for _ in 0..length {
        output.push(value);
        value = if value == 251 { 1 } else { value + 1 };
    }
    output
}

fn is_palindrome(bytes: &[u8]) -> bool {
    bytes.iter().eq(bytes.iter().rev())
}

fn assert_image_words(encoded: &[u8], start: usize, image_id: [u32; 8]) {
    for (index, word) in image_id.into_iter().enumerate() {
        let word_start = start + index * 4;
        let raw = &encoded[word_start..word_start + 4];
        assert_eq!(raw, &word.to_le_bytes());
        assert!(!is_palindrome(raw));
    }
}

fn assert_decode_error(
    encoded: [u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1],
    expected: SpotV7FirecrackerAuthorityInputErrorV1,
) {
    assert_eq!(
        SpotV7FirecrackerAuthorityInputManifestV1::decode(&encoded),
        Err(expected)
    );
}

fn xor_byte(
    mut encoded: [u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1],
    offset: usize,
) -> [u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1] {
    encoded[offset] ^= 1;
    encoded
}

fn reverse_field(
    mut encoded: [u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1],
    start: usize,
    length: usize,
) -> [u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1] {
    encoded[start..start + length].reverse();
    encoded
}

fn one_bit_mutation(bytes: &[u8]) -> Vec<u8> {
    let mut mutated = bytes.to_vec();
    let index = mutated.len() / 2;
    mutated[index] ^= 1;
    mutated
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
