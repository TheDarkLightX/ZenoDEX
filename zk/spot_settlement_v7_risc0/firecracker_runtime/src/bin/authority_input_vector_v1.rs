use zenodex_zrpf_spot_v7_firecracker_runtime::{
    SpotV7FirecrackerAuthorityInputErrorV1, SpotV7FirecrackerAuthorityInputManifestV1,
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
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

fn main() -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
    let v7_receipt = distinguishing_artifact(V7_RECEIPT_BYTES, 8);
    let guest_input = distinguishing_artifact(GUEST_INPUT_BYTES, 30);
    let v6_receipt = distinguishing_artifact(V6_RECEIPT_BYTES, 54);
    let manifest = SpotV7FirecrackerAuthorityInputManifestV1::new(
        V7_IMAGE_ID,
        V6_IMAGE_ID,
        &v7_receipt,
        &guest_input,
        &v6_receipt,
    )?;
    println!("manifest_hex={}", hex::encode(manifest.encode()));
    println!("manifest_sha256={}", hex::encode(manifest.sha256()));
    println!(
        "profile_sha256={}",
        hex::encode(SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1)
    );
    Ok(())
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
