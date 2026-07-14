use zenodex_zrpf_spot_v7_firecracker_runtime::{
    SpotV7FirecrackerAuthorityInputManifestV1,
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

fn main() {
    let manifest = SpotV7FirecrackerAuthorityInputManifestV1::new(
        V7_IMAGE_ID,
        V6_IMAGE_ID,
        b"canonical-v7-succinct-receipt\n",
        b"exact-v7-guest-input\0with-binary",
        b"canonical-v6-child-succinct-receipt\n",
    )
    .expect("fixed vector must be valid");
    println!("manifest_hex={}", hex::encode(manifest.encode()));
    println!("manifest_sha256={}", hex::encode(manifest.sha256()));
    println!(
        "profile_sha256={}",
        hex::encode(SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1)
    );
}
