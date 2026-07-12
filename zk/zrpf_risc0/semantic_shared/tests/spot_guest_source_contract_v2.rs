const GUEST_SOURCE: &str = include_str!("../../methods/ordinary_spot_settlement/src/main.rs");
const GUEST_INPUT_CODEC: &str = include_str!("../src/spot_certificate_v1/guest_input_v2/codec.rs");
const WORKSPACE_MANIFEST: &str = include_str!("../../Cargo.toml");
const METHODS_MANIFEST: &str = include_str!("../../methods/Cargo.toml");
const METHODS_BUILD: &str = include_str!("../../methods/build.rs");
const SETTLEMENT_MANIFEST: &str = include_str!("../../methods/ordinary_spot_settlement/Cargo.toml");

#[test]
fn guest_verifies_exact_l2_proposal_before_claim_derivation_or_interpretation() {
    let authenticate_start = GUEST_SOURCE
        .find(concat!("pub(super) f", "n authenticate("))
        .expect("receipt-verified constructor");
    let compose_start = GUEST_SOURCE[authenticate_start..]
        .find(concat!("pub(super) f", "n compose("))
        .map(|offset| authenticate_start + offset)
        .expect("receipt-verified compose");
    let authenticate = &GUEST_SOURCE[authenticate_start..compose_start];
    let markers = [
        "env::verify(",
        "derive_risc0_verified_claim_binding_v1(",
        "bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2(",
        "Self {",
    ];
    let positions = markers.map(|marker| authenticate.find(marker).expect(marker));

    assert_eq!(positions, {
        let mut sorted = positions;
        sorted.sort_unstable();
        sorted
    });
    assert!(authenticate.contains("PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5"));
    assert!(authenticate.contains("envelope.proposal_bytes()"));
    assert!(!authenticate.contains("decode_exact_value_aggregate_proposal_v5"));
    assert_eq!(GUEST_SOURCE.matches("env::verify(").count(), 1);
}

#[test]
fn guest_commits_only_canonical_bounded_settlement_certificate_bytes() {
    let main_start = GUEST_SOURCE
        .find(concat!("pub f", "n main()"))
        .expect("guest main");
    let main_end = GUEST_SOURCE[main_start..]
        .find(concat!("f", "n read_bounded_input()"))
        .map(|offset| main_start + offset)
        .expect("bounded reader");
    let main = &GUEST_SOURCE[main_start..main_end];
    let markers = [
        "decode_exact_ordinary_spot_settlement_guest_envelope_v2(&input_bytes)",
        "ReceiptVerifiedSpotSettlementInputV2::authenticate(envelope)",
        "verified.compose()",
        "env::commit_slice(&certificate_bytes)",
    ];
    let positions = markers.map(|marker| main.find(marker).expect(marker));

    assert_eq!(positions, {
        let mut sorted = positions;
        sorted.sort_unstable();
        sorted
    });
    assert!(GUEST_SOURCE.contains("MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 == 74_678"));
    assert!(GUEST_SOURCE.contains("MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 == 1_024"));
    for forbidden in [
        "expected_self_image_id",
        "receipt_valid",
        "settlement_guest_image_id",
        "settlement_authority",
    ] {
        assert!(!GUEST_SOURCE.contains(forbidden));
    }
}

#[test]
fn proposal_opaque_decoder_contains_no_v5_proposal_interpretation() {
    let opaque_start = GUEST_INPUT_CODEC
        .find("pub fn decode_exact_ordinary_spot_settlement_guest_envelope_v2(")
        .expect("opaque decoder");
    let validated_start = GUEST_INPUT_CODEC[opaque_start..]
        .find("pub fn decode_exact_ordinary_spot_settlement_guest_input_v2(")
        .map(|offset| opaque_start + offset)
        .expect("validated decoder");
    let opaque = &GUEST_INPUT_CODEC[opaque_start..validated_start];
    let validated = &GUEST_INPUT_CODEC[validated_start..];

    assert!(opaque.contains("decode_envelope_parts(bytes)?"));
    assert!(!opaque.contains("decode_exact_value_aggregate_proposal_v5"));
    assert!(!GUEST_INPUT_CODEC.contains("decode_exact_value_aggregate_proposal_v5"));
    assert!(validated.contains("decode_exact_ordinary_spot_settlement_guest_envelope_v2(bytes)?"));
    assert!(validated.contains("envelope.into_validated()"));
}

#[test]
fn settlement_method_and_root_policy_are_registered_fail_closed() {
    assert!(WORKSPACE_MANIFEST.contains("\"value_aggregate_root_policy\""));
    assert!(WORKSPACE_MANIFEST.contains("\"methods/ordinary_spot_settlement\""));
    assert!(METHODS_MANIFEST.contains("\"ordinary_spot_settlement\""));
    assert!(SETTLEMENT_MANIFEST.contains("zenodex-zrpf-risc0-value-aggregate-root-policy"));
    assert!(METHODS_BUILD
        .contains("pub const ZENODEX_ZRPF_RISC0_ORDINARY_SPOT_SETTLEMENT_ELF: &[u8] = &[];"));
    assert!(METHODS_BUILD
        .contains("pub const ZENODEX_ZRPF_RISC0_ORDINARY_SPOT_SETTLEMENT_ID: [u32; 8] = [0; 8];"));
}
