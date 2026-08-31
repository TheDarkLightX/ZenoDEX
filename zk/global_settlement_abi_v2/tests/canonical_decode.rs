use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, decode_canonical_v2, AbiErrorV2, AssetTransferCommandV2, RootV2,
    MAX_CANONICAL_INPUT_BYTES_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_asset_transfer_golden.json");

fn command_bytes() -> Vec<u8> {
    let fixture: serde_json::Value = serde_json::from_str(GOLDEN).expect("golden fixture");
    serde_json::to_vec(&fixture["vectors"]["command"]["canonical"])
        .expect("canonical command bytes")
}

#[test]
fn canonical_decoder_rejects_trailing_whitespace_duplicate_fields_and_oversize() {
    let mut whitespace = command_bytes();
    whitespace.push(b'\n');
    assert!(matches!(
        decode_canonical_v2::<AssetTransferCommandV2>(&whitespace),
        Err(AbiErrorV2::CanonicalEncoding(_))
    ));

    let canonical = String::from_utf8(command_bytes()).expect("UTF-8 command");
    let duplicate = canonical.replacen(
        "\"amount_atoms\":25",
        "\"amount_atoms\":25,\"amount_atoms\":25",
        1,
    );
    assert!(matches!(
        decode_canonical_v2::<AssetTransferCommandV2>(duplicate.as_bytes()),
        Err(AbiErrorV2::CanonicalEncoding(_))
    ));

    let oversized = vec![b' '; MAX_CANONICAL_INPUT_BYTES_V2 + 1];
    assert_eq!(
        decode_canonical_v2::<AssetTransferCommandV2>(&oversized),
        Err(AbiErrorV2::InvalidBounds("canonical input bytes"))
    );
}

#[test]
fn canonical_encoder_rejects_floating_point_values() {
    assert!(matches!(
        canonical_bytes_v2(&serde_json::json!({"amount": 1.0})),
        Err(AbiErrorV2::CanonicalEncoding(_))
    ));
}

#[test]
fn root_validation_rejects_ascii_whitespace_disguised_as_hex() {
    let malformed = format!("0x{}  ", "11".repeat(31));
    let root: RootV2 = serde_json::from_value(serde_json::json!(malformed)).expect("root shape");

    assert!(root.validate("test root", true).is_err());
}
