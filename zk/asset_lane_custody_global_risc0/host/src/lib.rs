//! Bounded exact codec for the fixed custody receipt-verifier endpoint.
//!
//! Decoding establishes only the native receipt encoding. The fixed endpoint
//! separately binds the compiled image, exact journal, receipt kind, and proof.

use risc0_zkvm::Receipt;

pub const MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetLaneCustodyReceiptDecodeErrorV2 {
    InvalidBounds,
    InvalidEncoding,
    NonCanonical,
}

/// Decodes one bounded, exact `serde_json` encoding of a RISC0 receipt.
pub fn decode_canonical_asset_lane_custody_receipt_v2(
    receipt_bytes: &[u8],
) -> Result<Receipt, AssetLaneCustodyReceiptDecodeErrorV2> {
    if !(1..=MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2).contains(&receipt_bytes.len()) {
        return Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds);
    }
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| AssetLaneCustodyReceiptDecodeErrorV2::InvalidEncoding)?;
    let canonical = serde_json::to_vec(&receipt)
        .map_err(|_| AssetLaneCustodyReceiptDecodeErrorV2::InvalidEncoding)?;
    if canonical != receipt_bytes {
        return Err(AssetLaneCustodyReceiptDecodeErrorV2::NonCanonical);
    }
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, InnerReceipt, ReceiptClaim};

    fn fake_receipt_bytes() -> Vec<u8> {
        let receipt: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        serde_json::to_vec(&receipt).unwrap()
    }

    #[test]
    fn canonical_fake_receipt_round_trip_is_encoding_only() {
        let decoded =
            decode_canonical_asset_lane_custody_receipt_v2(&fake_receipt_bytes()).unwrap();

        assert_eq!(decoded.journal.bytes, b"journal");
        assert!(matches!(&decoded.inner, InnerReceipt::Fake(_)));
        assert!(decoded.verify([1; 8]).is_err());
    }

    #[test]
    fn malformed_truncated_and_appended_payloads_reject() {
        let canonical = fake_receipt_bytes();
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(b"malformed"),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidEncoding)
        ));
        assert!(
            decode_canonical_asset_lane_custody_receipt_v2(&canonical[..canonical.len() - 1])
                .is_err()
        );
        let mut appended = canonical;
        appended.extend_from_slice(b"{}");
        assert!(decode_canonical_asset_lane_custody_receipt_v2(&appended).is_err());
    }

    #[test]
    fn equivalent_noncanonical_json_and_unknown_fields_reject() {
        let canonical = fake_receipt_bytes();
        let receipt: Receipt = serde_json::from_slice(&canonical).unwrap();
        let pretty = serde_json::to_vec_pretty(&receipt).unwrap();
        assert_ne!(pretty, canonical);
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(&pretty),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::NonCanonical)
        ));

        let mut with_unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
        with_unknown
            .as_object_mut()
            .unwrap()
            .insert("verified".to_owned(), serde_json::Value::Bool(true));
        assert!(decode_canonical_asset_lane_custody_receipt_v2(
            &serde_json::to_vec(&with_unknown).unwrap()
        )
        .is_err());
    }

    #[test]
    fn receipt_size_bounds_reject_before_json_decoding() {
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(&[]),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds)
        ));
        let oversized = vec![b' '; MAX_ASSET_LANE_CUSTODY_RECEIPT_BYTES_V2 + 1];
        assert!(matches!(
            decode_canonical_asset_lane_custody_receipt_v2(&oversized),
            Err(AssetLaneCustodyReceiptDecodeErrorV2::InvalidBounds)
        ));
    }
}
