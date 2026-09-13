//! Exact receipt transport and verification. No publication authority is issued.

use risc0_zkvm::{InnerReceipt, Receipt};

pub const MAX_MARGIN_RECEIPT_BYTES_V2: usize = 16 * 1024 * 1024;
/// Provisional execution ceiling, not a claim that every valid state fits.
pub const MAX_MARGIN_GUEST_CYCLES_V2: u64 = 16 * 1024 * 1024;

#[derive(Debug, Eq, PartialEq)]
pub enum MarginReceiptErrorV2 {
    Bounds,
    Encoding,
    NonCanonical,
    Kind,
    Journal,
    Image,
    Verification,
}

pub fn encode_margin_receipt_v2(receipt: &Receipt) -> Result<Vec<u8>, MarginReceiptErrorV2> {
    let bytes = serde_json::to_vec(receipt).map_err(|_| MarginReceiptErrorV2::Encoding)?;
    if !(1..=MAX_MARGIN_RECEIPT_BYTES_V2).contains(&bytes.len()) {
        return Err(MarginReceiptErrorV2::Bounds);
    }
    Ok(bytes)
}

pub fn decode_margin_receipt_v2(bytes: &[u8]) -> Result<Receipt, MarginReceiptErrorV2> {
    if !(1..=MAX_MARGIN_RECEIPT_BYTES_V2).contains(&bytes.len()) {
        return Err(MarginReceiptErrorV2::Bounds);
    }
    let receipt = serde_json::from_slice(bytes).map_err(|_| MarginReceiptErrorV2::Encoding)?;
    if encode_margin_receipt_v2(&receipt)? != bytes {
        return Err(MarginReceiptErrorV2::NonCanonical);
    }
    Ok(receipt)
}

pub fn verify_margin_receipt_v2(
    receipt: &Receipt,
    image: [u32; 8],
    journal: &[u8],
) -> Result<(), MarginReceiptErrorV2> {
    if image == [0; 8] {
        return Err(MarginReceiptErrorV2::Image);
    }
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(MarginReceiptErrorV2::Kind);
    }
    if receipt.journal.bytes != journal {
        return Err(MarginReceiptErrorV2::Journal);
    }
    receipt
        .verify(image)
        .map_err(|_| MarginReceiptErrorV2::Verification)
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[cfg(feature = "compiled-guest")]
    #[test]
    fn rebuilt_guest_matches_the_measured_execution_candidate_image() {
        use zenodex_perps_margin_global_risc0_methods::{
            ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF, ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ID,
        };
        // Measured September 13; candidate identity only, no profile admission.
        // This assertion needs a guest build and never depends on proving.
        let expected = [
            2623568652, 651265610, 1043979988, 1361420132, 2865992097, 3697114616, 2674229025,
            75673820,
        ];
        assert_eq!(ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ID, expected);
        assert_eq!(
            risc0_zkvm::compute_image_id(ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF)
                .unwrap()
                .as_words(),
            expected
        );
    }

    #[test]
    fn synthetic_succinct_seal_cannot_replace_verification() {
        // A well-typed Succinct object with no proof. The kind tag alone must
        // never pass, even when its claim and journal name the expected image.
        let succinct = serde_json::from_value(serde_json::json!({
            "seal": [], "control_id": ([0_u32; 8]),
            "claim": risc0_zkvm::MaybePruned::Value(ReceiptClaim::ok([1; 8], b"journal".to_vec())),
            "hashfn": "poseidon2", "verifier_parameters": ([0_u32; 8]),
            "control_inclusion_proof": {"index": 0, "digests": []}
        }))
        .unwrap();
        let receipt = Receipt::new(InnerReceipt::Succinct(succinct), b"journal".to_vec());
        assert_eq!(
            verify_margin_receipt_v2(&receipt, [1; 8], b"foreign"),
            Err(MarginReceiptErrorV2::Journal)
        );
        assert_eq!(
            verify_margin_receipt_v2(&receipt, [1; 8], b"journal"),
            Err(MarginReceiptErrorV2::Verification)
        );
    }

    #[test]
    fn encoded_fake_receipt_remains_unverified_and_noncanonical_aliases_reject() {
        let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        let bytes = encode_margin_receipt_v2(&fake).unwrap();
        let decoded = decode_margin_receipt_v2(&bytes).unwrap();
        assert_eq!(decoded.journal.bytes, b"journal");
        assert_eq!(
            verify_margin_receipt_v2(&decoded, [1; 8], b"journal"),
            Err(MarginReceiptErrorV2::Kind)
        );
        assert!(decoded.verify([1; 8]).is_err());
        assert_eq!(
            verify_margin_receipt_v2(&decoded, [0; 8], b"journal"),
            Err(MarginReceiptErrorV2::Image)
        );
        for suffix in [b" ".as_slice(), b"{}", b"\0"] {
            let mut extended = bytes.clone();
            extended.extend_from_slice(suffix);
            assert!(decode_margin_receipt_v2(&extended).is_err());
        }
        let mut unknown: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        unknown
            .as_object_mut()
            .unwrap()
            .insert("verified".into(), true.into());
        assert!(decode_margin_receipt_v2(&serde_json::to_vec(&unknown).unwrap()).is_err());
        assert!(decode_margin_receipt_v2(&bytes[..bytes.len() - 1]).is_err());
    }

    #[test]
    fn receipt_bounds_are_checked_before_decode() {
        for bytes in [vec![], vec![b' '; MAX_MARGIN_RECEIPT_BYTES_V2 + 1]] {
            assert!(matches!(
                decode_margin_receipt_v2(&bytes),
                Err(MarginReceiptErrorV2::Bounds)
            ));
        }
        assert!(matches!(
            decode_margin_receipt_v2(b"malformed"),
            Err(MarginReceiptErrorV2::Encoding)
        ));
    }
}
