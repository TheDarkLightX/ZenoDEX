//! Verification-only V1 endpoint; compiled method and native postcard codec.
use risc0_zkvm::Receipt;
use std::process::ExitCode;
use zenodex_global_economic_root_risc0_methods::{
    ZENODEX_ECONOMIC_ROOT_GUEST_ELF, ZENODEX_ECONOMIC_ROOT_GUEST_ID,
};

#[path = "../../../../risc0_receipt_verifier_v1/mod.rs"]
mod endpoint;

fn decode_receipt_v1(encoded: &[u8]) -> Result<Receipt, ()> {
    let (receipt, trailing): (Receipt, _) = postcard::take_from_bytes(encoded).map_err(|_| ())?;
    if !trailing.is_empty() {
        return Err(());
    }
    let canonical = postcard::to_allocvec(&receipt).map_err(|_| ())?;
    if canonical != encoded {
        return Err(());
    }
    Ok(receipt)
}

fn main() -> ExitCode {
    endpoint::run_v1(
        ZENODEX_ECONOMIC_ROOT_GUEST_ELF,
        ZENODEX_ECONOMIC_ROOT_GUEST_ID,
        decode_receipt_v1,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[test]
    fn canonical_native_codec_round_trips_but_other_encodings_reject() {
        let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        let encoded = postcard::to_allocvec(&fake).unwrap();
        assert_eq!(
            decode_receipt_v1(&encoded).unwrap().journal.bytes,
            b"journal"
        );
        for suffix in [b' ', 0] {
            let mut extended = encoded.clone();
            extended.push(suffix);
            assert!(decode_receipt_v1(&extended).is_err());
        }
        assert!(decode_receipt_v1(&encoded[..encoded.len() - 1]).is_err());
        assert!(decode_receipt_v1(b"malformed").is_err());
        assert!(decode_receipt_v1(br#"{"inner":{"Fake":{}}}"#).is_err());
    }
}
