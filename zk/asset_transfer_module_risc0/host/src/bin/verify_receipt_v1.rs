//! Verification-only V1 endpoint; compiled method and native json codec.
use risc0_zkvm::Receipt;
use std::process::ExitCode;
use zenodex_asset_transfer_module_risc0_host::encode_asset_transfer_module_receipt_v1 as encode_native_receipt;
use zenodex_asset_transfer_module_risc0_methods::{
    ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF, ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
};

#[path = "../../../../risc0_receipt_verifier_v1/mod.rs"]
mod endpoint;

fn decode_receipt_v1(encoded: &[u8]) -> Result<Receipt, ()> {
    let receipt: Receipt = serde_json::from_slice(encoded).map_err(|_| ())?;
    let canonical = encode_native_receipt(&receipt).map_err(|_| ())?;
    if canonical != encoded {
        return Err(());
    }
    Ok(receipt)
}

fn main() -> ExitCode {
    endpoint::run_v1(
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF,
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
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
        let encoded = encode_native_receipt(&fake).unwrap();
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
        assert!(decode_receipt_v1(&[2, 0, 0, 1]).is_err());
    }
}
