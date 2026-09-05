//! Fixed compiled route image and canonical native JSON receipt codec.
use risc0_zkvm::Receipt;
use std::process::ExitCode;
use zenodex_asset_transfer_route_composer_risc0_methods::{
    ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF, ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
};
#[path = "../../../../risc0_receipt_verifier_v1/mod.rs"]
mod endpoint;

fn decode_receipt_v1(encoded: &[u8]) -> Result<Receipt, ()> {
    let receipt: Receipt = serde_json::from_slice(encoded).map_err(|_| ())?;
    if serde_json::to_vec(&receipt).map_err(|_| ())? != encoded {
        return Err(());
    }
    Ok(receipt)
}
fn main() -> ExitCode {
    endpoint::run_v1(
        ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF,
        ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
        decode_receipt_v1,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[test]
    fn native_json_codec_rejects_noncanonical_and_unknown_fields() {
        let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        let bytes = serde_json::to_vec(&fake).unwrap();
        assert_eq!(decode_receipt_v1(&bytes).unwrap().journal.bytes, b"journal");
        let mut trailing = bytes.clone();
        trailing.push(b' ');
        assert!(decode_receipt_v1(&trailing).is_err());
        let mut extra: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        extra
            .as_object_mut()
            .unwrap()
            .insert("verified".to_owned(), serde_json::Value::Bool(true));
        assert!(decode_receipt_v1(&serde_json::to_vec(&extra).unwrap()).is_err());
        assert!(decode_receipt_v1(&bytes[..bytes.len() - 1]).is_err());
    }
}
