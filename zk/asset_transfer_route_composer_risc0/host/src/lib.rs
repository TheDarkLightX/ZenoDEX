//! Exact compiled route/coordinator image binding, without ledger authority.

use core::fmt;
use risc0_zkvm::{
    compute_image_id, default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt,
};
use zenodex_asset_lane_coordinator_risc0_methods::{
    ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF, ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_asset_transfer_route_composer_risc0_methods::{
    ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF, ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
};
use zenodex_asset_transfer_route_composer_risc0_shared::{
    canonical_asset_transfer_route_input_bytes_v1, prepare_asset_transfer_route_v1,
    AssetTransferRouteGuestErrorV1, AssetTransferRouteGuestInputV1, PreparedAssetTransferRouteV1,
};
use zenodex_global_settlement_abi_v1::RootV1;

#[derive(Debug)]
pub enum AssetTransferRouteHostErrorV1 {
    Guest(AssetTransferRouteGuestErrorV1),
    PlaceholderMethod,
    MethodBinding,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    Environment,
    Proving,
}
impl fmt::Display for AssetTransferRouteHostErrorV1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "asset route host rejected: {self:?}")
    }
}
impl std::error::Error for AssetTransferRouteHostErrorV1 {}
impl From<AssetTransferRouteGuestErrorV1> for AssetTransferRouteHostErrorV1 {
    fn from(value: AssetTransferRouteGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

fn measured_image(elf: &[u8], image: [u32; 8]) -> Result<RootV1, AssetTransferRouteHostErrorV1> {
    if elf.is_empty() || image == [0; 8] {
        return Err(AssetTransferRouteHostErrorV1::PlaceholderMethod);
    }
    let measured =
        compute_image_id(elf).map_err(|_| AssetTransferRouteHostErrorV1::MethodBinding)?;
    if measured.as_words() != image {
        return Err(AssetTransferRouteHostErrorV1::MethodBinding);
    }
    let mut hex = String::from("0x");
    for word in image {
        for byte in word.to_le_bytes() {
            hex.push_str(&format!("{byte:02x}"));
        }
    }
    RootV1::parse(hex, "compiled asset route image", false)
        .map_err(|_| AssetTransferRouteHostErrorV1::MethodBinding)
}

pub fn asset_transfer_route_image_root_v1() -> Result<RootV1, AssetTransferRouteHostErrorV1> {
    measured_image(
        ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF,
        ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
    )
}

fn require_bound_methods(
    prepared: &PreparedAssetTransferRouteV1,
) -> Result<(), AssetTransferRouteHostErrorV1> {
    measured_image(
        ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF,
        ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
    )?;
    if prepared.route_image() != &asset_transfer_route_image_root_v1()?
        || prepared.coordinator_image() != ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID
    {
        return Err(AssetTransferRouteHostErrorV1::MethodBinding);
    }
    Ok(())
}

fn verify_receipt(
    receipt: &Receipt,
    image: [u32; 8],
    journal: &[u8],
) -> Result<(), AssetTransferRouteHostErrorV1> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(AssetTransferRouteHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != journal {
        return Err(AssetTransferRouteHostErrorV1::ReceiptJournal);
    }
    receipt
        .verify(image)
        .map_err(|_| AssetTransferRouteHostErrorV1::ReceiptVerification)
}

pub fn build_asset_transfer_route_executor_env_v1(
    input: &AssetTransferRouteGuestInputV1,
    coordinator_receipt: Receipt,
) -> Result<ExecutorEnv<'static>, AssetTransferRouteHostErrorV1> {
    let bytes = canonical_asset_transfer_route_input_bytes_v1(input)?;
    let prepared = prepare_asset_transfer_route_v1(input.clone())?;
    require_bound_methods(&prepared)?;
    verify_receipt(
        &coordinator_receipt,
        prepared.coordinator_image(),
        prepared.lane_journal_bytes(),
    )?;
    let length =
        u32::try_from(bytes.len()).map_err(|_| AssetTransferRouteHostErrorV1::Environment)?;
    ExecutorEnv::builder()
        .write_slice(&[length])
        .write_slice(&bytes)
        .add_assumption(coordinator_receipt)
        .build()
        .map_err(|_| AssetTransferRouteHostErrorV1::Environment)
}

pub fn verify_asset_transfer_route_receipt_v1(
    receipt: &Receipt,
    prepared: &PreparedAssetTransferRouteV1,
) -> Result<(), AssetTransferRouteHostErrorV1> {
    require_bound_methods(prepared)?;
    verify_receipt(
        receipt,
        ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
        prepared.route_journal_bytes(),
    )
}

pub fn prove_asset_transfer_route_succinct_v1(
    input: &AssetTransferRouteGuestInputV1,
    coordinator_receipt: Receipt,
) -> Result<Receipt, AssetTransferRouteHostErrorV1> {
    let prepared = prepare_asset_transfer_route_v1(input.clone())?;
    let receipt = default_prover()
        .prove_with_opts(
            build_asset_transfer_route_executor_env_v1(input, coordinator_receipt)?,
            ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| AssetTransferRouteHostErrorV1::Proving)?
        .receipt;
    verify_asset_transfer_route_receipt_v1(&receipt, &prepared)?;
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[test]
    fn unsealed_claim_and_placeholder_have_no_verification_authority() {
        let receipt: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        assert!(matches!(
            verify_receipt(&receipt, [1; 8], b"journal"),
            Err(AssetTransferRouteHostErrorV1::ReceiptKind)
        ));
        assert!(matches!(
            measured_image(&[], [1; 8]),
            Err(AssetTransferRouteHostErrorV1::PlaceholderMethod)
        ));
    }
}
