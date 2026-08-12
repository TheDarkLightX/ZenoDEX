use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_asset_transfer_module_risc0_methods::{
    ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF, ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
};
use zenodex_asset_transfer_module_risc0_shared::{
    canonical_asset_transfer_guest_input_bytes_v1, prepare_asset_transfer_module_v1,
    AssetTransferGuestErrorV1, PreparedAssetTransferModuleV1,
};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, AssetTransferLaneModuleInputV1, LaneModuleSuccinctReceiptVerifierV1,
    RootV1,
};

pub const MAX_ASSET_TRANSFER_MODULE_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub enum AssetTransferModuleHostErrorV1 {
    Guest(AssetTransferGuestErrorV1),
    InputTooLarge,
    PlaceholderMethod,
    Environment,
    Proving,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    ReceiptEncoding,
    ReceiptDecoding,
    ReceiptSize,
    MethodBinding,
}

impl fmt::Display for AssetTransferModuleHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "asset transfer module host rejected: {self:?}")
    }
}

impl std::error::Error for AssetTransferModuleHostErrorV1 {}

impl From<AssetTransferGuestErrorV1> for AssetTransferModuleHostErrorV1 {
    fn from(value: AssetTransferGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_asset_transfer_module_executor_env_v1(
    input: &AssetTransferLaneModuleInputV1,
) -> Result<(ExecutorEnv<'static>, PreparedAssetTransferModuleV1), AssetTransferModuleHostErrorV1> {
    let input_bytes = canonical_asset_transfer_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| AssetTransferModuleHostErrorV1::InputTooLarge)?;
    let prepared = prepare_asset_transfer_module_v1(input.clone())?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    let env = builder
        .build()
        .map_err(|_| AssetTransferModuleHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_asset_transfer_module_succinct_v1(
    input: &AssetTransferLaneModuleInputV1,
) -> Result<Receipt, AssetTransferModuleHostErrorV1> {
    require_real_method_v1()?;
    let (env, prepared) = build_asset_transfer_module_executor_env_v1(input)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| AssetTransferModuleHostErrorV1::Proving)?;
    verify_asset_transfer_module_receipt_v1(&prove_info.receipt, &prepared.journal_bytes)?;
    Ok(prove_info.receipt)
}

pub fn verify_asset_transfer_module_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), AssetTransferModuleHostErrorV1> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(AssetTransferModuleHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(AssetTransferModuleHostErrorV1::ReceiptJournal);
    }
    require_real_method_v1()?;
    receipt
        .verify(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID)
        .map_err(|_| AssetTransferModuleHostErrorV1::ReceiptVerification)
}

pub fn asset_transfer_module_image_root_v1() -> Result<RootV1, AssetTransferModuleHostErrorV1> {
    require_real_method_v1()?;
    let mut bytes = [0_u8; 32];
    for (chunk, word) in bytes
        .chunks_exact_mut(core::mem::size_of::<u32>())
        .zip(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    RootV1::parse(
        format!("0x{}", hex::encode(bytes)),
        "asset transfer module image root",
        false,
    )
    .map_err(|_| AssetTransferModuleHostErrorV1::MethodBinding)
}

pub fn encode_asset_transfer_module_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, AssetTransferModuleHostErrorV1> {
    serde_json::to_vec(receipt).map_err(|_| AssetTransferModuleHostErrorV1::ReceiptEncoding)
}

pub fn require_asset_transfer_module_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), AssetTransferModuleHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_ASSET_TRANSFER_MODULE_RECEIPT_BYTES_V1 {
        return Err(AssetTransferModuleHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub struct PinnedAssetTransferModuleReceiptVerifierV1;

impl LaneModuleSuccinctReceiptVerifierV1 for PinnedAssetTransferModuleReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_asset_transfer_module_receipt_bytes_len_v1(receipt_bytes.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("asset transfer RISC0 receipt bytes"))?;
        let actual_image = asset_transfer_module_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("asset transfer RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding("asset transfer RISC0 image"));
        }
        let receipt: Receipt = serde_json::from_slice(receipt_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("asset transfer RISC0 receipt encoding"))?;
        verify_asset_transfer_module_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("asset transfer RISC0 receipt"))
    }
}

fn require_real_method_v1() -> Result<(), AssetTransferModuleHostErrorV1> {
    if ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF.is_empty()
        || ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID == [0; 8]
    {
        Err(AssetTransferModuleHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}
