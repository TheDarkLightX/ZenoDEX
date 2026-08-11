use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_asset_lane_coordinator_risc0_methods::{
    ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF, ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_asset_lane_coordinator_risc0_shared::{
    canonical_asset_lane_coordinator_guest_input_bytes_v1, prepare_asset_lane_coordinator_v1,
    AssetLaneCoordinatorGuestErrorV1, AssetLaneCoordinatorGuestInputV1,
    PreparedAssetLaneCoordinatorV1, ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, LaneCompositionSuccinctReceiptVerifierV1, RootV1,
};

#[derive(Debug)]
pub enum AssetLaneCoordinatorHostErrorV1 {
    Guest(AssetLaneCoordinatorGuestErrorV1),
    InputTooLarge,
    PlaceholderMethod,
    PinnedModuleImage,
    Environment,
    ModuleReceiptKind,
    ModuleReceiptJournal,
    ModuleReceiptVerification,
    Proving,
    LaneReceiptKind,
    LaneReceiptJournal,
    LaneReceiptVerification,
    ReceiptEncoding,
    ReceiptDecoding,
    MethodBinding,
}

impl fmt::Display for AssetLaneCoordinatorHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "asset lane coordinator host rejected: {self:?}")
    }
}

impl std::error::Error for AssetLaneCoordinatorHostErrorV1 {}

impl From<AssetLaneCoordinatorGuestErrorV1> for AssetLaneCoordinatorHostErrorV1 {
    fn from(value: AssetLaneCoordinatorGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_asset_lane_coordinator_executor_env_v1(
    input: &AssetLaneCoordinatorGuestInputV1,
    module_receipt: Receipt,
) -> Result<(ExecutorEnv<'static>, PreparedAssetLaneCoordinatorV1), AssetLaneCoordinatorHostErrorV1>
{
    let input_bytes = canonical_asset_lane_coordinator_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| AssetLaneCoordinatorHostErrorV1::InputTooLarge)?;
    let prepared = prepare_asset_lane_coordinator_v1(input.clone())?;
    verify_module_receipt_v1(&module_receipt, &prepared.module_journal_bytes)?;

    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    builder.add_assumption(module_receipt);
    let env = builder
        .build()
        .map_err(|_| AssetLaneCoordinatorHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_asset_lane_coordinator_succinct_v1(
    input: &AssetLaneCoordinatorGuestInputV1,
    module_receipt: Receipt,
) -> Result<Receipt, AssetLaneCoordinatorHostErrorV1> {
    require_real_method_v1()?;
    let (env, prepared) = build_asset_lane_coordinator_executor_env_v1(input, module_receipt)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| AssetLaneCoordinatorHostErrorV1::Proving)?;
    verify_asset_lane_coordinator_receipt_v1(&prove_info.receipt, &prepared.lane_journal_bytes)?;
    Ok(prove_info.receipt)
}

pub fn verify_module_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), AssetLaneCoordinatorHostErrorV1> {
    require_pinned_module_image_v1()?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(AssetLaneCoordinatorHostErrorV1::ModuleReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(AssetLaneCoordinatorHostErrorV1::ModuleReceiptJournal);
    }
    receipt
        .verify(ASSET_TRANSFER_MODULE_IMAGE_ID_V1)
        .map_err(|_| AssetLaneCoordinatorHostErrorV1::ModuleReceiptVerification)
}

pub fn verify_asset_lane_coordinator_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), AssetLaneCoordinatorHostErrorV1> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(AssetLaneCoordinatorHostErrorV1::LaneReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(AssetLaneCoordinatorHostErrorV1::LaneReceiptJournal);
    }
    require_real_method_v1()?;
    receipt
        .verify(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID)
        .map_err(|_| AssetLaneCoordinatorHostErrorV1::LaneReceiptVerification)
}

pub fn asset_lane_coordinator_image_root_v1() -> Result<RootV1, AssetLaneCoordinatorHostErrorV1> {
    require_real_method_v1()?;
    image_id_root_v1(
        ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
        "asset lane coordinator image root",
    )
}

pub fn asset_transfer_module_image_root_v1() -> Result<RootV1, AssetLaneCoordinatorHostErrorV1> {
    require_pinned_module_image_v1()?;
    image_id_root_v1(
        ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
        "asset transfer module image root",
    )
}

pub fn encode_asset_lane_coordinator_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, AssetLaneCoordinatorHostErrorV1> {
    serde_json::to_vec(receipt).map_err(|_| AssetLaneCoordinatorHostErrorV1::ReceiptEncoding)
}

pub struct PinnedAssetLaneCoordinatorReceiptVerifierV1;

impl LaneCompositionSuccinctReceiptVerifierV1 for PinnedAssetLaneCoordinatorReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        let actual_image = asset_lane_coordinator_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("asset lane coordinator RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding(
                "asset lane coordinator RISC0 image",
            ));
        }
        let receipt: Receipt = serde_json::from_slice(receipt_bytes).map_err(|_| {
            AbiErrorV1::InvalidBinding("asset lane coordinator RISC0 receipt encoding")
        })?;
        verify_asset_lane_coordinator_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("asset lane coordinator RISC0 receipt"))
    }
}

fn image_id_root_v1(
    image_id: [u32; 8],
    field: &'static str,
) -> Result<RootV1, AssetLaneCoordinatorHostErrorV1> {
    let mut bytes = [0_u8; 32];
    for (chunk, word) in bytes
        .chunks_exact_mut(core::mem::size_of::<u32>())
        .zip(image_id)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    RootV1::parse(format!("0x{}", hex::encode(bytes)), field, false)
        .map_err(|_| AssetLaneCoordinatorHostErrorV1::MethodBinding)
}

fn require_real_method_v1() -> Result<(), AssetLaneCoordinatorHostErrorV1> {
    if ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF.is_empty()
        || ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID == [0; 8]
    {
        Err(AssetLaneCoordinatorHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

fn require_pinned_module_image_v1() -> Result<(), AssetLaneCoordinatorHostErrorV1> {
    if ASSET_TRANSFER_MODULE_IMAGE_ID_V1 == [0; 8] {
        Err(AssetLaneCoordinatorHostErrorV1::PinnedModuleImage)
    } else {
        Ok(())
    }
}
