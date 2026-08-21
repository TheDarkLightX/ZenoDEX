use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, RootV1, ZDEXLaneSuccinctReceiptVerifierV1,
};
use zenodex_zdex_fee_allocation_risc0_methods::{
    ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ELF, ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID,
};
use zenodex_zdex_fee_allocation_risc0_shared::{
    canonical_zdex_fee_allocation_guest_input_bytes_v1, prepare_zdex_fee_allocation_v1,
    PreparedZDEXFeeAllocationV1, ZDEXFeeAllocationGuestErrorV1, ZDEXFeeAllocationGuestInputV1,
};

pub const MAX_ZDEX_FEE_ALLOCATION_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub enum ZDEXFeeAllocationHostErrorV1 {
    Guest(ZDEXFeeAllocationGuestErrorV1),
    InputTooLarge,
    PlaceholderMethod,
    Environment,
    Proving,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    ReceiptEncoding,
    ReceiptNonCanonical,
    ReceiptSize,
    MethodBinding,
}

impl fmt::Display for ZDEXFeeAllocationHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "ZDEX fee-allocation host rejected: {self:?}")
    }
}

impl std::error::Error for ZDEXFeeAllocationHostErrorV1 {}

impl From<ZDEXFeeAllocationGuestErrorV1> for ZDEXFeeAllocationHostErrorV1 {
    fn from(value: ZDEXFeeAllocationGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_zdex_fee_allocation_executor_env_v1(
    input: &ZDEXFeeAllocationGuestInputV1,
) -> Result<(ExecutorEnv<'static>, PreparedZDEXFeeAllocationV1), ZDEXFeeAllocationHostErrorV1> {
    let input_bytes = canonical_zdex_fee_allocation_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| ZDEXFeeAllocationHostErrorV1::InputTooLarge)?;
    let prepared = prepare_zdex_fee_allocation_v1(input.clone())?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    let env = builder
        .build()
        .map_err(|_| ZDEXFeeAllocationHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_zdex_fee_allocation_succinct_v1(
    input: &ZDEXFeeAllocationGuestInputV1,
) -> Result<Receipt, ZDEXFeeAllocationHostErrorV1> {
    require_real_method_v1()?;
    let (env, prepared) = build_zdex_fee_allocation_executor_env_v1(input)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| ZDEXFeeAllocationHostErrorV1::Proving)?;
    verify_zdex_fee_allocation_receipt_v1(&prove_info.receipt, &prepared.journal_bytes)?;
    Ok(prove_info.receipt)
}

pub fn verify_zdex_fee_allocation_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), ZDEXFeeAllocationHostErrorV1> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(ZDEXFeeAllocationHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(ZDEXFeeAllocationHostErrorV1::ReceiptJournal);
    }
    require_real_method_v1()?;
    receipt
        .verify(ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID)
        .map_err(|_| ZDEXFeeAllocationHostErrorV1::ReceiptVerification)
}

pub fn zdex_fee_allocation_image_root_v1() -> Result<RootV1, ZDEXFeeAllocationHostErrorV1> {
    require_real_method_v1()?;
    let mut bytes = [0_u8; 32];
    for (chunk, word) in bytes
        .chunks_exact_mut(core::mem::size_of::<u32>())
        .zip(ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    RootV1::parse(
        format!("0x{}", hex::encode(bytes)),
        "ZDEX fee-allocation image root",
        false,
    )
    .map_err(|_| ZDEXFeeAllocationHostErrorV1::MethodBinding)
}

pub fn encode_zdex_fee_allocation_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, ZDEXFeeAllocationHostErrorV1> {
    serde_json::to_vec(receipt).map_err(|_| ZDEXFeeAllocationHostErrorV1::ReceiptEncoding)
}

pub fn decode_canonical_zdex_fee_allocation_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, ZDEXFeeAllocationHostErrorV1> {
    require_zdex_fee_allocation_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| ZDEXFeeAllocationHostErrorV1::ReceiptEncoding)?;
    let canonical = encode_zdex_fee_allocation_receipt_v1(&receipt)?;
    if canonical != receipt_bytes {
        return Err(ZDEXFeeAllocationHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn require_zdex_fee_allocation_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), ZDEXFeeAllocationHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_ZDEX_FEE_ALLOCATION_RECEIPT_BYTES_V1 {
        return Err(ZDEXFeeAllocationHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub struct PinnedZDEXFeeAllocationReceiptVerifierV1;

impl ZDEXLaneSuccinctReceiptVerifierV1 for PinnedZDEXFeeAllocationReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_zdex_fee_allocation_receipt_bytes_len_v1(receipt_bytes.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX fee-allocation RISC0 receipt bytes"))?;
        let actual_image = zdex_fee_allocation_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX fee-allocation RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX fee-allocation RISC0 image",
            ));
        }
        let receipt = decode_canonical_zdex_fee_allocation_receipt_v1(receipt_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX fee-allocation receipt encoding"))?;
        verify_zdex_fee_allocation_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX fee-allocation RISC0 receipt"))
    }
}

fn require_real_method_v1() -> Result<(), ZDEXFeeAllocationHostErrorV1> {
    if ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ELF.is_empty()
        || ZENODEX_ZDEX_FEE_ALLOCATION_GUEST_ID == [0; 8]
    {
        Err(ZDEXFeeAllocationHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}
