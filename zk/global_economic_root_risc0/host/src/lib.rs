//! Measured root-image proving and verification. This module has no ledger writer.

use core::fmt;
use risc0_zkvm::{
    compute_image_id, default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt,
};
use zenodex_global_economic_epoch_risc0_shared::image_id_root_v1;
use zenodex_global_economic_root_risc0_methods::{
    ZENODEX_ECONOMIC_ROOT_GUEST_ELF, ZENODEX_ECONOMIC_ROOT_GUEST_ID,
};
use zenodex_global_economic_root_risc0_shared::{
    canonical_root_input_bytes_v1, prepare_root_input_v1, PreparedRootV1, RootGuestErrorV1,
    RootGuestInputV1,
};

#[derive(Debug)]
pub enum EconomicRootHostErrorV1 {
    Guest(RootGuestErrorV1),
    PlaceholderMethod,
    MethodBinding,
    ReceiptCount,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    Environment,
    Proving,
}
impl fmt::Display for EconomicRootHostErrorV1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "economic root host rejected: {self:?}")
    }
}
impl std::error::Error for EconomicRootHostErrorV1 {}
impl From<RootGuestErrorV1> for EconomicRootHostErrorV1 {
    fn from(value: RootGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn economic_root_image_root_v1() -> Result<String, EconomicRootHostErrorV1> {
    if ZENODEX_ECONOMIC_ROOT_GUEST_ELF.is_empty() || ZENODEX_ECONOMIC_ROOT_GUEST_ID == [0; 8] {
        return Err(EconomicRootHostErrorV1::PlaceholderMethod);
    }
    let measured = compute_image_id(ZENODEX_ECONOMIC_ROOT_GUEST_ELF)
        .map_err(|_| EconomicRootHostErrorV1::MethodBinding)?;
    if measured.as_words() != ZENODEX_ECONOMIC_ROOT_GUEST_ID {
        return Err(EconomicRootHostErrorV1::MethodBinding);
    }
    image_id_root_v1(ZENODEX_ECONOMIC_ROOT_GUEST_ID)
        .map(|root| root.as_str().to_owned())
        .map_err(|_| EconomicRootHostErrorV1::MethodBinding)
}

fn require_bound_method(prepared: &PreparedRootV1) -> Result<(), EconomicRootHostErrorV1> {
    let actual = economic_root_image_root_v1()?;
    if prepared
        .root_image_id()
        .is_some_and(|expected| expected != actual)
    {
        return Err(EconomicRootHostErrorV1::MethodBinding);
    }
    Ok(())
}

pub fn build_economic_root_executor_env_v1(
    input: &RootGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<ExecutorEnv<'static>, EconomicRootHostErrorV1> {
    let bytes = canonical_root_input_bytes_v1(input)?;
    let prepared = prepare_root_input_v1(&bytes)?;
    require_bound_method(&prepared)?;
    if receipts.len() != prepared.child_claims().len() {
        return Err(EconomicRootHostErrorV1::ReceiptCount);
    }
    let length = u32::try_from(bytes.len()).map_err(|_| EconomicRootHostErrorV1::Environment)?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[length]).write_slice(&bytes);
    for (receipt, claim) in receipts.into_iter().zip(prepared.child_claims()) {
        verify_receipt(&receipt, claim.image_id(), claim.journal_bytes())?;
        builder.add_assumption(receipt);
    }
    builder
        .build()
        .map_err(|_| EconomicRootHostErrorV1::Environment)
}

fn verify_receipt(
    receipt: &Receipt,
    image: [u32; 8],
    journal: &[u8],
) -> Result<(), EconomicRootHostErrorV1> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(EconomicRootHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != journal {
        return Err(EconomicRootHostErrorV1::ReceiptJournal);
    }
    receipt
        .verify(image)
        .map_err(|_| EconomicRootHostErrorV1::ReceiptVerification)
}

pub fn verify_economic_root_receipt_v1(
    receipt: &Receipt,
    prepared: &PreparedRootV1,
) -> Result<(), EconomicRootHostErrorV1> {
    require_bound_method(prepared)?;
    verify_receipt(
        receipt,
        ZENODEX_ECONOMIC_ROOT_GUEST_ID,
        prepared.journal_bytes(),
    )
}

pub fn prove_economic_root_succinct_v1(
    input: &RootGuestInputV1,
    receipts: Vec<Receipt>,
) -> Result<Receipt, EconomicRootHostErrorV1> {
    let prepared = prepare_root_input_v1(&canonical_root_input_bytes_v1(input)?)?;
    let env = build_economic_root_executor_env_v1(input, receipts)?;
    let receipt = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ECONOMIC_ROOT_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| EconomicRootHostErrorV1::Proving)?
        .receipt;
    verify_economic_root_receipt_v1(&receipt, &prepared)?;
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[test]
    fn claimed_success_without_cryptographic_seal_has_no_receipt_authority() {
        let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        assert!(matches!(
            verify_receipt(&fake, [1; 8], b"journal"),
            Err(EconomicRootHostErrorV1::ReceiptKind)
        ));
    }
}
