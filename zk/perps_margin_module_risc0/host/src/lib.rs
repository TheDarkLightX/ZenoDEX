use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, LaneModuleSuccinctReceiptVerifierV1, PerpsMarginLaneModuleInputV1,
    RootV1, MAX_JOURNAL_BYTES_V1,
};
use zenodex_perps_margin_module_risc0_methods::{
    ZENODEX_PERPS_MARGIN_MODULE_GUEST_ELF, ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID,
};
use zenodex_perps_margin_module_risc0_shared::{
    canonical_perps_margin_module_guest_input_bytes_v1, prepare_perps_margin_module_v1,
    PerpsMarginModuleGuestErrorV1, PreparedPerpsMarginModuleV1,
};

pub const MAX_PERPS_MARGIN_MODULE_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;
pub const MAX_PERPS_MARGIN_MODULE_CYCLES_V1: u64 = 4 * 1024 * 1024;

#[derive(Debug)]
pub enum PerpsMarginModuleHostErrorV1 {
    Guest(PerpsMarginModuleGuestErrorV1),
    InputTooLarge,
    DevelopmentModeConfigured,
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

impl fmt::Display for PerpsMarginModuleHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "perps margin module host rejected: {self:?}")
    }
}

impl std::error::Error for PerpsMarginModuleHostErrorV1 {}

impl From<PerpsMarginModuleGuestErrorV1> for PerpsMarginModuleHostErrorV1 {
    fn from(value: PerpsMarginModuleGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_perps_margin_module_executor_env_v1(
    input: &PerpsMarginLaneModuleInputV1,
) -> Result<(ExecutorEnv<'static>, PreparedPerpsMarginModuleV1), PerpsMarginModuleHostErrorV1> {
    require_perps_margin_module_runtime_configuration_v1()?;
    let input_bytes = canonical_perps_margin_module_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| PerpsMarginModuleHostErrorV1::InputTooLarge)?;
    let prepared = prepare_perps_margin_module_v1(input.clone())?;
    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_PERPS_MARGIN_MODULE_CYCLES_V1));
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    let env = builder
        .build()
        .map_err(|_| PerpsMarginModuleHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_perps_margin_module_succinct_v1(
    input: &PerpsMarginLaneModuleInputV1,
) -> Result<Receipt, PerpsMarginModuleHostErrorV1> {
    require_perps_margin_module_runtime_configuration_v1()?;
    require_real_method_v1()?;
    let (env, prepared) = build_perps_margin_module_executor_env_v1(input)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_PERPS_MARGIN_MODULE_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| PerpsMarginModuleHostErrorV1::Proving)?;
    verify_perps_margin_module_receipt_v1(&prove_info.receipt, &prepared.journal_bytes)?;
    Ok(prove_info.receipt)
}

pub fn verify_perps_margin_module_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), PerpsMarginModuleHostErrorV1> {
    require_perps_margin_module_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(expected_journal_bytes)?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(PerpsMarginModuleHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(PerpsMarginModuleHostErrorV1::ReceiptJournal);
    }
    require_real_method_v1()?;
    receipt
        .verify(ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID)
        .map_err(|_| PerpsMarginModuleHostErrorV1::ReceiptVerification)
}

pub fn perps_margin_module_image_root_v1() -> Result<RootV1, PerpsMarginModuleHostErrorV1> {
    require_real_method_v1()?;
    let mut bytes = [0_u8; 32];
    for (chunk, word) in bytes
        .chunks_exact_mut(core::mem::size_of::<u32>())
        .zip(ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    RootV1::parse(
        format!("0x{}", hex::encode(bytes)),
        "perps margin module image root",
        false,
    )
    .map_err(|_| PerpsMarginModuleHostErrorV1::MethodBinding)
}

pub fn encode_perps_margin_module_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, PerpsMarginModuleHostErrorV1> {
    let bytes =
        serde_json::to_vec(receipt).map_err(|_| PerpsMarginModuleHostErrorV1::ReceiptEncoding)?;
    require_perps_margin_module_receipt_bytes_len_v1(bytes.len())?;
    Ok(bytes)
}

pub fn decode_canonical_perps_margin_module_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, PerpsMarginModuleHostErrorV1> {
    require_perps_margin_module_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| PerpsMarginModuleHostErrorV1::ReceiptEncoding)?;
    if encode_perps_margin_module_receipt_v1(&receipt)? != receipt_bytes {
        return Err(PerpsMarginModuleHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn require_perps_margin_module_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), PerpsMarginModuleHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_PERPS_MARGIN_MODULE_RECEIPT_BYTES_V1 {
        return Err(PerpsMarginModuleHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub fn require_perps_margin_module_runtime_configuration_v1(
) -> Result<(), PerpsMarginModuleHostErrorV1> {
    let configured = std::env::var_os("RISC0_DEV_MODE");
    if development_mode_requested_v1(configured.as_deref()) {
        return Err(PerpsMarginModuleHostErrorV1::DevelopmentModeConfigured);
    }
    Ok(())
}

pub struct PinnedPerpsMarginModuleReceiptVerifierV1;

impl LaneModuleSuccinctReceiptVerifierV1 for PinnedPerpsMarginModuleReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_perps_margin_module_receipt_bytes_len_v1(receipt_bytes.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("perps margin RISC0 receipt bytes"))?;
        require_expected_journal_bytes_v1(expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBounds("perps margin RISC0 journal bytes"))?;
        let actual_image = perps_margin_module_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("perps margin RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding("perps margin RISC0 image"));
        }
        let receipt = decode_canonical_perps_margin_module_receipt_v1(receipt_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("perps margin RISC0 receipt encoding"))?;
        verify_perps_margin_module_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("perps margin RISC0 receipt"))
    }
}

fn require_expected_journal_bytes_v1(
    expected_journal_bytes: &[u8],
) -> Result<(), PerpsMarginModuleHostErrorV1> {
    let journal_len = u64::try_from(expected_journal_bytes.len())
        .map_err(|_| PerpsMarginModuleHostErrorV1::ReceiptJournal)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(PerpsMarginModuleHostErrorV1::ReceiptJournal);
    }
    Ok(())
}

fn require_real_method_v1() -> Result<(), PerpsMarginModuleHostErrorV1> {
    if ZENODEX_PERPS_MARGIN_MODULE_GUEST_ELF.is_empty()
        || ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID == [0; 8]
    {
        Err(PerpsMarginModuleHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

fn development_mode_requested_v1(value: Option<&std::ffi::OsStr>) -> bool {
    value.is_some_and(|value| {
        value
            .to_str()
            .is_none_or(|text| matches!(text.to_ascii_lowercase().as_str(), "1" | "true" | "yes"))
    })
}

#[cfg(test)]
mod tests {
    use super::development_mode_requested_v1;
    use std::ffi::OsStr;

    #[test]
    fn development_mode_detection_is_fail_closed_for_true_and_non_utf8_values() {
        assert!(!development_mode_requested_v1(None));
        assert!(!development_mode_requested_v1(Some(OsStr::new("0"))));
        assert!(development_mode_requested_v1(Some(OsStr::new("true"))));
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            assert!(development_mode_requested_v1(Some(OsStr::from_bytes(&[
                0xff,
            ]))));
        }
    }
}
