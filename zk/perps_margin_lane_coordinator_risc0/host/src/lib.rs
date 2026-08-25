use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, LaneCompositionSuccinctReceiptVerifierV1, RootV1, MAX_JOURNAL_BYTES_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_methods::{
    ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF, ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    canonical_perps_margin_lane_coordinator_guest_input_bytes_v1,
    prepare_perps_margin_lane_coordinator_v1, PerpsMarginLaneCoordinatorGuestErrorV1,
    PerpsMarginLaneCoordinatorGuestInputV1, PreparedPerpsMarginLaneCoordinatorV1,
    PERPS_MARGIN_MODULE_IMAGE_ID_V1,
};

pub const MAX_PERPS_MARGIN_LANE_COORDINATOR_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;
pub const MAX_PERPS_MARGIN_LANE_COORDINATOR_CYCLES_V1: u64 = 8 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginLaneCoordinatorHostErrorV1 {
    Guest(PerpsMarginLaneCoordinatorGuestErrorV1),
    InputTooLarge,
    DevelopmentModeConfigured,
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
    ReceiptNonCanonical,
    ReceiptSize,
    MethodBinding,
}

impl fmt::Display for PerpsMarginLaneCoordinatorHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "perps margin lane coordinator host rejected: {self:?}"
        )
    }
}

impl std::error::Error for PerpsMarginLaneCoordinatorHostErrorV1 {}

impl From<PerpsMarginLaneCoordinatorGuestErrorV1> for PerpsMarginLaneCoordinatorHostErrorV1 {
    fn from(value: PerpsMarginLaneCoordinatorGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_perps_margin_lane_coordinator_executor_env_v1(
    input: &PerpsMarginLaneCoordinatorGuestInputV1,
    module_receipt: Receipt,
) -> Result<
    (ExecutorEnv<'static>, PreparedPerpsMarginLaneCoordinatorV1),
    PerpsMarginLaneCoordinatorHostErrorV1,
> {
    require_perps_margin_lane_coordinator_runtime_configuration_v1()?;
    let input_bytes = canonical_perps_margin_lane_coordinator_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::InputTooLarge)?;
    let prepared = prepare_perps_margin_lane_coordinator_v1(input.clone())?;
    verify_perps_margin_module_receipt_v1(&module_receipt, &prepared.module_journal_bytes)?;

    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_PERPS_MARGIN_LANE_COORDINATOR_CYCLES_V1));
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    builder.add_assumption(module_receipt);
    let env = builder
        .build()
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_perps_margin_lane_coordinator_succinct_v1(
    input: &PerpsMarginLaneCoordinatorGuestInputV1,
    module_receipt: Receipt,
) -> Result<Receipt, PerpsMarginLaneCoordinatorHostErrorV1> {
    require_perps_margin_lane_coordinator_runtime_configuration_v1()?;
    require_real_method_v1()?;
    let (env, prepared) =
        build_perps_margin_lane_coordinator_executor_env_v1(input, module_receipt)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::Proving)?;
    verify_perps_margin_lane_coordinator_receipt_v1(
        &prove_info.receipt,
        &prepared.lane_journal_bytes,
    )?;
    Ok(prove_info.receipt)
}

pub fn verify_perps_margin_module_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    require_perps_margin_lane_coordinator_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(
        expected_journal_bytes,
        PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptJournal,
    )?;
    require_pinned_module_image_v1()?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptJournal);
    }
    receipt
        .verify(PERPS_MARGIN_MODULE_IMAGE_ID_V1)
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::ModuleReceiptVerification)
}

pub fn verify_perps_margin_lane_coordinator_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    require_perps_margin_lane_coordinator_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(
        expected_journal_bytes,
        PerpsMarginLaneCoordinatorHostErrorV1::LaneReceiptJournal,
    )?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::LaneReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::LaneReceiptJournal);
    }
    require_real_method_v1()?;
    receipt
        .verify(ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID)
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::LaneReceiptVerification)
}

pub fn perps_margin_lane_coordinator_image_root_v1(
) -> Result<RootV1, PerpsMarginLaneCoordinatorHostErrorV1> {
    require_real_method_v1()?;
    image_id_root_v1(
        ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID,
        "perps margin lane coordinator image root",
    )
}

pub fn perps_margin_module_image_root_v1() -> Result<RootV1, PerpsMarginLaneCoordinatorHostErrorV1>
{
    require_pinned_module_image_v1()?;
    image_id_root_v1(
        PERPS_MARGIN_MODULE_IMAGE_ID_V1,
        "perps margin module image root",
    )
}

pub fn encode_perps_margin_lane_coordinator_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, PerpsMarginLaneCoordinatorHostErrorV1> {
    let bytes = serde_json::to_vec(receipt)
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::ReceiptEncoding)?;
    require_perps_margin_lane_coordinator_receipt_bytes_len_v1(bytes.len())?;
    Ok(bytes)
}

pub fn decode_canonical_perps_margin_lane_coordinator_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, PerpsMarginLaneCoordinatorHostErrorV1> {
    require_perps_margin_lane_coordinator_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::ReceiptEncoding)?;
    if encode_perps_margin_lane_coordinator_receipt_v1(&receipt)? != receipt_bytes {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn require_perps_margin_lane_coordinator_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_PERPS_MARGIN_LANE_COORDINATOR_RECEIPT_BYTES_V1 {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub fn require_perps_margin_lane_coordinator_runtime_configuration_v1(
) -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    let configured = std::env::var_os("RISC0_DEV_MODE");
    if development_mode_requested_v1(configured.as_deref()) {
        return Err(PerpsMarginLaneCoordinatorHostErrorV1::DevelopmentModeConfigured);
    }
    Ok(())
}

pub struct PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1;

impl LaneCompositionSuccinctReceiptVerifierV1
    for PinnedPerpsMarginLaneCoordinatorReceiptVerifierV1
{
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_perps_margin_lane_coordinator_receipt_bytes_len_v1(receipt_bytes.len()).map_err(
            |_| AbiErrorV1::InvalidBounds("perps margin lane coordinator RISC0 receipt bytes"),
        )?;
        let actual_image = perps_margin_lane_coordinator_image_root_v1().map_err(|_| {
            AbiErrorV1::InvalidBinding("perps margin lane coordinator RISC0 method")
        })?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin lane coordinator RISC0 image",
            ));
        }
        let receipt = decode_canonical_perps_margin_lane_coordinator_receipt_v1(receipt_bytes)
            .map_err(|_| {
                AbiErrorV1::InvalidBinding("perps margin lane coordinator RISC0 receipt encoding")
            })?;
        verify_perps_margin_lane_coordinator_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("perps margin lane coordinator RISC0 receipt"))
    }
}

fn require_expected_journal_bytes_v1(
    expected_journal_bytes: &[u8],
    error: PerpsMarginLaneCoordinatorHostErrorV1,
) -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    let journal_len = u64::try_from(expected_journal_bytes.len()).map_err(|_| error)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(error);
    }
    Ok(())
}

fn image_id_root_v1(
    image_id: [u32; 8],
    field: &'static str,
) -> Result<RootV1, PerpsMarginLaneCoordinatorHostErrorV1> {
    let mut bytes = [0_u8; 32];
    for (chunk, word) in bytes
        .chunks_exact_mut(core::mem::size_of::<u32>())
        .zip(image_id)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    RootV1::parse(format!("0x{}", hex::encode(bytes)), field, false)
        .map_err(|_| PerpsMarginLaneCoordinatorHostErrorV1::MethodBinding)
}

fn require_real_method_v1() -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    if ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ELF.is_empty()
        || ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID == [0; 8]
    {
        Err(PerpsMarginLaneCoordinatorHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

fn require_pinned_module_image_v1() -> Result<(), PerpsMarginLaneCoordinatorHostErrorV1> {
    if PERPS_MARGIN_MODULE_IMAGE_ID_V1 == [0; 8] {
        Err(PerpsMarginLaneCoordinatorHostErrorV1::PinnedModuleImage)
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
