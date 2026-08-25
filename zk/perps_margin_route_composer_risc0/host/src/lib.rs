use core::fmt;

use risc0_zkvm::{default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, RootV1, RouteCompositionSuccinctReceiptVerifierV1,
    MAX_JOURNAL_BYTES_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_methods::ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID;
use zenodex_perps_margin_route_composer_risc0_methods::{
    ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF, ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID,
};
use zenodex_perps_margin_route_composer_risc0_shared::{
    canonical_perps_margin_route_composer_guest_input_bytes_v1,
    prepare_perps_margin_route_composer_v1, PerpsMarginRouteComposerGuestErrorV1,
    PerpsMarginRouteComposerGuestInputV1, PreparedPerpsMarginRouteComposerV1,
    PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1,
};

pub const MAX_PERPS_MARGIN_ROUTE_COMPOSER_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;
pub const MAX_PERPS_MARGIN_ROUTE_COMPOSER_CYCLES_V1: u64 = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginRouteComposerHostErrorV1 {
    Guest(PerpsMarginRouteComposerGuestErrorV1),
    InputTooLarge,
    DevelopmentModeConfigured,
    PlaceholderMethod,
    PlaceholderLaneMethod,
    PinnedLaneImage,
    Environment,
    LaneReceiptKind,
    LaneReceiptJournal,
    LaneReceiptVerification,
    Proving,
    RouteReceiptKind,
    RouteReceiptJournal,
    RouteReceiptVerification,
    ReceiptEncoding,
    ReceiptNonCanonical,
    ReceiptSize,
    MethodBinding,
}

impl fmt::Display for PerpsMarginRouteComposerHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "perps margin route host rejected: {self:?}")
    }
}

impl std::error::Error for PerpsMarginRouteComposerHostErrorV1 {}

impl From<PerpsMarginRouteComposerGuestErrorV1> for PerpsMarginRouteComposerHostErrorV1 {
    fn from(value: PerpsMarginRouteComposerGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_perps_margin_route_composer_executor_env_v1(
    input: &PerpsMarginRouteComposerGuestInputV1,
    lane_receipt: Receipt,
) -> Result<
    (ExecutorEnv<'static>, PreparedPerpsMarginRouteComposerV1),
    PerpsMarginRouteComposerHostErrorV1,
> {
    require_perps_margin_route_composer_runtime_configuration_v1()?;
    let input_bytes = canonical_perps_margin_route_composer_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::InputTooLarge)?;
    let prepared = prepare_perps_margin_route_composer_v1(input.clone())?;
    verify_perps_margin_lane_receipt_v1(&lane_receipt, &prepared.lane_journal_bytes)?;

    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_PERPS_MARGIN_ROUTE_COMPOSER_CYCLES_V1));
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    builder.add_assumption(lane_receipt);
    let env = builder
        .build()
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_perps_margin_route_composer_succinct_v1(
    input: &PerpsMarginRouteComposerGuestInputV1,
    lane_receipt: Receipt,
) -> Result<Receipt, PerpsMarginRouteComposerHostErrorV1> {
    require_perps_margin_route_composer_runtime_configuration_v1()?;
    require_real_route_method_v1()?;
    let (env, prepared) = build_perps_margin_route_composer_executor_env_v1(input, lane_receipt)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::Proving)?;
    verify_perps_margin_route_composer_receipt_v1(
        &prove_info.receipt,
        &prepared.route_journal_bytes,
    )?;
    Ok(prove_info.receipt)
}

pub fn verify_perps_margin_lane_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    require_expected_journal_bytes_v1(
        expected_journal_bytes,
        PerpsMarginRouteComposerHostErrorV1::LaneReceiptJournal,
    )?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(PerpsMarginRouteComposerHostErrorV1::LaneReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(PerpsMarginRouteComposerHostErrorV1::LaneReceiptJournal);
    }
    require_real_lane_method_v1()?;
    receipt
        .verify(PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1)
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::LaneReceiptVerification)
}

pub fn verify_perps_margin_route_composer_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    require_expected_journal_bytes_v1(
        expected_journal_bytes,
        PerpsMarginRouteComposerHostErrorV1::RouteReceiptJournal,
    )?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(PerpsMarginRouteComposerHostErrorV1::RouteReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(PerpsMarginRouteComposerHostErrorV1::RouteReceiptJournal);
    }
    require_real_route_method_v1()?;
    receipt
        .verify(ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID)
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::RouteReceiptVerification)
}

pub fn perps_margin_route_composer_image_root_v1(
) -> Result<RootV1, PerpsMarginRouteComposerHostErrorV1> {
    require_real_route_method_v1()?;
    image_id_root_v1(
        ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID,
        "perps margin route composer image root",
    )
}

pub fn encode_perps_margin_route_composer_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, PerpsMarginRouteComposerHostErrorV1> {
    let bytes = serde_json::to_vec(receipt)
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::ReceiptEncoding)?;
    require_perps_margin_route_composer_receipt_bytes_len_v1(bytes.len())?;
    Ok(bytes)
}

pub fn decode_canonical_perps_margin_route_composer_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, PerpsMarginRouteComposerHostErrorV1> {
    require_perps_margin_route_composer_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::ReceiptEncoding)?;
    if encode_perps_margin_route_composer_receipt_v1(&receipt)? != receipt_bytes {
        return Err(PerpsMarginRouteComposerHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn require_perps_margin_route_composer_runtime_configuration_v1(
) -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    let configured = std::env::var_os("RISC0_DEV_MODE");
    if development_mode_requested_v1(configured.as_deref()) {
        return Err(PerpsMarginRouteComposerHostErrorV1::DevelopmentModeConfigured);
    }
    Ok(())
}

pub struct PinnedPerpsMarginRouteComposerReceiptVerifierV1;

impl RouteCompositionSuccinctReceiptVerifierV1 for PinnedPerpsMarginRouteComposerReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_perps_margin_route_composer_receipt_bytes_len_v1(receipt_bytes.len()).map_err(
            |_| AbiErrorV1::InvalidBounds("perps margin route composer RISC0 receipt bytes"),
        )?;
        let actual_image = perps_margin_route_composer_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("perps margin route composer RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin route composer RISC0 image",
            ));
        }
        let receipt = decode_canonical_perps_margin_route_composer_receipt_v1(receipt_bytes)
            .map_err(|_| {
                AbiErrorV1::InvalidBinding("perps margin route composer receipt encoding")
            })?;
        verify_perps_margin_route_composer_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("perps margin route composer receipt"))
    }
}

pub fn require_perps_margin_route_composer_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_PERPS_MARGIN_ROUTE_COMPOSER_RECEIPT_BYTES_V1 {
        return Err(PerpsMarginRouteComposerHostErrorV1::ReceiptSize);
    }
    Ok(())
}

fn require_expected_journal_bytes_v1(
    expected_journal_bytes: &[u8],
    error: PerpsMarginRouteComposerHostErrorV1,
) -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    let journal_len = u64::try_from(expected_journal_bytes.len()).map_err(|_| error)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(error);
    }
    Ok(())
}

fn image_id_root_v1(
    image_id: [u32; 8],
    field: &'static str,
) -> Result<RootV1, PerpsMarginRouteComposerHostErrorV1> {
    let mut bytes = [0_u8; 32];
    for (chunk, word) in bytes
        .chunks_exact_mut(core::mem::size_of::<u32>())
        .zip(image_id)
    {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    RootV1::parse(format!("0x{}", hex::encode(bytes)), field, false)
        .map_err(|_| PerpsMarginRouteComposerHostErrorV1::MethodBinding)
}

fn require_real_route_method_v1() -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    if ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ELF.is_empty()
        || ZENODEX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_ID == [0; 8]
    {
        Err(PerpsMarginRouteComposerHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

fn require_real_lane_method_v1() -> Result<(), PerpsMarginRouteComposerHostErrorV1> {
    if ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID == [0; 8] {
        return Err(PerpsMarginRouteComposerHostErrorV1::PlaceholderLaneMethod);
    }
    if ZENODEX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_ID != PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1 {
        return Err(PerpsMarginRouteComposerHostErrorV1::PinnedLaneImage);
    }
    Ok(())
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
    fn development_mode_detection_is_fail_closed() {
        assert!(!development_mode_requested_v1(None));
        assert!(!development_mode_requested_v1(Some(OsStr::new("0"))));
        assert!(development_mode_requested_v1(Some(OsStr::new("true"))));
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            assert!(development_mode_requested_v1(Some(OsStr::from_bytes(&[
                0xff
            ]))));
        }
    }
}
