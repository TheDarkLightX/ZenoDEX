use core::fmt;

use risc0_zkvm::{default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, RootV1, ZDEXLaneSuccinctReceiptVerifierV1, MAX_JOURNAL_BYTES_V1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_methods::{
    ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
    ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_shared::{
    canonical_zdex_tokenomics_fee_lane_coordinator_guest_input_bytes_v1,
    canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1,
    prepare_zdex_tokenomics_fee_lane_coordinator_v1, prepare_zdex_tokenomics_lane_coordinator_v1,
    risc0_digest_bytes_from_root_v1, PreparedZDEXTokenomicsFeeLaneCoordinatorV1,
    PreparedZDEXTokenomicsLaneCoordinatorV1, ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
    ZDEXTokenomicsLaneCoordinatorGuestErrorV1, ZDEXTokenomicsLaneCoordinatorGuestInputV1,
    MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_JOURNAL_BYTES_V1,
};

pub const MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub enum ZDEXTokenomicsLaneCoordinatorHostErrorV1 {
    Guest(ZDEXTokenomicsLaneCoordinatorGuestErrorV1),
    InputTooLarge,
    DevelopmentModeConfigured,
    PlaceholderMethod,
    Environment,
    Proving,
    ChildReceiptKind,
    ChildReceiptJournal,
    ChildReceiptVerification,
    ReceiptKind,
    ReceiptJournal,
    ReceiptVerification,
    ReceiptEncoding,
    ReceiptNonCanonical,
    ReceiptSize,
    MethodBinding,
}

impl fmt::Display for ZDEXTokenomicsLaneCoordinatorHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "ZDEX tokenomics lane coordinator host rejected: {self:?}"
        )
    }
}

impl std::error::Error for ZDEXTokenomicsLaneCoordinatorHostErrorV1 {}

impl From<ZDEXTokenomicsLaneCoordinatorGuestErrorV1> for ZDEXTokenomicsLaneCoordinatorHostErrorV1 {
    fn from(value: ZDEXTokenomicsLaneCoordinatorGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_zdex_tokenomics_lane_coordinator_executor_env_v1(
    input: &ZDEXTokenomicsLaneCoordinatorGuestInputV1,
    child_burn_receipt: &Receipt,
) -> Result<
    (
        ExecutorEnv<'static>,
        PreparedZDEXTokenomicsLaneCoordinatorV1,
    ),
    ZDEXTokenomicsLaneCoordinatorHostErrorV1,
> {
    require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1()?;
    let input_bytes = canonical_zdex_tokenomics_lane_coordinator_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::InputTooLarge)?;
    let prepared = prepare_zdex_tokenomics_lane_coordinator_v1(input.clone())?;
    verify_child_burn_receipt_v1(
        child_burn_receipt,
        &prepared.input.module_release.guest_image_id,
        &prepared.burn_journal_bytes,
    )?;

    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    builder.add_assumption(child_burn_receipt.clone());
    let env = builder
        .build()
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn build_zdex_tokenomics_fee_lane_coordinator_executor_env_v1(
    input: &ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
    child_fee_receipt: &Receipt,
) -> Result<
    (
        ExecutorEnv<'static>,
        PreparedZDEXTokenomicsFeeLaneCoordinatorV1,
    ),
    ZDEXTokenomicsLaneCoordinatorHostErrorV1,
> {
    require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1()?;
    let input_bytes = canonical_zdex_tokenomics_fee_lane_coordinator_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::InputTooLarge)?;
    let prepared = prepare_zdex_tokenomics_fee_lane_coordinator_v1(input.clone())?;
    verify_child_fee_allocation_receipt_v1(
        child_fee_receipt,
        &prepared.input.module_release.guest_image_id,
        &prepared.child_journal_bytes,
    )?;

    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    builder.add_assumption(child_fee_receipt.clone());
    let env = builder
        .build()
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_zdex_tokenomics_lane_coordinator_succinct_v1(
    input: &ZDEXTokenomicsLaneCoordinatorGuestInputV1,
    child_burn_receipt: &Receipt,
) -> Result<Receipt, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1()?;
    require_real_coordinator_method_v1()?;
    let (env, prepared) =
        build_zdex_tokenomics_lane_coordinator_executor_env_v1(input, child_burn_receipt)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::Proving)?;
    verify_zdex_tokenomics_lane_coordinator_receipt_v1(
        &prove_info.receipt,
        &prepared.lane_journal_bytes,
    )?;
    Ok(prove_info.receipt)
}

pub fn prove_zdex_tokenomics_fee_lane_coordinator_succinct_v1(
    input: &ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
    child_fee_receipt: &Receipt,
) -> Result<Receipt, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1()?;
    require_real_coordinator_method_v1()?;
    let (env, prepared) =
        build_zdex_tokenomics_fee_lane_coordinator_executor_env_v1(input, child_fee_receipt)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::Proving)?;
    verify_zdex_tokenomics_lane_coordinator_receipt_v1(
        &prove_info.receipt,
        &prepared.lane_journal_bytes,
    )?;
    Ok(prove_info.receipt)
}

pub fn verify_child_burn_receipt_v1(
    receipt: &Receipt,
    expected_image_id: &RootV1,
    expected_burn_journal_bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    verify_child_module_receipt_v1(receipt, expected_image_id, expected_burn_journal_bytes)
}

pub fn verify_child_fee_allocation_receipt_v1(
    receipt: &Receipt,
    expected_image_id: &RootV1,
    expected_fee_journal_bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    verify_child_module_receipt_v1(receipt, expected_image_id, expected_fee_journal_bytes)
}

pub fn verify_child_module_receipt_v1(
    receipt: &Receipt,
    expected_image_id: &RootV1,
    expected_child_journal_bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(expected_child_journal_bytes, true)?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptKind);
    }
    if receipt.journal.bytes != expected_child_journal_bytes {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptJournal);
    }
    let image_id = digest_from_root_v1(expected_image_id)?;
    receipt
        .verify(image_id)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptVerification)
}

pub fn verify_zdex_tokenomics_lane_coordinator_receipt_v1(
    receipt: &Receipt,
    expected_lane_journal_bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(expected_lane_journal_bytes, false)?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_lane_journal_bytes {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptJournal);
    }
    require_real_coordinator_method_v1()?;
    receipt
        .verify(ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptVerification)
}

pub fn zdex_tokenomics_lane_coordinator_image_root_v1(
) -> Result<RootV1, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    require_real_coordinator_method_v1()?;
    image_root_from_words_v1(ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID)
}

pub fn encode_zdex_tokenomics_lane_coordinator_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    let receipt_bytes = serde_json::to_vec(receipt)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptEncoding)?;
    require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(receipt_bytes.len())?;
    Ok(receipt_bytes)
}

pub fn decode_canonical_zdex_tokenomics_lane_coordinator_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptEncoding)?;
    let canonical = encode_zdex_tokenomics_lane_coordinator_receipt_v1(&receipt)?;
    if canonical != receipt_bytes {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_RECEIPT_BYTES_V1 {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub fn require_zdex_tokenomics_lane_coordinator_runtime_configuration_v1(
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    let configured = std::env::var_os("RISC0_DEV_MODE");
    require_development_mode_unset_v1(configured.as_deref())
}

pub struct PinnedZDEXTokenomicsLaneCoordinatorReceiptVerifierV1;

impl ZDEXLaneSuccinctReceiptVerifierV1 for PinnedZDEXTokenomicsLaneCoordinatorReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_zdex_tokenomics_lane_coordinator_receipt_bytes_len_v1(receipt_bytes.len())
            .map_err(|_| {
                AbiErrorV1::InvalidBounds("ZDEX tokenomics coordinator RISC0 receipt bytes")
            })?;
        require_expected_journal_bytes_v1(expected_journal_bytes, false).map_err(|_| {
            AbiErrorV1::InvalidBounds("ZDEX tokenomics coordinator RISC0 journal bytes")
        })?;
        let actual_image = zdex_tokenomics_lane_coordinator_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX tokenomics coordinator RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX tokenomics coordinator RISC0 image",
            ));
        }
        let receipt = decode_canonical_zdex_tokenomics_lane_coordinator_receipt_v1(receipt_bytes)
            .map_err(|_| {
            AbiErrorV1::InvalidBinding("ZDEX tokenomics coordinator receipt encoding")
        })?;
        verify_zdex_tokenomics_lane_coordinator_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX tokenomics coordinator RISC0 receipt"))
    }
}

fn require_expected_journal_bytes_v1(
    expected_journal_bytes: &[u8],
    child: bool,
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    let journal_len = u64::try_from(expected_journal_bytes.len()).map_err(|_| {
        if child {
            ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptJournal
        } else {
            ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptJournal
        }
    })?;
    let maximum = if child {
        MAX_JOURNAL_BYTES_V1
    } else {
        MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_JOURNAL_BYTES_V1.min(MAX_JOURNAL_BYTES_V1)
    };
    if journal_len == 0 || journal_len > maximum {
        return Err(if child {
            ZDEXTokenomicsLaneCoordinatorHostErrorV1::ChildReceiptJournal
        } else {
            ZDEXTokenomicsLaneCoordinatorHostErrorV1::ReceiptJournal
        });
    }
    Ok(())
}

fn digest_from_root_v1(root: &RootV1) -> Result<Digest, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    let bytes = risc0_digest_bytes_from_root_v1(root)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::MethodBinding)?;
    Ok(Digest::from(bytes))
}

fn image_root_from_words_v1(
    image_id: [u32; 8],
) -> Result<RootV1, ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    let digest = Digest::from(image_id);
    RootV1::parse(
        format!("0x{digest}"),
        "ZDEX tokenomics lane coordinator image root",
        false,
    )
    .map_err(|_| ZDEXTokenomicsLaneCoordinatorHostErrorV1::MethodBinding)
}

fn require_real_coordinator_method_v1() -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    if ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ELF.is_empty()
        || ZENODEX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_ID == [0; 8]
    {
        Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

fn require_development_mode_unset_v1(
    value: Option<&std::ffi::OsStr>,
) -> Result<(), ZDEXTokenomicsLaneCoordinatorHostErrorV1> {
    if development_mode_requested_v1(value) {
        return Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::DevelopmentModeConfigured);
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
    use super::{
        development_mode_requested_v1, digest_from_root_v1, image_root_from_words_v1,
        require_development_mode_unset_v1, ZDEXTokenomicsLaneCoordinatorHostErrorV1,
    };
    use risc0_zkvm::Digest;
    use std::ffi::OsStr;
    use zenodex_global_settlement_abi_v1::RootV1;

    #[test]
    fn root_and_risc0_digest_encodings_round_trip() {
        // Arrange
        let words = [
            0x0123_4567,
            0x89ab_cdef,
            0x1020_3040,
            0x5060_7080,
            0xa0b0_c0d0,
            0xe0f0_0102,
            0x0304_0506,
            0x0708_090a,
        ];
        let expected = Digest::from(words);

        // Act
        let root = image_root_from_words_v1(words).unwrap();
        let actual = digest_from_root_v1(&root).unwrap();

        // Assert
        assert_eq!(actual, expected);
        assert_eq!(root.as_str(), format!("0x{expected}"));
    }

    #[test]
    fn malformed_or_zero_image_roots_fail_closed() {
        // Arrange
        let zero = RootV1::parse(
            format!("0x{:064x}", 0),
            "ZDEX tokenomics test zero image",
            true,
        )
        .unwrap();

        // Act / Assert
        assert!(matches!(
            digest_from_root_v1(&zero),
            Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::MethodBinding)
        ));
    }

    #[test]
    fn development_mode_parser_matches_upstream_truthy_values() {
        // Arrange
        let truthy = ["1", "true", "TRUE", "yes", "YES"];
        let falsey = ["", "0", "false", "no", " true "];

        // Act / Assert
        for value in truthy {
            assert!(development_mode_requested_v1(Some(OsStr::new(value))));
        }
        for value in falsey {
            assert!(!development_mode_requested_v1(Some(OsStr::new(value))));
        }
        assert!(!development_mode_requested_v1(None));
    }

    #[test]
    fn configured_development_mode_is_a_typed_rejection() {
        // Arrange / Act / Assert
        assert!(matches!(
            require_development_mode_unset_v1(Some(OsStr::new("yes"))),
            Err(ZDEXTokenomicsLaneCoordinatorHostErrorV1::DevelopmentModeConfigured)
        ));
        assert!(require_development_mode_unset_v1(Some(OsStr::new("0"))).is_ok());
    }
}
