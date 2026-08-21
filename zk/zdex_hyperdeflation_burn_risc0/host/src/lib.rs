use core::fmt;

use risc0_zkvm::{default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AbiResultV1, RootV1, ZDEXLaneSuccinctReceiptVerifierV1, MAX_JOURNAL_BYTES_V1,
};
use zenodex_zdex_hyperdeflation_burn_risc0_methods::{
    ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ELF, ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID,
};
use zenodex_zdex_hyperdeflation_burn_risc0_shared::{
    canonical_zdex_hyperdeflation_burn_guest_input_bytes_v1, prepare_zdex_hyperdeflation_burn_v1,
    PreparedZDEXHyperdeflationBurnV1, ZDEXHyperdeflationBurnGuestErrorV1,
    ZDEXHyperdeflationBurnGuestInputV1,
};

pub const MAX_ZDEX_HYPERDEFLATION_BURN_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub enum ZDEXHyperdeflationBurnHostErrorV1 {
    Guest(ZDEXHyperdeflationBurnGuestErrorV1),
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

impl fmt::Display for ZDEXHyperdeflationBurnHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "ZDEX hyperdeflation burn host rejected: {self:?}"
        )
    }
}

impl std::error::Error for ZDEXHyperdeflationBurnHostErrorV1 {}

impl From<ZDEXHyperdeflationBurnGuestErrorV1> for ZDEXHyperdeflationBurnHostErrorV1 {
    fn from(value: ZDEXHyperdeflationBurnGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

pub fn build_zdex_hyperdeflation_burn_executor_env_v1(
    input: &ZDEXHyperdeflationBurnGuestInputV1,
) -> Result<
    (ExecutorEnv<'static>, PreparedZDEXHyperdeflationBurnV1),
    ZDEXHyperdeflationBurnHostErrorV1,
> {
    let input_bytes = canonical_zdex_hyperdeflation_burn_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::InputTooLarge)?;
    let prepared = prepare_zdex_hyperdeflation_burn_v1(input.clone())?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    let env = builder
        .build()
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_zdex_hyperdeflation_burn_succinct_v1(
    input: &ZDEXHyperdeflationBurnGuestInputV1,
) -> Result<Receipt, ZDEXHyperdeflationBurnHostErrorV1> {
    require_zdex_hyperdeflation_burn_runtime_configuration_v1()?;
    require_real_method_v1()?;
    let (env, prepared) = build_zdex_hyperdeflation_burn_executor_env_v1(input)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::Proving)?;
    verify_zdex_hyperdeflation_burn_receipt_v1(&prove_info.receipt, &prepared.journal_bytes)?;
    Ok(prove_info.receipt)
}

pub fn verify_zdex_hyperdeflation_burn_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), ZDEXHyperdeflationBurnHostErrorV1> {
    require_zdex_hyperdeflation_burn_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(expected_journal_bytes)?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptJournal);
    }
    require_real_method_v1()?;
    receipt
        .verify(ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID)
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::ReceiptVerification)
}

pub fn zdex_hyperdeflation_burn_image_root_v1() -> Result<RootV1, ZDEXHyperdeflationBurnHostErrorV1>
{
    require_real_method_v1()?;
    image_root_from_words_v1(ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID)
}

fn image_root_from_words_v1(
    image_id: [u32; 8],
) -> Result<RootV1, ZDEXHyperdeflationBurnHostErrorV1> {
    let digest = Digest::from(image_id);
    RootV1::parse(
        format!("0x{digest}"),
        "ZDEX hyperdeflation burn image root",
        false,
    )
    .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::MethodBinding)
}

pub fn encode_zdex_hyperdeflation_burn_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, ZDEXHyperdeflationBurnHostErrorV1> {
    let receipt_bytes = serde_json::to_vec(receipt)
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::ReceiptEncoding)?;
    require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(receipt_bytes.len())?;
    Ok(receipt_bytes)
}

pub fn decode_canonical_zdex_hyperdeflation_burn_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, ZDEXHyperdeflationBurnHostErrorV1> {
    require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::ReceiptEncoding)?;
    let canonical = encode_zdex_hyperdeflation_burn_receipt_v1(&receipt)?;
    if canonical != receipt_bytes {
        return Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), ZDEXHyperdeflationBurnHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_ZDEX_HYPERDEFLATION_BURN_RECEIPT_BYTES_V1 {
        return Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub fn require_zdex_hyperdeflation_burn_runtime_configuration_v1(
) -> Result<(), ZDEXHyperdeflationBurnHostErrorV1> {
    // RISC0 3.0.6 panics when its disable-dev-mode feature is combined with a
    // truthy RISC0_DEV_MODE value. Convert that process abort into a typed,
    // fail-closed shell rejection before entering the dependency.
    let configured = std::env::var_os("RISC0_DEV_MODE");
    require_development_mode_unset_v1(configured.as_deref())
}

fn require_development_mode_unset_v1(
    value: Option<&std::ffi::OsStr>,
) -> Result<(), ZDEXHyperdeflationBurnHostErrorV1> {
    if development_mode_requested_v1(value) {
        return Err(ZDEXHyperdeflationBurnHostErrorV1::DevelopmentModeConfigured);
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

pub struct PinnedZDEXHyperdeflationBurnReceiptVerifierV1;

impl ZDEXLaneSuccinctReceiptVerifierV1 for PinnedZDEXHyperdeflationBurnReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()> {
        require_zdex_hyperdeflation_burn_receipt_bytes_len_v1(receipt_bytes.len()).map_err(
            |_| AbiErrorV1::InvalidBounds("ZDEX hyperdeflation burn RISC0 receipt bytes"),
        )?;
        require_expected_journal_bytes_v1(expected_journal_bytes).map_err(|_| {
            AbiErrorV1::InvalidBounds("ZDEX hyperdeflation burn RISC0 journal bytes")
        })?;
        let actual_image = zdex_hyperdeflation_burn_image_root_v1()
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX hyperdeflation burn RISC0 method"))?;
        if expected_image_id != &actual_image {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX hyperdeflation burn RISC0 image",
            ));
        }
        let receipt = decode_canonical_zdex_hyperdeflation_burn_receipt_v1(receipt_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX hyperdeflation burn receipt encoding"))?;
        verify_zdex_hyperdeflation_burn_receipt_v1(&receipt, expected_journal_bytes)
            .map_err(|_| AbiErrorV1::InvalidBinding("ZDEX hyperdeflation burn RISC0 receipt"))
    }
}

fn require_expected_journal_bytes_v1(
    expected_journal_bytes: &[u8],
) -> Result<(), ZDEXHyperdeflationBurnHostErrorV1> {
    let journal_len = u64::try_from(expected_journal_bytes.len())
        .map_err(|_| ZDEXHyperdeflationBurnHostErrorV1::ReceiptJournal)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptJournal);
    }
    Ok(())
}

fn require_real_method_v1() -> Result<(), ZDEXHyperdeflationBurnHostErrorV1> {
    if ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ELF.is_empty()
        || ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID == [0; 8]
    {
        Err(ZDEXHyperdeflationBurnHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        development_mode_requested_v1, image_root_from_words_v1, require_development_mode_unset_v1,
        ZDEXHyperdeflationBurnHostErrorV1,
    };
    use risc0_zkvm::Digest;
    use std::ffi::OsStr;

    #[test]
    fn image_root_uses_risc0_digest_encoding() {
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
        let expected = format!("0x{}", Digest::from(words));

        // Act
        let actual = image_root_from_words_v1(words).unwrap();

        // Assert
        assert_eq!(actual.as_str(), expected);
    }

    #[test]
    fn development_mode_parser_matches_the_upstream_truthy_values() {
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
            Err(ZDEXHyperdeflationBurnHostErrorV1::DevelopmentModeConfigured)
        ));
        assert!(require_development_mode_unset_v1(Some(OsStr::new("0"))).is_ok());
    }
}
