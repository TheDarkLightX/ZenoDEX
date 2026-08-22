use core::fmt;

use risc0_zkvm::{default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use zenodex_economic_initial_state_risc0_methods::{
    ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ELF, ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID,
};
use zenodex_economic_initial_state_risc0_shared::{
    canonical_economic_initial_state_guest_input_bytes_v1, prepare_economic_initial_state_v1,
    EconomicInitialStateGuestErrorV1, EconomicInitialStateGuestInputV1,
    PreparedEconomicInitialStateV1,
};
use zenodex_global_settlement_abi_v1::{
    hash_bytes_sha256_v1, EconomicInitialStateCertificateV1, EconomicInitialStateJournalV1,
    ReceiptKindV1, RootV1, MAX_CYCLE_BUDGET_V1, MAX_JOURNAL_BYTES_V1,
};

pub const MAX_ECONOMIC_INITIAL_STATE_RECEIPT_BYTES_V1: usize = 16 * 1024 * 1024;

#[derive(Debug)]
pub enum EconomicInitialStateHostErrorV1 {
    Guest(EconomicInitialStateGuestErrorV1),
    InputTooLarge,
    DevelopmentModeConfigured,
    PlaceholderMethod,
    Environment,
    Proving,
    ReceiptKind,
    ReceiptJournal,
    JournalEncoding,
    JournalNonCanonical,
    ReceiptVerification,
    ReceiptEncoding,
    ReceiptNonCanonical,
    ReceiptSize,
    MethodBinding,
    Certificate,
}

impl fmt::Display for EconomicInitialStateHostErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "economic initial-state host rejected: {self:?}")
    }
}

impl std::error::Error for EconomicInitialStateHostErrorV1 {}

impl From<EconomicInitialStateGuestErrorV1> for EconomicInitialStateHostErrorV1 {
    fn from(value: EconomicInitialStateGuestErrorV1) -> Self {
        Self::Guest(value)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedEconomicInitialStateV1 {
    pub certificate: EconomicInitialStateCertificateV1,
    pub receipt_bytes: Vec<u8>,
}

/// Host-observed execution diagnostics. These values carry no receipt authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EconomicInitialStateProofMetricsV1 {
    pub segments: usize,
    pub total_cycles: u64,
    pub user_cycles: u64,
    pub paging_cycles: u64,
    pub reserved_cycles: u64,
}

/// A receipt already checked by the host, paired with non-authoritative diagnostics.
#[derive(Clone, Debug)]
#[must_use]
pub struct ProvedEconomicInitialStateV1 {
    receipt: Receipt,
    metrics: EconomicInitialStateProofMetricsV1,
}

impl ProvedEconomicInitialStateV1 {
    pub fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn metrics(&self) -> &EconomicInitialStateProofMetricsV1 {
        &self.metrics
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

pub fn build_economic_initial_state_executor_env_v1(
    input: &EconomicInitialStateGuestInputV1,
) -> Result<(ExecutorEnv<'static>, PreparedEconomicInitialStateV1), EconomicInitialStateHostErrorV1>
{
    let input_bytes = canonical_economic_initial_state_guest_input_bytes_v1(input)?;
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| EconomicInitialStateHostErrorV1::InputTooLarge)?;
    let prepared = prepare_economic_initial_state_v1(input.clone())?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]);
    builder.write_slice(&input_bytes);
    let env = builder
        .build()
        .map_err(|_| EconomicInitialStateHostErrorV1::Environment)?;
    Ok((env, prepared))
}

pub fn prove_economic_initial_state_succinct_v1(
    input: &EconomicInitialStateGuestInputV1,
) -> Result<Receipt, EconomicInitialStateHostErrorV1> {
    Ok(prove_economic_initial_state_succinct_with_metrics_v1(input)?.into_receipt())
}

pub fn prove_economic_initial_state_succinct_with_metrics_v1(
    input: &EconomicInitialStateGuestInputV1,
) -> Result<ProvedEconomicInitialStateV1, EconomicInitialStateHostErrorV1> {
    require_economic_initial_state_runtime_configuration_v1()?;
    require_input_method_binding_v1(input)?;
    let (env, prepared) = build_economic_initial_state_executor_env_v1(input)?;
    let prove_info = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|_| EconomicInitialStateHostErrorV1::Proving)?;
    verify_economic_initial_state_receipt_v1(&prove_info.receipt, prepared.journal_bytes())?;
    let metrics = EconomicInitialStateProofMetricsV1 {
        segments: prove_info.stats.segments,
        total_cycles: prove_info.stats.total_cycles,
        user_cycles: prove_info.stats.user_cycles,
        paging_cycles: prove_info.stats.paging_cycles,
        reserved_cycles: prove_info.stats.reserved_cycles,
    };
    Ok(ProvedEconomicInitialStateV1 {
        receipt: prove_info.receipt,
        metrics,
    })
}

pub fn verify_economic_initial_state_receipt_v1(
    receipt: &Receipt,
    expected_journal_bytes: &[u8],
) -> Result<(), EconomicInitialStateHostErrorV1> {
    require_economic_initial_state_runtime_configuration_v1()?;
    require_expected_journal_bytes_v1(expected_journal_bytes)?;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(EconomicInitialStateHostErrorV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_journal_bytes {
        return Err(EconomicInitialStateHostErrorV1::ReceiptJournal);
    }
    let journal = decode_canonical_economic_initial_state_journal_v1(expected_journal_bytes)?;
    let actual_image = economic_initial_state_image_root_v1()?;
    if journal.root_image_id != actual_image {
        return Err(EconomicInitialStateHostErrorV1::MethodBinding);
    }
    receipt
        .verify(ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID)
        .map_err(|_| EconomicInitialStateHostErrorV1::ReceiptVerification)
}

pub fn decode_canonical_economic_initial_state_journal_v1(
    journal_bytes: &[u8],
) -> Result<EconomicInitialStateJournalV1, EconomicInitialStateHostErrorV1> {
    require_expected_journal_bytes_v1(journal_bytes)?;
    let journal: EconomicInitialStateJournalV1 = serde_json::from_slice(journal_bytes)
        .map_err(|_| EconomicInitialStateHostErrorV1::JournalEncoding)?;
    let canonical = journal
        .canonical_bytes()
        .map_err(|_| EconomicInitialStateHostErrorV1::JournalEncoding)?;
    if canonical != journal_bytes {
        return Err(EconomicInitialStateHostErrorV1::JournalNonCanonical);
    }
    Ok(journal)
}

pub fn economic_initial_state_image_root_v1() -> Result<RootV1, EconomicInitialStateHostErrorV1> {
    require_real_method_v1()?;
    image_root_from_words_v1(ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID)
}

fn image_root_from_words_v1(image_id: [u32; 8]) -> Result<RootV1, EconomicInitialStateHostErrorV1> {
    let digest = Digest::from(image_id);
    RootV1::parse(
        format!("0x{digest}"),
        "economic initial-state image root",
        false,
    )
    .map_err(|_| EconomicInitialStateHostErrorV1::MethodBinding)
}

pub fn encode_economic_initial_state_receipt_v1(
    receipt: &Receipt,
) -> Result<Vec<u8>, EconomicInitialStateHostErrorV1> {
    let receipt_bytes = serde_json::to_vec(receipt)
        .map_err(|_| EconomicInitialStateHostErrorV1::ReceiptEncoding)?;
    require_economic_initial_state_receipt_bytes_len_v1(receipt_bytes.len())?;
    Ok(receipt_bytes)
}

pub fn decode_canonical_economic_initial_state_receipt_v1(
    receipt_bytes: &[u8],
) -> Result<Receipt, EconomicInitialStateHostErrorV1> {
    require_economic_initial_state_receipt_bytes_len_v1(receipt_bytes.len())?;
    let receipt: Receipt = serde_json::from_slice(receipt_bytes)
        .map_err(|_| EconomicInitialStateHostErrorV1::ReceiptEncoding)?;
    let canonical = encode_economic_initial_state_receipt_v1(&receipt)?;
    if canonical != receipt_bytes {
        return Err(EconomicInitialStateHostErrorV1::ReceiptNonCanonical);
    }
    Ok(receipt)
}

pub fn certify_economic_initial_state_receipt_v1(
    prepared: &PreparedEconomicInitialStateV1,
    receipt: &Receipt,
    release_cycle_budget: u64,
) -> Result<CertifiedEconomicInitialStateV1, EconomicInitialStateHostErrorV1> {
    if release_cycle_budget == 0 || release_cycle_budget > MAX_CYCLE_BUDGET_V1 {
        return Err(EconomicInitialStateHostErrorV1::Certificate);
    }
    prepared
        .revalidate()
        .map_err(EconomicInitialStateHostErrorV1::Guest)?;
    require_input_method_binding_v1(prepared.input())?;
    verify_economic_initial_state_receipt_v1(receipt, prepared.journal_bytes())?;
    let receipt_bytes = encode_economic_initial_state_receipt_v1(receipt)?;
    let statement = &prepared.input().statement;
    let receipt_root = RootV1::parse(
        format!("0x{}", hash_bytes_sha256_v1(&receipt_bytes)),
        "economic initial-state receipt root",
        false,
    )
    .map_err(|_| EconomicInitialStateHostErrorV1::Certificate)?;
    let journal_bytes = u64::try_from(prepared.journal_bytes().len())
        .map_err(|_| EconomicInitialStateHostErrorV1::Certificate)?;
    let certificate = EconomicInitialStateCertificateV1 {
        schema: statement.schema.clone(),
        kind: statement.kind,
        chain_id: statement.chain_id.clone(),
        deployment_root: statement.deployment_root.clone(),
        profile_root: statement.profile_root.clone(),
        writer_epoch: statement.writer_epoch,
        height: statement.height,
        state_root: statement.state_root.clone(),
        source_profile_root: statement.source_profile_root.clone(),
        source_state_root: statement.source_state_root.clone(),
        source_writer_epoch: statement.source_writer_epoch,
        source_height: statement.source_height,
        state_atom_coverage_root: statement.state_atom_coverage_root.clone(),
        lane_object_coverage_root: statement.lane_object_coverage_root.clone(),
        replay_continuity_root: statement.replay_continuity_root.clone(),
        terminal_continuity_root: statement.terminal_continuity_root.clone(),
        outbox_continuity_root: statement.outbox_continuity_root.clone(),
        source_manifest_root: statement.source_manifest_root.clone(),
        toolchain_manifest_root: statement.toolchain_manifest_root.clone(),
        root_image_id: statement.root_image_id.clone(),
        receipt_root,
        receipt_kind: ReceiptKindV1::SUCCINCT,
        journal_bytes,
        cycle_budget: release_cycle_budget,
    };
    certificate
        .validate()
        .map_err(|_| EconomicInitialStateHostErrorV1::Certificate)?;
    Ok(CertifiedEconomicInitialStateV1 {
        certificate,
        receipt_bytes,
    })
}

pub fn require_economic_initial_state_receipt_bytes_len_v1(
    receipt_len: usize,
) -> Result<(), EconomicInitialStateHostErrorV1> {
    if receipt_len == 0 || receipt_len > MAX_ECONOMIC_INITIAL_STATE_RECEIPT_BYTES_V1 {
        return Err(EconomicInitialStateHostErrorV1::ReceiptSize);
    }
    Ok(())
}

pub fn require_economic_initial_state_runtime_configuration_v1(
) -> Result<(), EconomicInitialStateHostErrorV1> {
    let configured = std::env::var_os("RISC0_DEV_MODE");
    require_development_mode_unset_v1(configured.as_deref())
}

fn require_development_mode_unset_v1(
    value: Option<&std::ffi::OsStr>,
) -> Result<(), EconomicInitialStateHostErrorV1> {
    if development_mode_requested_v1(value) {
        return Err(EconomicInitialStateHostErrorV1::DevelopmentModeConfigured);
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

fn require_input_method_binding_v1(
    input: &EconomicInitialStateGuestInputV1,
) -> Result<(), EconomicInitialStateHostErrorV1> {
    let actual_image = economic_initial_state_image_root_v1()?;
    require_method_root_bindings_v1(
        &actual_image,
        &input.profile.root_image_id,
        &input.statement.root_image_id,
    )
}

fn require_method_root_bindings_v1(
    actual_image: &RootV1,
    profile_image: &RootV1,
    statement_image: &RootV1,
) -> Result<(), EconomicInitialStateHostErrorV1> {
    if profile_image != actual_image || statement_image != actual_image {
        return Err(EconomicInitialStateHostErrorV1::MethodBinding);
    }
    Ok(())
}

fn require_expected_journal_bytes_v1(
    expected_journal_bytes: &[u8],
) -> Result<(), EconomicInitialStateHostErrorV1> {
    let journal_len = u64::try_from(expected_journal_bytes.len())
        .map_err(|_| EconomicInitialStateHostErrorV1::ReceiptJournal)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(EconomicInitialStateHostErrorV1::ReceiptJournal);
    }
    Ok(())
}

fn require_real_method_v1() -> Result<(), EconomicInitialStateHostErrorV1> {
    require_method_values_v1(
        ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ELF,
        ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID,
    )
}

fn require_method_values_v1(
    elf: &[u8],
    image_id: [u32; 8],
) -> Result<(), EconomicInitialStateHostErrorV1> {
    if elf.is_empty() || image_id == [0; 8] {
        Err(EconomicInitialStateHostErrorV1::PlaceholderMethod)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        development_mode_requested_v1, image_root_from_words_v1, require_development_mode_unset_v1,
        require_method_root_bindings_v1, require_method_values_v1, EconomicInitialStateHostErrorV1,
    };
    use risc0_zkvm::Digest;
    use std::ffi::OsStr;
    use zenodex_global_settlement_abi_v1::RootV1;

    fn root(value: u64) -> RootV1 {
        RootV1::parse(format!("0x{value:064x}"), "host test root", false).unwrap()
    }

    #[test]
    fn image_root_uses_risc0_digest_encoding() {
        let words = [1, 2, 3, 4, 5, 6, 7, 8];
        let expected = format!("0x{}", Digest::from(words));

        let actual = image_root_from_words_v1(words).unwrap();

        assert_eq!(actual.as_str(), expected);
    }

    #[test]
    fn configured_development_mode_is_a_typed_rejection() {
        assert!(development_mode_requested_v1(Some(OsStr::new("YES"))));
        assert!(!development_mode_requested_v1(Some(OsStr::new("0"))));
        assert!(matches!(
            require_development_mode_unset_v1(Some(OsStr::new("true"))),
            Err(EconomicInitialStateHostErrorV1::DevelopmentModeConfigured)
        ));
    }

    #[test]
    fn placeholder_method_never_verifies_or_proves() {
        assert!(matches!(
            require_method_values_v1(&[], [0; 8]),
            Err(EconomicInitialStateHostErrorV1::PlaceholderMethod)
        ));
        assert!(require_method_values_v1(&[1], [1; 8]).is_ok());
    }

    #[test]
    fn profile_and_statement_must_name_the_exact_measured_image() {
        let actual = root(1);

        assert!(require_method_root_bindings_v1(&actual, &actual, &actual).is_ok());
        assert!(matches!(
            require_method_root_bindings_v1(&actual, &root(2), &actual),
            Err(EconomicInitialStateHostErrorV1::MethodBinding)
        ));
        assert!(matches!(
            require_method_root_bindings_v1(&actual, &actual, &root(3)),
            Err(EconomicInitialStateHostErrorV1::MethodBinding)
        ));
    }
}
