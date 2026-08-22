//! Canonical input and exact target-row coverage for initial-state proving.
//!
//! This guest contract proves only the supplied public statement over the
//! explicit global-state tables. Private lane-root contents, predecessor-source
//! migration totality, and source-authorization legitimacy remain external
//! obligations.

use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, validate_economic_initial_state_explicit_row_count_v1,
    validate_economic_initial_state_statement_bindings_v1, EconomicInitialStateJournalV1,
    EconomicInitialStateSourceManifestV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1,
    GlobalEconomicStateV1, MAX_JOURNAL_BYTES_V1,
};

pub const ECONOMIC_INITIAL_STATE_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/economic-initial-state-guest-input/v1";
pub const MAX_ECONOMIC_INITIAL_STATE_GUEST_INPUT_BYTES_V1: usize = 8 * 1024 * 1024;
pub const MAX_ECONOMIC_INITIAL_STATE_GUEST_INPUT_BYTES_U32_V1: u32 = 8 * 1024 * 1024;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicInitialStateGuestInputV1 {
    pub schema: String,
    pub profile: EconomicProfileSnapshotV1,
    pub policy_registry: EconomicPolicyRegistryV1,
    pub state: GlobalEconomicStateV1,
    pub source_manifest: EconomicInitialStateSourceManifestV1,
    pub statement: EconomicInitialStateJournalV1,
}

impl EconomicInitialStateGuestInputV1 {
    pub fn validate(&self) -> Result<(), EconomicInitialStateGuestErrorV1> {
        if self.schema != ECONOMIC_INITIAL_STATE_GUEST_INPUT_SCHEMA_V1 {
            return Err(EconomicInitialStateGuestErrorV1::Schema);
        }
        validate_economic_initial_state_explicit_row_count_v1(&self.state)
            .map_err(|_| EconomicInitialStateGuestErrorV1::ExplicitRowCount)?;
        self.profile
            .validate()
            .map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
        self.policy_registry
            .validate()
            .map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
        self.state
            .validate()
            .map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
        self.source_manifest
            .validate()
            .map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
        self.statement
            .validate()
            .map_err(|_| EconomicInitialStateGuestErrorV1::Abi)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EconomicInitialStateGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    ExplicitRowCount,
    Abi,
    StatementBinding,
    JournalTooLarge,
}

impl EconomicInitialStateGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "economic initial-state guest input is empty",
            Self::InputTooLarge => "economic initial-state guest input exceeds release bound",
            Self::Decode => "economic initial-state guest input decode failed",
            Self::NonCanonicalInput => "economic initial-state guest input is noncanonical",
            Self::Schema => "economic initial-state guest input schema is unsupported",
            Self::ExplicitRowCount => {
                "economic initial-state explicit row count exceeds release bound"
            }
            Self::Abi => "economic initial-state guest ABI validation failed",
            Self::StatementBinding => "economic initial-state statement binding rejected",
            Self::JournalTooLarge => "economic initial-state journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for EconomicInitialStateGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "economic initial-state guest rejected: {self:?}")
    }
}

impl std::error::Error for EconomicInitialStateGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedEconomicInitialStateV1 {
    input: EconomicInitialStateGuestInputV1,
    journal_bytes: Vec<u8>,
}

impl PreparedEconomicInitialStateV1 {
    pub fn input(&self) -> &EconomicInitialStateGuestInputV1 {
        &self.input
    }

    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }

    pub fn revalidate(&self) -> Result<(), EconomicInitialStateGuestErrorV1> {
        let rebuilt = prepare_economic_initial_state_v1(self.input.clone())?;
        if rebuilt.journal_bytes != self.journal_bytes {
            return Err(EconomicInitialStateGuestErrorV1::StatementBinding);
        }
        Ok(())
    }
}

pub fn canonical_economic_initial_state_guest_input_bytes_v1(
    input: &EconomicInitialStateGuestInputV1,
) -> Result<Vec<u8>, EconomicInitialStateGuestErrorV1> {
    input.validate()?;
    let bytes = canonical_bytes_v1(input).map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_economic_initial_state_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedEconomicInitialStateV1, EconomicInitialStateGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: EconomicInitialStateGuestInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| EconomicInitialStateGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(EconomicInitialStateGuestErrorV1::NonCanonicalInput);
    }
    prepare_economic_initial_state_v1(input)
}

pub fn prepare_economic_initial_state_v1(
    input: EconomicInitialStateGuestInputV1,
) -> Result<PreparedEconomicInitialStateV1, EconomicInitialStateGuestErrorV1> {
    input.validate()?;
    validate_economic_initial_state_statement_bindings_v1(
        &input.profile,
        &input.policy_registry,
        &input.state,
        &input.source_manifest,
        &input.statement,
    )
    .map_err(|_| EconomicInitialStateGuestErrorV1::StatementBinding)?;
    let journal_bytes = input
        .statement
        .canonical_bytes()
        .map_err(|_| EconomicInitialStateGuestErrorV1::Abi)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| EconomicInitialStateGuestErrorV1::JournalTooLarge)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(EconomicInitialStateGuestErrorV1::JournalTooLarge);
    }
    Ok(PreparedEconomicInitialStateV1 {
        input,
        journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), EconomicInitialStateGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(EconomicInitialStateGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ECONOMIC_INITIAL_STATE_GUEST_INPUT_BYTES_V1 {
        return Err(EconomicInitialStateGuestErrorV1::InputTooLarge);
    }
    Ok(())
}
