use core::fmt;

use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, transition_perps_margin_lane_module_v1, PerpsMarginAcceptedV1,
    PerpsMarginLaneModuleInputV1, PerpsMarginRejectCodeV1, PerpsMarginResultV1,
    MAX_JOURNAL_BYTES_V1,
};

pub const MAX_PERPS_MARGIN_MODULE_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_PERPS_MARGIN_MODULE_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginModuleGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Abi,
    Rejected(PerpsMarginRejectCodeV1),
    JournalTooLarge,
}

impl PerpsMarginModuleGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "perps margin module guest input is empty",
            Self::InputTooLarge => "perps margin module guest input exceeds release bound",
            Self::Decode => "perps margin module guest input decode failed",
            Self::NonCanonicalInput => "perps margin module guest input is noncanonical",
            Self::Abi => "perps margin module guest ABI validation failed",
            Self::Rejected(_) => "perps margin economic transition rejected",
            Self::JournalTooLarge => "perps margin module journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for PerpsMarginModuleGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "perps margin module guest rejected: {self:?}")
    }
}

impl std::error::Error for PerpsMarginModuleGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedPerpsMarginModuleV1 {
    pub input: PerpsMarginLaneModuleInputV1,
    pub accepted: PerpsMarginAcceptedV1,
    pub journal_bytes: Vec<u8>,
}

pub fn canonical_perps_margin_module_guest_input_bytes_v1(
    input: &PerpsMarginLaneModuleInputV1,
) -> Result<Vec<u8>, PerpsMarginModuleGuestErrorV1> {
    input
        .validate()
        .map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    let bytes = canonical_bytes_v1(input).map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_perps_margin_module_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedPerpsMarginModuleV1, PerpsMarginModuleGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: PerpsMarginLaneModuleInputV1 =
        serde_json::from_slice(input_bytes).map_err(|_| PerpsMarginModuleGuestErrorV1::Decode)?;
    let canonical = canonical_bytes_v1(&input).map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(PerpsMarginModuleGuestErrorV1::NonCanonicalInput);
    }
    prepare_perps_margin_module_v1(input)
}

pub fn prepare_perps_margin_module_v1(
    input: PerpsMarginLaneModuleInputV1,
) -> Result<PreparedPerpsMarginModuleV1, PerpsMarginModuleGuestErrorV1> {
    input
        .validate()
        .map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    let result = transition_perps_margin_lane_module_v1(&input)
        .map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    let accepted = match result {
        PerpsMarginResultV1::Accepted(accepted) => *accepted,
        PerpsMarginResultV1::Rejected(rejected) => {
            return Err(PerpsMarginModuleGuestErrorV1::Rejected(rejected.code));
        }
    };
    accepted
        .validate()
        .map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    let journal_bytes = canonical_bytes_v1(&accepted.module_journal)
        .map_err(|_| PerpsMarginModuleGuestErrorV1::Abi)?;
    validate_journal_size_v1(&journal_bytes)?;
    Ok(PreparedPerpsMarginModuleV1 {
        input,
        accepted,
        journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), PerpsMarginModuleGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(PerpsMarginModuleGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_PERPS_MARGIN_MODULE_GUEST_INPUT_BYTES_V1 {
        return Err(PerpsMarginModuleGuestErrorV1::InputTooLarge);
    }
    Ok(())
}

fn validate_journal_size_v1(journal_bytes: &[u8]) -> Result<(), PerpsMarginModuleGuestErrorV1> {
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| PerpsMarginModuleGuestErrorV1::JournalTooLarge)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(PerpsMarginModuleGuestErrorV1::JournalTooLarge);
    }
    Ok(())
}
