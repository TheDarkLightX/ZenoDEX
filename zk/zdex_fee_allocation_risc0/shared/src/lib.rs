use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, transition_zdex_fee_allocation_v1, ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1, ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationRejectCodeV1, ZDEXFeeAllocationResultV1, ZDEXFeeStateV1, MAX_JOURNAL_BYTES_V1,
};

pub const ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/zdex-fee-allocation-guest-input/v1";
pub const MAX_ZDEX_FEE_ALLOCATION_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_ZDEX_FEE_ALLOCATION_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationGuestInputV1 {
    pub schema: String,
    pub context: ZDEXFeeAllocationContextV1,
    pub pre_state: ZDEXFeeStateV1,
    pub policy: ZDEXFeeAllocationPolicyV1,
    pub command: ZDEXFeeAllocationCommandV1,
}

impl ZDEXFeeAllocationGuestInputV1 {
    pub fn validate(&self) -> Result<(), ZDEXFeeAllocationGuestErrorV1> {
        if self.schema != ZDEX_FEE_ALLOCATION_GUEST_INPUT_SCHEMA_V1 {
            return Err(ZDEXFeeAllocationGuestErrorV1::Schema);
        }
        self.context
            .validate()
            .map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
        self.pre_state
            .validate()
            .map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
        self.policy
            .validate()
            .map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ZDEXFeeAllocationGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    Abi,
    Rejected(ZDEXFeeAllocationRejectCodeV1),
    JournalTooLarge,
}

impl ZDEXFeeAllocationGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "ZDEX fee-allocation guest input is empty",
            Self::InputTooLarge => "ZDEX fee-allocation guest input exceeds release bound",
            Self::Decode => "ZDEX fee-allocation guest input decode failed",
            Self::NonCanonicalInput => "ZDEX fee-allocation guest input is noncanonical",
            Self::Schema => "ZDEX fee-allocation guest input schema is unsupported",
            Self::Abi => "ZDEX fee-allocation guest ABI validation failed",
            Self::Rejected(_) => "ZDEX fee-allocation economic transition rejected",
            Self::JournalTooLarge => "ZDEX fee-allocation journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for ZDEXFeeAllocationGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "ZDEX fee-allocation guest rejected: {self:?}")
    }
}

impl std::error::Error for ZDEXFeeAllocationGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedZDEXFeeAllocationV1 {
    pub input: ZDEXFeeAllocationGuestInputV1,
    pub accepted: ZDEXFeeAllocationAcceptedV1,
    pub journal_bytes: Vec<u8>,
}

pub fn canonical_zdex_fee_allocation_guest_input_bytes_v1(
    input: &ZDEXFeeAllocationGuestInputV1,
) -> Result<Vec<u8>, ZDEXFeeAllocationGuestErrorV1> {
    input.validate()?;
    let bytes = canonical_bytes_v1(input).map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_zdex_fee_allocation_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedZDEXFeeAllocationV1, ZDEXFeeAllocationGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: ZDEXFeeAllocationGuestInputV1 =
        serde_json::from_slice(input_bytes).map_err(|_| ZDEXFeeAllocationGuestErrorV1::Decode)?;
    let canonical = canonical_bytes_v1(&input).map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(ZDEXFeeAllocationGuestErrorV1::NonCanonicalInput);
    }
    prepare_zdex_fee_allocation_v1(input)
}

pub fn prepare_zdex_fee_allocation_v1(
    input: ZDEXFeeAllocationGuestInputV1,
) -> Result<PreparedZDEXFeeAllocationV1, ZDEXFeeAllocationGuestErrorV1> {
    input.validate()?;
    let result = transition_zdex_fee_allocation_v1(
        &input.context,
        &input.pre_state,
        &input.policy,
        &input.command,
    )
    .map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
    let accepted = match result {
        ZDEXFeeAllocationResultV1::Accepted(accepted) => *accepted,
        ZDEXFeeAllocationResultV1::Rejected(rejected) => {
            return Err(ZDEXFeeAllocationGuestErrorV1::Rejected(rejected.code));
        }
    };
    accepted
        .validate()
        .map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
    let journal_bytes =
        canonical_bytes_v1(&accepted.occurrence).map_err(|_| ZDEXFeeAllocationGuestErrorV1::Abi)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| ZDEXFeeAllocationGuestErrorV1::JournalTooLarge)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(ZDEXFeeAllocationGuestErrorV1::JournalTooLarge);
    }
    Ok(PreparedZDEXFeeAllocationV1 {
        input,
        accepted,
        journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), ZDEXFeeAllocationGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(ZDEXFeeAllocationGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ZDEX_FEE_ALLOCATION_GUEST_INPUT_BYTES_V1 {
        return Err(ZDEXFeeAllocationGuestErrorV1::InputTooLarge);
    }
    Ok(())
}
