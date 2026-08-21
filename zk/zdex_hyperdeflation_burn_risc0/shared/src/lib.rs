use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, refine_zdex_burn_leaf_v1, transition_zdex_purchase_and_burn_v1, RootV1,
    ZDEXAMMPurchaseJournalV1, ZDEXBurnLeafProjectionV1, ZDEXBurnRejectCodeV1,
    ZDEXBurnRouteContextV1, ZDEXHyperdeflationPolicyV1, ZDEXPurchaseAndBurnCommandV1,
    ZDEXPurchaseAndBurnResultV1, ZDEXSupplyStateV1, MAX_JOURNAL_BYTES_V1,
};

pub const ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/zdex-hyperdeflation-burn-guest-input/v1";
pub const MAX_ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXHyperdeflationBurnGuestInputV1 {
    pub schema: String,
    pub policy: ZDEXHyperdeflationPolicyV1,
    pub pre_state: ZDEXSupplyStateV1,
    pub route_context: ZDEXBurnRouteContextV1,
    pub command: ZDEXPurchaseAndBurnCommandV1,
    pub purchase_journal: ZDEXAMMPurchaseJournalV1,
    pub tokenomics_module_release_id: RootV1,
}

impl ZDEXHyperdeflationBurnGuestInputV1 {
    pub fn validate(&self) -> Result<(), ZDEXHyperdeflationBurnGuestErrorV1> {
        if self.schema != ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_SCHEMA_V1 {
            return Err(ZDEXHyperdeflationBurnGuestErrorV1::Schema);
        }
        self.policy
            .validate()
            .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
        self.pre_state
            .validate()
            .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
        self.route_context
            .validate()
            .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
        self.command
            .validate()
            .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
        self.purchase_journal
            .validate()
            .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
        self.tokenomics_module_release_id
            .validate("ZDEX burn guest tokenomics release id", false)
            .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ZDEXHyperdeflationBurnGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    Abi,
    Rejected(ZDEXBurnRejectCodeV1),
    Refinement,
    JournalTooLarge,
}

impl ZDEXHyperdeflationBurnGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "ZDEX burn guest input is empty",
            Self::InputTooLarge => "ZDEX burn guest input exceeds release bound",
            Self::Decode => "ZDEX burn guest input decode failed",
            Self::NonCanonicalInput => "ZDEX burn guest input is noncanonical",
            Self::Schema => "ZDEX burn guest input schema is unsupported",
            Self::Abi => "ZDEX burn guest ABI validation failed",
            Self::Rejected(_) => "ZDEX burn economic transition rejected",
            Self::Refinement => "ZDEX burn route refinement rejected",
            Self::JournalTooLarge => "ZDEX burn journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for ZDEXHyperdeflationBurnGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "ZDEX burn guest rejected: {self:?}")
    }
}

impl std::error::Error for ZDEXHyperdeflationBurnGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedZDEXHyperdeflationBurnV1 {
    pub input: ZDEXHyperdeflationBurnGuestInputV1,
    pub projection: ZDEXBurnLeafProjectionV1,
    pub journal_bytes: Vec<u8>,
}

pub fn canonical_zdex_hyperdeflation_burn_guest_input_bytes_v1(
    input: &ZDEXHyperdeflationBurnGuestInputV1,
) -> Result<Vec<u8>, ZDEXHyperdeflationBurnGuestErrorV1> {
    input.validate()?;
    let bytes = canonical_bytes_v1(input).map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_zdex_hyperdeflation_burn_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedZDEXHyperdeflationBurnV1, ZDEXHyperdeflationBurnGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: ZDEXHyperdeflationBurnGuestInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(ZDEXHyperdeflationBurnGuestErrorV1::NonCanonicalInput);
    }
    prepare_zdex_hyperdeflation_burn_v1(input)
}

pub fn prepare_zdex_hyperdeflation_burn_v1(
    input: ZDEXHyperdeflationBurnGuestInputV1,
) -> Result<PreparedZDEXHyperdeflationBurnV1, ZDEXHyperdeflationBurnGuestErrorV1> {
    input.validate()?;
    let result = transition_zdex_purchase_and_burn_v1(
        &input.policy,
        &input.pre_state,
        &input.route_context,
        &input.command,
    )
    .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
    let accepted = match result {
        ZDEXPurchaseAndBurnResultV1::Accepted(accepted) => *accepted,
        ZDEXPurchaseAndBurnResultV1::Rejected(rejected) => {
            return Err(ZDEXHyperdeflationBurnGuestErrorV1::Rejected(
                rejected.code(),
            ));
        }
    };
    accepted
        .validate()
        .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
    let projection = refine_zdex_burn_leaf_v1(
        &accepted,
        &input.purchase_journal,
        &input.tokenomics_module_release_id,
    )
    .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Refinement)?;
    projection
        .validate()
        .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Refinement)?;
    let journal_bytes = canonical_bytes_v1(projection.journal())
        .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::Abi)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| ZDEXHyperdeflationBurnGuestErrorV1::JournalTooLarge)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(ZDEXHyperdeflationBurnGuestErrorV1::JournalTooLarge);
    }
    Ok(PreparedZDEXHyperdeflationBurnV1 {
        input,
        projection,
        journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), ZDEXHyperdeflationBurnGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(ZDEXHyperdeflationBurnGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_BYTES_V1 {
        return Err(ZDEXHyperdeflationBurnGuestErrorV1::InputTooLarge);
    }
    Ok(())
}
