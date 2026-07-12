use core::fmt;

use super::hash::canonical_asset_name;
use super::{SemanticEpochErrorV1, ZrpfErrorV3};

#[derive(Clone, Debug, PartialEq, Eq)]
/// Stable fail-closed errors for the pure Spot represented-value reference kernel.
pub enum SpotSemanticValueErrorV1 {
    EmptyLeaves,
    TooManyLeaves {
        actual: usize,
        maximum: usize,
    },
    OpeningCountMismatch,
    BaseProposalMismatch,
    EpochRangeUnsupported,
    PublicPolicyMismatch,
    AuthorityGrantPolicyMismatch,
    ClosedScopeMismatch,
    InvalidPublicPolicyHash,
    InvalidLaneId,
    MixedLaneId {
        ordinal: usize,
    },
    ZeroStateRoot {
        ordinal: usize,
    },
    NonChangingValueState {
        ordinal: usize,
    },
    StateCommitmentMismatch {
        ordinal: usize,
        side: &'static str,
    },
    StateDiscontinuity {
        ordinal: usize,
    },
    DuplicateTransactionRoot {
        ordinal: usize,
    },
    TooManyRows {
        ordinal: usize,
        actual: usize,
        maximum: usize,
    },
    TooManyRepresentedRows {
        actual: usize,
        maximum: usize,
    },
    AssetRowsNotCanonical {
        ordinal: usize,
    },
    AssetRowsRootMismatch {
        ordinal: usize,
    },
    NonCanonicalAssetId {
        ordinal: usize,
        row: usize,
    },
    ZeroAssetRow {
        ordinal: usize,
        row: usize,
    },
    SupplyRowCombinesMintAndBurn {
        ordinal: usize,
        row: usize,
    },
    OrdinaryRowHasAuthority {
        ordinal: usize,
        row: usize,
    },
    MintRowShapeInvalid {
        ordinal: usize,
        row: usize,
    },
    BurnUnsupported {
        ordinal: usize,
        row: usize,
    },
    MissingMintGrant {
        ordinal: usize,
        row: usize,
    },
    MintAuthorityMismatch {
        ordinal: usize,
        row: usize,
    },
    MintCapExceeded {
        ordinal: usize,
        row: usize,
    },
    EmptyRepresentedRows,
    AssetImbalance {
        asset_id: [u8; 32],
    },
    InvalidGrant,
    NonCanonicalGrantOrder,
    TooManyGrants {
        actual: usize,
        maximum: usize,
    },
    NonCanonicalSubtreeLeaves,
    SubtreeScopeMismatch {
        ordinal: usize,
    },
    DuplicateSubtreeIdentity {
        field: &'static str,
    },
    NonZeroOriginClosedEpoch,
    ArithmeticOverflow(&'static str),
    LegacyDerivation(&'static str),
    Protocol(SemanticEpochErrorV1),
    Structural(ZrpfErrorV3),
}

impl fmt::Display for SpotSemanticValueErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyLeaves => formatter.write_str("spot value epoch has no leaves"),
            Self::TooManyLeaves { actual, maximum } => {
                write!(
                    formatter,
                    "spot value leaf count {actual} exceeds {maximum}"
                )
            }
            Self::OpeningCountMismatch => {
                formatter.write_str("spot value leaf/opening counts differ")
            }
            Self::BaseProposalMismatch => {
                formatter.write_str("spot value leaves do not recompose the base semantic proposal")
            }
            Self::EpochRangeUnsupported => {
                formatter.write_str("spot value profile requires one exact epoch")
            }
            Self::PublicPolicyMismatch => {
                formatter.write_str("spot value policy differs from the authenticated scope")
            }
            Self::AuthorityGrantPolicyMismatch => {
                formatter.write_str("spot value closed-root grant policy differs from its subtree")
            }
            Self::ClosedScopeMismatch => {
                formatter.write_str("spot value closed-root scope differs from its subtree")
            }
            Self::InvalidPublicPolicyHash => {
                formatter.write_str("spot value public policy hash is zero")
            }
            Self::InvalidLaneId => formatter.write_str("spot value lane ID is invalid"),
            Self::MixedLaneId { ordinal } => {
                write!(formatter, "spot value leaf {ordinal} uses a different lane")
            }
            Self::ZeroStateRoot { ordinal } => {
                write!(formatter, "spot value leaf {ordinal} has a zero state root")
            }
            Self::NonChangingValueState { ordinal } => {
                write!(
                    formatter,
                    "spot value leaf {ordinal} has rows but no state-root change"
                )
            }
            Self::StateCommitmentMismatch { ordinal, side } => {
                write!(
                    formatter,
                    "spot value leaf {ordinal} {side} state opening mismatches"
                )
            }
            Self::StateDiscontinuity { ordinal } => {
                write!(
                    formatter,
                    "spot value leaf {ordinal} does not continue prior state"
                )
            }
            Self::DuplicateTransactionRoot { ordinal } => {
                write!(
                    formatter,
                    "spot value leaf {ordinal} repeats a transaction root"
                )
            }
            Self::TooManyRows {
                ordinal,
                actual,
                maximum,
            } => write!(
                formatter,
                "spot value leaf {ordinal} row count {actual} exceeds {maximum}"
            ),
            Self::TooManyRepresentedRows { actual, maximum } => {
                write!(
                    formatter,
                    "spot value summary row count {actual} exceeds {maximum}"
                )
            }
            Self::AssetRowsNotCanonical { ordinal } => {
                write!(
                    formatter,
                    "spot value leaf {ordinal} rows are not canonical legacy rows"
                )
            }
            Self::AssetRowsRootMismatch { ordinal } => {
                write!(
                    formatter,
                    "spot value leaf {ordinal} asset-row root mismatches"
                )
            }
            Self::NonCanonicalAssetId { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} has a noncanonical asset ID"
                )
            }
            Self::ZeroAssetRow { ordinal, row } => {
                write!(formatter, "spot value row {ordinal}:{row} is all zero")
            }
            Self::SupplyRowCombinesMintAndBurn { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} combines mint and burn"
                )
            }
            Self::OrdinaryRowHasAuthority { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} has an unexpected authority"
                )
            }
            Self::MintRowShapeInvalid { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} has an invalid mint shape"
                )
            }
            Self::BurnUnsupported { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} uses unsupported burn semantics"
                )
            }
            Self::MissingMintGrant { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} has no governed mint grant"
                )
            }
            Self::MintAuthorityMismatch { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} mint authority mismatches"
                )
            }
            Self::MintCapExceeded { ordinal, row } => {
                write!(
                    formatter,
                    "spot value row {ordinal}:{row} exceeds its closed-root mint cap"
                )
            }
            Self::EmptyRepresentedRows => {
                formatter.write_str("spot value epoch contains no represented external-effect rows")
            }
            Self::AssetImbalance { asset_id } => {
                write!(
                    formatter,
                    "spot value asset {} is imbalanced",
                    AssetHex(*asset_id)
                )
            }
            Self::InvalidGrant => formatter.write_str("spot value mint grant is invalid"),
            Self::NonCanonicalGrantOrder => {
                formatter.write_str("spot value mint grants are not sorted unique")
            }
            Self::TooManyGrants { actual, maximum } => {
                write!(
                    formatter,
                    "spot value grant count {actual} exceeds {maximum}"
                )
            }
            Self::NonCanonicalSubtreeLeaves => {
                formatter.write_str("spot value subtree leaves are not dense and canonical")
            }
            Self::SubtreeScopeMismatch { ordinal } => {
                write!(
                    formatter,
                    "spot value subtree leaf {ordinal} has a different scope"
                )
            }
            Self::DuplicateSubtreeIdentity { field } => {
                write!(formatter, "spot value subtree repeats {field}")
            }
            Self::NonZeroOriginClosedEpoch => {
                formatter.write_str("closed spot value epoch must start at ordinal zero")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "spot value overflow: {field}"),
            Self::LegacyDerivation(field) => {
                write!(formatter, "spot value legacy derivation failed: {field}")
            }
            Self::Protocol(error) => write!(formatter, "semantic proposal rejected: {error}"),
            Self::Structural(error) => write!(formatter, "ZRPF commitment rejected: {error}"),
        }
    }
}

struct AssetHex([u8; 32]);

impl fmt::Display for AssetHex {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&canonical_asset_name(self.0))
    }
}
