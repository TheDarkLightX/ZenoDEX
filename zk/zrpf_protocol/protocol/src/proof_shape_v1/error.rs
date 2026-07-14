use core::fmt;

use super::{AssumptionIdV1, ProofShapeIdV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofShapeErrorV1 {
    InvalidVersion {
        field: &'static str,
        actual: u16,
    },
    ZeroIdentifier(&'static str),
    InvalidDerivedIdentity(&'static str),
    InvalidResourceCeiling(&'static str),
    InvalidChildJournalByteLimit,
    TooManyAllowedChildBindings {
        actual: usize,
        maximum: usize,
    },
    DuplicateAllowedChildBinding,
    NonCanonicalAllowedChildBindingOrder,
    LeafHasChildContract,
    AggregateHasNoChildContract,
    TooManyRequiredAssumptions {
        actual: usize,
        maximum: usize,
    },
    DuplicateAssumptionSlot,
    DuplicateExpectedVerificationClaim,
    DuplicateExpectedChildJournal,
    NonDenseAssumptionSlots,
    NonCanonicalAssumptionOrder,
    ProofShapeMismatch {
        expected: ProofShapeIdV1,
        actual: ProofShapeIdV1,
    },
    AssumptionCountCeilingExceeded {
        actual: usize,
        maximum: usize,
    },
    RequiredBindingNotAllowed,
    TotalChildJournalCeilingExceeded {
        actual: u64,
        maximum: u64,
    },
    InvalidResolvedChildJournalBytes,
    TooManyResolvedClaims {
        actual: usize,
        maximum: usize,
    },
    DuplicateResolvedAssumption,
    DuplicateVerificationClaim,
    DuplicateResolvedChildJournal,
    SurplusResolvedClaim {
        assumption_id: AssumptionIdV1,
    },
    UnresolvedAssumption {
        slot: u16,
    },
    ChildShapeMismatch,
    ChildProgramMismatch,
    ChildProfileMismatch,
    VerificationClaimMismatch,
    ChildJournalMismatch,
    ChildJournalBytesExceeded {
        actual: u64,
        maximum: u64,
    },
    EmptyRegistry,
    TooManyRegistryEntries {
        actual: usize,
        maximum: usize,
    },
    DuplicateProofShape,
    NonCanonicalRegistryOrder,
    DuplicateAssumptionManifest,
    UnknownAssumptionManifest,
    ArithmeticOverflow(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for ProofShapeErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion { field, actual } => {
                write!(formatter, "invalid {field} version: {actual}")
            }
            Self::ZeroIdentifier(field) => write!(formatter, "zero identifier: {field}"),
            Self::InvalidDerivedIdentity(field) => {
                write!(formatter, "derived identity mismatch: {field}")
            }
            Self::InvalidResourceCeiling(field) => {
                write!(formatter, "invalid resource ceiling: {field}")
            }
            Self::InvalidChildJournalByteLimit => {
                formatter.write_str("invalid child journal byte limit")
            }
            Self::TooManyAllowedChildBindings { actual, maximum } => {
                write!(
                    formatter,
                    "allowed child binding count {actual} exceeds {maximum}"
                )
            }
            Self::DuplicateAllowedChildBinding => {
                formatter.write_str("duplicate allowed child binding")
            }
            Self::NonCanonicalAllowedChildBindingOrder => {
                formatter.write_str("allowed child bindings are not in canonical order")
            }
            Self::LeafHasChildContract => {
                formatter.write_str("leaf proof shape declares a child contract")
            }
            Self::AggregateHasNoChildContract => {
                formatter.write_str("aggregate proof shape has no child contract")
            }
            Self::TooManyRequiredAssumptions { actual, maximum } => {
                write!(
                    formatter,
                    "required assumption count {actual} exceeds {maximum}"
                )
            }
            Self::DuplicateAssumptionSlot => formatter.write_str("duplicate assumption slot"),
            Self::DuplicateExpectedVerificationClaim => {
                formatter.write_str("duplicate expected verification claim")
            }
            Self::DuplicateExpectedChildJournal => {
                formatter.write_str("duplicate expected child journal")
            }
            Self::NonDenseAssumptionSlots => {
                formatter.write_str("assumption slots are not dense from zero")
            }
            Self::NonCanonicalAssumptionOrder => {
                formatter.write_str("assumptions are not in canonical slot order")
            }
            Self::ProofShapeMismatch { .. } => {
                formatter.write_str("assumption manifest proof shape mismatch")
            }
            Self::AssumptionCountCeilingExceeded { actual, maximum } => {
                write!(formatter, "assumption count {actual} exceeds {maximum}")
            }
            Self::RequiredBindingNotAllowed => {
                formatter.write_str("required child binding is not allowed")
            }
            Self::TotalChildJournalCeilingExceeded { actual, maximum } => {
                write!(formatter, "child journal bytes {actual} exceed {maximum}")
            }
            Self::InvalidResolvedChildJournalBytes => {
                formatter.write_str("invalid resolved child journal byte count")
            }
            Self::TooManyResolvedClaims { actual, maximum } => {
                write!(formatter, "resolved claim count {actual} exceeds {maximum}")
            }
            Self::DuplicateResolvedAssumption => {
                formatter.write_str("duplicate resolved assumption")
            }
            Self::DuplicateVerificationClaim => formatter.write_str("duplicate verification claim"),
            Self::DuplicateResolvedChildJournal => {
                formatter.write_str("duplicate resolved child journal")
            }
            Self::SurplusResolvedClaim { .. } => {
                formatter.write_str("resolved claim is not required")
            }
            Self::UnresolvedAssumption { slot } => {
                write!(formatter, "required assumption slot {slot} is unresolved")
            }
            Self::ChildShapeMismatch => formatter.write_str("child shape mismatch"),
            Self::ChildProgramMismatch => formatter.write_str("child program mismatch"),
            Self::ChildProfileMismatch => formatter.write_str("child profile mismatch"),
            Self::VerificationClaimMismatch => formatter.write_str("verification claim mismatch"),
            Self::ChildJournalMismatch => formatter.write_str("child journal mismatch"),
            Self::ChildJournalBytesExceeded { actual, maximum } => {
                write!(formatter, "child journal bytes {actual} exceed {maximum}")
            }
            Self::EmptyRegistry => formatter.write_str("proof shape registry is empty"),
            Self::TooManyRegistryEntries { actual, maximum } => {
                write!(formatter, "registry entry count {actual} exceeds {maximum}")
            }
            Self::DuplicateProofShape => formatter.write_str("duplicate proof shape"),
            Self::NonCanonicalRegistryOrder => {
                formatter.write_str("proof shape registrations are not in canonical order")
            }
            Self::DuplicateAssumptionManifest => {
                formatter.write_str("duplicate assumption manifest")
            }
            Self::UnknownAssumptionManifest => formatter.write_str("unknown assumption manifest"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::EmptyInput => formatter.write_str("input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "input length {actual} exceeds {maximum}")
            }
            Self::PostcardDecode => formatter.write_str("postcard decode failed"),
            Self::TrailingBytes => formatter.write_str("postcard input has trailing bytes"),
            Self::NonCanonicalEncoding => formatter.write_str("postcard input is noncanonical"),
        }
    }
}
