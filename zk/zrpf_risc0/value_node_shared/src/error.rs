use core::fmt;

use zenodex_zrpf_protocol_v3::{SemanticEpochErrorV1, ValueNodeErrorV4, ZrpfErrorV3};
use zenodex_zrpf_risc0_semantic_shared::{SpotSemanticValueErrorV1, SpotValueWireErrorV4};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotValueLeafInputErrorV4 {
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    Truncated,
    InvalidSchema(u16),
    ZeroSelfImageId,
    InvalidAdapterJournalLength(usize),
    InvalidWitnessLength(usize),
    InvalidSemanticOpening,
    InvalidLaneLength(usize),
    InvalidUtf8,
    InvalidRowCount(usize),
    InvalidAssetIdLength { row: usize, length: usize },
    InvalidGrantCount(usize),
    WitnessRejected,
    TrailingBytes,
    LengthOverflow,
    NonCanonicalEncoding,
}

impl fmt::Display for SpotValueLeafInputErrorV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("Spot value leaf input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "Spot value leaf input {actual} exceeds {maximum}"
                )
            }
            Self::Truncated => formatter.write_str("Spot value leaf input is truncated"),
            Self::InvalidSchema(version) => {
                write!(formatter, "invalid Spot value leaf schema: {version}")
            }
            Self::ZeroSelfImageId => formatter.write_str("Spot value leaf self image is zero"),
            Self::InvalidAdapterJournalLength(length) => {
                write!(formatter, "invalid adapter journal length: {length}")
            }
            Self::InvalidWitnessLength(length) => {
                write!(formatter, "invalid Spot value witness length: {length}")
            }
            Self::InvalidSemanticOpening => {
                formatter.write_str("Spot value semantic opening is zero")
            }
            Self::InvalidLaneLength(length) => {
                write!(formatter, "invalid Spot value lane length: {length}")
            }
            Self::InvalidUtf8 => formatter.write_str("Spot value text is not UTF-8"),
            Self::InvalidRowCount(count) => {
                write!(formatter, "invalid Spot value row count: {count}")
            }
            Self::InvalidAssetIdLength { row, length } => {
                write!(
                    formatter,
                    "invalid Spot asset ID length at row {row}: {length}"
                )
            }
            Self::InvalidGrantCount(count) => {
                write!(formatter, "invalid Spot value grant count: {count}")
            }
            Self::WitnessRejected => formatter.write_str("Spot value witness rejected"),
            Self::TrailingBytes => formatter.write_str("Spot value leaf input has trailing bytes"),
            Self::LengthOverflow => formatter.write_str("Spot value leaf length overflow"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("Spot value leaf input is not canonical")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpotValueLeafProposalErrorV4 {
    Input(SpotValueLeafInputErrorV4),
    Structural(ZrpfErrorV3),
    SemanticLeaf(SemanticEpochErrorV1),
    SpotValue(SpotSemanticValueErrorV1),
    ValueWire(SpotValueWireErrorV4),
    ValueNode(ValueNodeErrorV4),
    Derivation(&'static str),
}

impl fmt::Display for SpotValueLeafProposalErrorV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(error) => write!(formatter, "Spot leaf input rejected: {error}"),
            Self::Structural(error) => write!(formatter, "Spot structural leaf rejected: {error}"),
            Self::SemanticLeaf(error) => write!(formatter, "Spot semantic leaf rejected: {error}"),
            Self::SpotValue(error) => write!(formatter, "Spot value reference rejected: {error}"),
            Self::ValueWire(error) => write!(formatter, "Spot V4 bridge rejected: {error}"),
            Self::ValueNode(error) => write!(formatter, "Spot V4 node rejected: {error}"),
            Self::Derivation(field) => write!(formatter, "Spot V4 derivation failed: {field}"),
        }
    }
}

impl From<SpotValueLeafInputErrorV4> for SpotValueLeafProposalErrorV4 {
    fn from(error: SpotValueLeafInputErrorV4) -> Self {
        Self::Input(error)
    }
}

impl From<ZrpfErrorV3> for SpotValueLeafProposalErrorV4 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl From<SemanticEpochErrorV1> for SpotValueLeafProposalErrorV4 {
    fn from(error: SemanticEpochErrorV1) -> Self {
        Self::SemanticLeaf(error)
    }
}

impl From<SpotSemanticValueErrorV1> for SpotValueLeafProposalErrorV4 {
    fn from(error: SpotSemanticValueErrorV1) -> Self {
        Self::SpotValue(error)
    }
}

impl From<SpotValueWireErrorV4> for SpotValueLeafProposalErrorV4 {
    fn from(error: SpotValueWireErrorV4) -> Self {
        Self::ValueWire(error)
    }
}

impl From<ValueNodeErrorV4> for SpotValueLeafProposalErrorV4 {
    fn from(error: ValueNodeErrorV4) -> Self {
        Self::ValueNode(error)
    }
}
