use core::fmt;

use zenodex_zrpf_protocol_v3::{
    EconomicActionBatchErrorV1, EconomicActionErrorV1, SettlementEffectErrorV2,
    SparseMerkleBatchTransitionErrorV1, ValueAggregateErrorV5, ValueNodeErrorV4, ZrpfErrorV3,
};

use crate::SpotSemanticValueErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpotSettlementProjectionErrorV1 {
    ValueAggregate(ValueAggregateErrorV5),
    ValueNode(ValueNodeErrorV4),
    SpotProfile(SpotSemanticValueErrorV1),
    Structural(ZrpfErrorV3),
    EconomicAction(EconomicActionErrorV1),
    EconomicBatch(EconomicActionBatchErrorV1),
    Settlement(SettlementEffectErrorV2),
    SparseMerkleBatch(SparseMerkleBatchTransitionErrorV1),
    ProfileMismatch(&'static str),
    SupplyChangingFlow,
    NonCanonicalOrdinaryFlow,
    EmptyEconomicFlow,
    MissingCanonicalCellWrite,
    UnexpectedCellWriteCount { actual: usize },
    ArithmeticOverflow(&'static str),
}

impl fmt::Display for SpotSettlementProjectionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValueAggregate(error) => write!(formatter, "Spot V5 proposal rejected: {error}"),
            Self::ValueNode(error) => write!(formatter, "Spot value subtree rejected: {error}"),
            Self::SpotProfile(error) => write!(formatter, "Spot profile rejected: {error}"),
            Self::Structural(error) => write!(formatter, "Spot structural value rejected: {error}"),
            Self::EconomicAction(error) => write!(formatter, "Spot action rejected: {error}"),
            Self::EconomicBatch(error) => write!(formatter, "Spot action batch rejected: {error}"),
            Self::Settlement(error) => write!(formatter, "Spot settlement plan rejected: {error}"),
            Self::SparseMerkleBatch(error) => {
                write!(formatter, "Spot settlement state witness rejected: {error}")
            }
            Self::ProfileMismatch(field) => write!(formatter, "Spot profile mismatch: {field}"),
            Self::SupplyChangingFlow => formatter
                .write_str("Spot ordinary settlement profile forbids supply-changing flows"),
            Self::NonCanonicalOrdinaryFlow => formatter.write_str(
                "Spot ordinary settlement flow must have equal nonzero outflow and inflow",
            ),
            Self::EmptyEconomicFlow => {
                formatter.write_str("Spot ordinary settlement profile requires an asset flow")
            }
            Self::MissingCanonicalCellWrite => {
                formatter.write_str("Spot settlement projection has no canonical cell write")
            }
            Self::UnexpectedCellWriteCount { actual } => write!(
                formatter,
                "Spot settlement projection has {actual} cell writes instead of one"
            ),
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "Spot settlement arithmetic overflow: {field}")
            }
        }
    }
}

impl From<ValueAggregateErrorV5> for SpotSettlementProjectionErrorV1 {
    fn from(error: ValueAggregateErrorV5) -> Self {
        Self::ValueAggregate(error)
    }
}

impl From<ValueNodeErrorV4> for SpotSettlementProjectionErrorV1 {
    fn from(error: ValueNodeErrorV4) -> Self {
        Self::ValueNode(error)
    }
}

impl From<SpotSemanticValueErrorV1> for SpotSettlementProjectionErrorV1 {
    fn from(error: SpotSemanticValueErrorV1) -> Self {
        Self::SpotProfile(error)
    }
}

impl From<ZrpfErrorV3> for SpotSettlementProjectionErrorV1 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl From<EconomicActionErrorV1> for SpotSettlementProjectionErrorV1 {
    fn from(error: EconomicActionErrorV1) -> Self {
        Self::EconomicAction(error)
    }
}

impl From<EconomicActionBatchErrorV1> for SpotSettlementProjectionErrorV1 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::EconomicBatch(error)
    }
}

impl From<SettlementEffectErrorV2> for SpotSettlementProjectionErrorV1 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::Settlement(error)
    }
}

impl From<SparseMerkleBatchTransitionErrorV1> for SpotSettlementProjectionErrorV1 {
    fn from(error: SparseMerkleBatchTransitionErrorV1) -> Self {
        Self::SparseMerkleBatch(error)
    }
}
