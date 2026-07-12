use core::fmt;

use zenodex_zrpf_protocol_v3::{SemanticEpochErrorV1, ValueNodeErrorV4, ZrpfErrorV3};

use super::super::SpotSemanticValueErrorV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Exact field whose independently derived V1 and V4 values disagree.
pub enum SpotValueWireFieldV4 {
    ScopeHash,
    LaneIdHash,
    ValueProfileId,
    AccountingDomainId,
    AtomsUnitId,
    StateRootSchemeId,
    Partition,
    RawPreStateRoot,
    RawPostStateRoot,
    LeafCount,
    RepresentedRowCount,
    SemanticLeafRecordsRoot,
    OrderedTransactionRootsRoot,
    StateChainRoot,
    AuthorityGrantsRoot,
    AssetFlowsRoot,
    AuthorityUsesRoot,
    ValueSubtreeRoot,
}

impl fmt::Display for SpotValueWireFieldV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ScopeHash => "scope_hash",
            Self::LaneIdHash => "lane_id_hash",
            Self::ValueProfileId => "value_profile_id",
            Self::AccountingDomainId => "accounting_domain_id",
            Self::AtomsUnitId => "atoms_unit_id",
            Self::StateRootSchemeId => "state_root_scheme_id",
            Self::Partition => "partition",
            Self::RawPreStateRoot => "raw_pre_state_root",
            Self::RawPostStateRoot => "raw_post_state_root",
            Self::LeafCount => "leaf_count",
            Self::RepresentedRowCount => "represented_row_count",
            Self::SemanticLeafRecordsRoot => "semantic_leaf_records_root",
            Self::OrderedTransactionRootsRoot => "ordered_transaction_roots_root",
            Self::StateChainRoot => "state_chain_root",
            Self::AuthorityGrantsRoot => "authority_grants_root",
            Self::AssetFlowsRoot => "asset_flows_root",
            Self::AuthorityUsesRoot => "authority_uses_root",
            Self::ValueSubtreeRoot => "value_subtree_root",
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Fail-closed errors for the pure Spot V1 to semantic-subtree V4 bridge.
pub enum SpotValueWireErrorV4 {
    ReferenceKernel(SpotSemanticValueErrorV1),
    SemanticLeaf(SemanticEpochErrorV1),
    Structural(ZrpfErrorV3),
    ValueNode(ValueNodeErrorV4),
    ReferenceMismatch(SpotValueWireFieldV4),
    ExpectedProjectionMismatch(SpotValueWireFieldV4),
}

impl fmt::Display for SpotValueWireErrorV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReferenceKernel(error) => {
                write!(formatter, "Spot reference kernel invalid: {error}")
            }
            Self::SemanticLeaf(error) => write!(formatter, "semantic leaf invalid: {error}"),
            Self::Structural(error) => write!(formatter, "structural value invalid: {error}"),
            Self::ValueNode(error) => write!(formatter, "V4 value node invalid: {error}"),
            Self::ReferenceMismatch(field) => {
                write!(formatter, "Spot V1 and V4 reference roots differ: {field}")
            }
            Self::ExpectedProjectionMismatch(field) => {
                write!(
                    formatter,
                    "V4 subtree differs from expected Spot projection: {field}"
                )
            }
        }
    }
}

impl From<ValueNodeErrorV4> for SpotValueWireErrorV4 {
    fn from(error: ValueNodeErrorV4) -> Self {
        Self::ValueNode(error)
    }
}

impl From<SpotSemanticValueErrorV1> for SpotValueWireErrorV4 {
    fn from(error: SpotSemanticValueErrorV1) -> Self {
        Self::ReferenceKernel(error)
    }
}
