use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use zenodex_zrpf_protocol_v3::CommitmentV3;

use crate::bounded::{deserialize_operations, deserialize_rows};
use crate::derive::{expected_rows_v1, require_conservation_v1, validate_operation_context};
use crate::hash::proposal_commitment_v1;
use crate::{
    ProposedZusdSourceEvidenceV1, ZusdValueFlowContextV1, ZusdValueFlowErrorV1, ZusdValueFlowRowV1,
    ZusdValueOperationV1, MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1, MAX_ZUSD_VALUE_FLOW_ROWS_V1,
};

pub const PROPOSED_ZUSD_VALUE_FLOW_VERSION_V1: u16 = 1;

/// Canonical proof-neutral zUSD lifecycle row proposal.
///
/// Construction derives all rows from validated operation inputs and supplies
/// no receipt, oracle, ledger, or settlement authority.
///
/// ```compile_fail
/// use zenodex_zrpf_zusd_value_flow_reference_v1::ProposedZusdValueFlowV1;
/// let proposal: ProposedZusdValueFlowV1 = unimplemented!();
/// let _ = proposal.settlement_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProposedZusdValueFlowV1 {
    proposal_version: u16,
    context: ZusdValueFlowContextV1,
    source_evidence: ProposedZusdSourceEvidenceV1,
    operations: Vec<ZusdValueOperationV1>,
    rows: Vec<ZusdValueFlowRowV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProposedZusdValueFlowWireV1 {
    proposal_version: u16,
    context: ZusdValueFlowContextV1,
    source_evidence: ProposedZusdSourceEvidenceV1,
    #[serde(deserialize_with = "deserialize_operations")]
    operations: Vec<ZusdValueOperationV1>,
    #[serde(deserialize_with = "deserialize_rows")]
    rows: Vec<ZusdValueFlowRowV1>,
}

impl ProposedZusdValueFlowV1 {
    pub fn new(
        context: ZusdValueFlowContextV1,
        source_evidence: ProposedZusdSourceEvidenceV1,
        mut operations: Vec<ZusdValueOperationV1>,
    ) -> Result<Self, ZusdValueFlowErrorV1> {
        require_operation_count(operations.len())?;
        operations.sort_by_key(ZusdValueOperationV1::action_index);
        require_operation_order(context, &operations)?;
        let rows = expected_rows_v1(context, &operations)?;
        Self::from_wire(ProposedZusdValueFlowWireV1 {
            proposal_version: PROPOSED_ZUSD_VALUE_FLOW_VERSION_V1,
            context,
            source_evidence,
            operations,
            rows,
        })
    }

    fn from_wire(wire: ProposedZusdValueFlowWireV1) -> Result<Self, ZusdValueFlowErrorV1> {
        let proposal = Self {
            proposal_version: wire.proposal_version,
            context: wire.context,
            source_evidence: wire.source_evidence,
            operations: wire.operations,
            rows: wire.rows,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }

    pub fn validate_self_consistency(&self) -> Result<(), ZusdValueFlowErrorV1> {
        if self.proposal_version != PROPOSED_ZUSD_VALUE_FLOW_VERSION_V1 {
            return Err(ZusdValueFlowErrorV1::InvalidContext("proposal_version"));
        }
        require_operation_count(self.operations.len())?;
        if self.rows.len() > MAX_ZUSD_VALUE_FLOW_ROWS_V1 {
            return Err(ZusdValueFlowErrorV1::TooManyRows {
                actual: self.rows.len(),
                maximum: MAX_ZUSD_VALUE_FLOW_ROWS_V1,
            });
        }
        require_operation_order(self.context, &self.operations)?;
        if self.rows != expected_rows_v1(self.context, &self.operations)? {
            return Err(ZusdValueFlowErrorV1::RowSetMismatch);
        }
        require_conservation_v1(&self.rows)
    }

    pub const fn context(&self) -> ZusdValueFlowContextV1 {
        self.context
    }

    pub const fn source_evidence(&self) -> ProposedZusdSourceEvidenceV1 {
        self.source_evidence
    }

    pub fn operations(&self) -> &[ZusdValueOperationV1] {
        &self.operations
    }

    pub fn rows(&self) -> &[ZusdValueFlowRowV1] {
        &self.rows
    }

    pub fn canonical_commitment(&self) -> Result<CommitmentV3, ZusdValueFlowErrorV1> {
        proposal_commitment_v1(self)
    }
}

impl<'de> Deserialize<'de> for ProposedZusdValueFlowV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProposedZusdValueFlowWireV1::deserialize(deserializer)?;
        Self::from_wire(wire).map_err(de::Error::custom)
    }
}

fn require_operation_count(count: usize) -> Result<(), ZusdValueFlowErrorV1> {
    if count == 0 {
        return Err(ZusdValueFlowErrorV1::EmptyOperations);
    }
    if count > MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1 {
        return Err(ZusdValueFlowErrorV1::TooManyOperations {
            actual: count,
            maximum: MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1,
        });
    }
    Ok(())
}

fn require_operation_order(
    context: ZusdValueFlowContextV1,
    operations: &[ZusdValueOperationV1],
) -> Result<(), ZusdValueFlowErrorV1> {
    let mut prior = None;
    for operation in operations {
        operation.validate_self_consistency()?;
        validate_operation_context(context, operation)?;
        if let Some(prior_index) = prior {
            if operation.action_index() == prior_index {
                return Err(ZusdValueFlowErrorV1::DuplicateActionIndex {
                    action_index: prior_index,
                });
            }
            if operation.action_index() < prior_index {
                return Err(ZusdValueFlowErrorV1::NonCanonicalOperationOrder);
            }
        }
        prior = Some(operation.action_index());
    }
    Ok(())
}
