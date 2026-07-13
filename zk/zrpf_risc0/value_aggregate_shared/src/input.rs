use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V4, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};

use crate::ValueAggregateRecompositionErrorV5;

#[derive(Clone, Debug, PartialEq, Eq)]
/// Bounded V4 child journal bytes for one level-one recomposition.
///
/// Construction checks only byte and count bounds. The recomposer establishes
/// exact canonical V4 decoding before deriving any child descriptor.
pub struct ValueAggregateLevelOneInputV5 {
    child_journal_bytes: Vec<Vec<u8>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Bounded level-one V5 proposal bytes for level-two recomposition.
///
/// Construction checks only byte and count bounds. The recomposer establishes
/// exact canonical V5 decoding before deriving any child descriptor.
pub struct ValueAggregateLevelTwoInputV5 {
    child_proposal_bytes: Vec<Vec<u8>>,
}

impl ValueAggregateLevelOneInputV5 {
    pub fn new(
        child_journal_bytes: Vec<Vec<u8>>,
    ) -> Result<Self, ValueAggregateRecompositionErrorV5> {
        validate_exact_children(&child_journal_bytes, MAX_NODE_JOURNAL_BYTES_V4)?;
        Ok(Self {
            child_journal_bytes,
        })
    }

    pub fn child_journal_bytes(&self) -> &[Vec<u8>] {
        &self.child_journal_bytes
    }
}

impl ValueAggregateLevelTwoInputV5 {
    pub fn new(
        child_proposal_bytes: Vec<Vec<u8>>,
    ) -> Result<Self, ValueAggregateRecompositionErrorV5> {
        validate_exact_children(&child_proposal_bytes, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5)?;
        Ok(Self {
            child_proposal_bytes,
        })
    }

    pub fn child_proposal_bytes(&self) -> &[Vec<u8>] {
        &self.child_proposal_bytes
    }
}

fn validate_exact_children(
    children: &[Vec<u8>],
    maximum_bytes: usize,
) -> Result<(), ValueAggregateRecompositionErrorV5> {
    if children.is_empty() || children.len() > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(ValueAggregateRecompositionErrorV5::InvalidChildCount {
            actual: children.len(),
            maximum: MAX_IMMEDIATE_CHILDREN_V3,
        });
    }
    for (index, child) in children.iter().enumerate() {
        if child.is_empty() {
            return Err(ValueAggregateRecompositionErrorV5::EmptyChildBytes(index));
        }
        if child.len() > maximum_bytes {
            return Err(ValueAggregateRecompositionErrorV5::ChildBytesTooLarge {
                child: index,
                actual: child.len(),
                maximum: maximum_bytes,
            });
        }
    }
    Ok(())
}
