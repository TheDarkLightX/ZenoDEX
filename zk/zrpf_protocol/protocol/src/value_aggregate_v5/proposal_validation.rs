use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use serde::{de, Deserializer, Serialize, Serializer};

use super::{ValueAggregateChildDescriptorV5, ValueAggregateErrorV5};
use crate::{NodeScopeV3, SemanticSubtreeV2, MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_LEVEL_V3};

pub(super) fn validate_shape(
    aggregate_level: u8,
    scope: &NodeScopeV3,
    semantic_subtree: &SemanticSubtreeV2,
    children: &[ValueAggregateChildDescriptorV5],
) -> Result<(), ValueAggregateErrorV5> {
    if aggregate_level == 0 || aggregate_level > MAX_NODE_LEVEL_V3 {
        return Err(ValueAggregateErrorV5::InvalidAggregateLevel(
            aggregate_level,
        ));
    }
    require_child_count(children.len())?;
    scope.validate()?;
    if scope.epoch_start() != scope.epoch_end() {
        return Err(ValueAggregateErrorV5::MultiEpochScope);
    }
    semantic_subtree.validate()?;
    if scope.canonical_hash()? != semantic_subtree.scope_hash() {
        return Err(ValueAggregateErrorV5::ScopeHashMismatch);
    }
    validate_children(aggregate_level, semantic_subtree, children)
}

fn validate_children(
    aggregate_level: u8,
    semantic_subtree: &SemanticSubtreeV2,
    children: &[ValueAggregateChildDescriptorV5],
) -> Result<(), ValueAggregateErrorV5> {
    let expected_level = aggregate_level - 1;
    let mut claims = BTreeSet::new();
    let mut journals = BTreeSet::new();
    let mut expected_start = semantic_subtree.partition().start();
    for (index, child) in children.iter().enumerate() {
        child.validate()?;
        if child.child_level() != expected_level {
            return Err(ValueAggregateErrorV5::InvalidChildLevel {
                child: index,
                actual: child.child_level(),
            });
        }
        if child.partition().start() != expected_start {
            return Err(ValueAggregateErrorV5::ChildPartitionGap { child: index });
        }
        if child.child_level() == 0
            && child.partition().end_exclusive() - child.partition().start() != 1
        {
            return Err(ValueAggregateErrorV5::ChildPartitionCoverageMismatch);
        }
        expected_start = child.partition().end_exclusive();
        if !claims.insert(child.claim_binding()) {
            return Err(ValueAggregateErrorV5::DuplicateChildClaim);
        }
        if !journals.insert(child.journal_hash()) {
            return Err(ValueAggregateErrorV5::DuplicateChildJournal);
        }
    }
    if expected_start != semantic_subtree.partition().end_exclusive() {
        return Err(ValueAggregateErrorV5::ChildPartitionCoverageMismatch);
    }
    Ok(())
}

fn require_child_count(count: usize) -> Result<(), ValueAggregateErrorV5> {
    if count == 0 {
        return Err(ValueAggregateErrorV5::EmptyChildren);
    }
    if count > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(ValueAggregateErrorV5::TooManyChildren {
            actual: count,
            maximum: MAX_IMMEDIATE_CHILDREN_V3,
        });
    }
    Ok(())
}

pub(super) fn child_count(count: usize) -> Result<u8, ValueAggregateErrorV5> {
    require_child_count(count)?;
    u8::try_from(count).map_err(|_| ValueAggregateErrorV5::ArithmeticOverflow("child_count"))
}

pub(super) fn serialize_children<S>(
    children: &[ValueAggregateChildDescriptorV5],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    children.serialize(serializer)
}

pub(super) fn deserialize_children<'de, D>(
    deserializer: D,
) -> Result<Vec<ValueAggregateChildDescriptorV5>, D::Error>
where
    D: Deserializer<'de>,
{
    struct ChildrenVisitor;

    impl<'de> de::Visitor<'de> for ChildrenVisitor {
        type Value = Vec<ValueAggregateChildDescriptorV5>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "between one and {MAX_IMMEDIATE_CHILDREN_V3} V5 child descriptors"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: de::SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_IMMEDIATE_CHILDREN_V3 {
                return Err(de::Error::custom(ValueAggregateErrorV5::TooManyChildren {
                    actual: declared,
                    maximum: MAX_IMMEDIATE_CHILDREN_V3,
                }));
            }
            let mut children = Vec::with_capacity(declared);
            while let Some(child) = sequence.next_element()? {
                if children.len() == MAX_IMMEDIATE_CHILDREN_V3 {
                    return Err(de::Error::custom(ValueAggregateErrorV5::TooManyChildren {
                        actual: MAX_IMMEDIATE_CHILDREN_V3 + 1,
                        maximum: MAX_IMMEDIATE_CHILDREN_V3,
                    }));
                }
                children.push(child);
            }
            Ok(children)
        }
    }

    deserializer.deserialize_seq(ChildrenVisitor)
}
