use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::{
    derive_value_aggregate_roots_v5, proposal_commitment_v5, ProposalCommitmentInputV5,
};
use super::{
    ValueAggregateChildDescriptorV5, ValueAggregateErrorV5, VALUE_AGGREGATE_PROPOSAL_VERSION_V5,
};
use crate::{
    CommitmentV3, NodeScopeV3, SemanticSubtreeV2, MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_LEVEL_V3,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueAggregateProposalInputV5 {
    pub aggregate_level: u8,
    pub scope: NodeScopeV3,
    pub semantic_subtree: SemanticSubtreeV2,
    pub children: Vec<ValueAggregateChildDescriptorV5>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
/// Canonically encoded value-aggregation proposal with no parent runtime image.
///
/// This type authenticates no receipt and grants no settlement or ledger
/// authority. The only authority-bearing constructor belongs in a sealed outer
/// receipt verifier.
pub struct ProposedValueAggregateV5 {
    proposal_version: u16,
    aggregate_level: u8,
    scope: NodeScopeV3,
    semantic_subtree: SemanticSubtreeV2,
    #[serde(serialize_with = "serialize_children")]
    children: Vec<ValueAggregateChildDescriptorV5>,
    child_descriptors_root: CommitmentV3,
    child_claims_root: CommitmentV3,
    child_journals_root: CommitmentV3,
    child_programs_root: CommitmentV3,
    child_manifests_root: CommitmentV3,
    dependency_manifest_root: CommitmentV3,
    proposal_commitment: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProposedValueAggregateWireV5 {
    proposal_version: u16,
    aggregate_level: u8,
    scope: NodeScopeV3,
    semantic_subtree: SemanticSubtreeV2,
    #[serde(deserialize_with = "deserialize_children")]
    children: Vec<ValueAggregateChildDescriptorV5>,
    child_descriptors_root: CommitmentV3,
    child_claims_root: CommitmentV3,
    child_journals_root: CommitmentV3,
    child_programs_root: CommitmentV3,
    child_manifests_root: CommitmentV3,
    dependency_manifest_root: CommitmentV3,
    proposal_commitment: CommitmentV3,
}

impl ProposedValueAggregateV5 {
    pub fn derive(input: ValueAggregateProposalInputV5) -> Result<Self, ValueAggregateErrorV5> {
        validate_shape(
            input.aggregate_level,
            &input.scope,
            &input.semantic_subtree,
            &input.children,
        )?;
        let roots = derive_value_aggregate_roots_v5(&input.children)?;
        let child_count = child_count(input.children.len())?;
        let proposal_commitment = proposal_commitment_v5(ProposalCommitmentInputV5 {
            proposal_version: VALUE_AGGREGATE_PROPOSAL_VERSION_V5,
            aggregate_level: input.aggregate_level,
            scope_hash: input.scope.canonical_hash()?,
            semantic_subtree_hash: input.semantic_subtree.canonical_hash()?,
            child_count,
            roots: &roots,
        })?;
        let proposal = Self {
            proposal_version: VALUE_AGGREGATE_PROPOSAL_VERSION_V5,
            aggregate_level: input.aggregate_level,
            scope: input.scope,
            semantic_subtree: input.semantic_subtree,
            children: input.children,
            child_descriptors_root: roots.child_descriptors_root,
            child_claims_root: roots.child_claims_root,
            child_journals_root: roots.child_journals_root,
            child_programs_root: roots.child_programs_root,
            child_manifests_root: roots.child_manifests_root,
            dependency_manifest_root: roots.dependency_manifest_root,
            proposal_commitment,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }

    pub fn validate_self_consistency(&self) -> Result<(), ValueAggregateErrorV5> {
        if self.proposal_version != VALUE_AGGREGATE_PROPOSAL_VERSION_V5 {
            return Err(ValueAggregateErrorV5::InvalidProposalVersion(
                self.proposal_version,
            ));
        }
        validate_shape(
            self.aggregate_level,
            &self.scope,
            &self.semantic_subtree,
            &self.children,
        )?;
        let roots = derive_value_aggregate_roots_v5(&self.children)?;
        self.require_stored_roots(&roots)?;
        let expected_proposal = proposal_commitment_v5(ProposalCommitmentInputV5 {
            proposal_version: self.proposal_version,
            aggregate_level: self.aggregate_level,
            scope_hash: self.scope.canonical_hash()?,
            semantic_subtree_hash: self.semantic_subtree.canonical_hash()?,
            child_count: child_count(self.children.len())?,
            roots: &roots,
        })?;
        if self.proposal_commitment != expected_proposal {
            return Err(ValueAggregateErrorV5::CommitmentMismatch(
                "proposal_commitment",
            ));
        }
        Ok(())
    }

    fn require_stored_roots(
        &self,
        roots: &super::hash::DerivedValueAggregateRootsV5,
    ) -> Result<(), ValueAggregateErrorV5> {
        for (field, actual, expected) in [
            (
                "child_descriptors_root",
                self.child_descriptors_root,
                roots.child_descriptors_root,
            ),
            (
                "child_claims_root",
                self.child_claims_root,
                roots.child_claims_root,
            ),
            (
                "child_journals_root",
                self.child_journals_root,
                roots.child_journals_root,
            ),
            (
                "child_programs_root",
                self.child_programs_root,
                roots.child_programs_root,
            ),
            (
                "child_manifests_root",
                self.child_manifests_root,
                roots.child_manifests_root,
            ),
            (
                "dependency_manifest_root",
                self.dependency_manifest_root,
                roots.dependency_manifest_root,
            ),
        ] {
            if actual != expected {
                return Err(ValueAggregateErrorV5::CommitmentMismatch(field));
            }
        }
        Ok(())
    }

    pub const fn proposal_version(&self) -> u16 {
        self.proposal_version
    }

    pub const fn aggregate_level(&self) -> u8 {
        self.aggregate_level
    }

    pub const fn scope(&self) -> &NodeScopeV3 {
        &self.scope
    }

    pub const fn semantic_subtree(&self) -> &SemanticSubtreeV2 {
        &self.semantic_subtree
    }

    pub fn children(&self) -> &[ValueAggregateChildDescriptorV5] {
        &self.children
    }

    pub const fn child_descriptors_root(&self) -> CommitmentV3 {
        self.child_descriptors_root
    }

    pub const fn child_claims_root(&self) -> CommitmentV3 {
        self.child_claims_root
    }

    pub const fn child_journals_root(&self) -> CommitmentV3 {
        self.child_journals_root
    }

    pub const fn child_programs_root(&self) -> CommitmentV3 {
        self.child_programs_root
    }

    pub const fn child_manifests_root(&self) -> CommitmentV3 {
        self.child_manifests_root
    }

    pub const fn dependency_manifest_root(&self) -> CommitmentV3 {
        self.dependency_manifest_root
    }

    pub const fn proposal_commitment(&self) -> CommitmentV3 {
        self.proposal_commitment
    }

    fn from_wire(wire: ProposedValueAggregateWireV5) -> Result<Self, ValueAggregateErrorV5> {
        let proposal = Self {
            proposal_version: wire.proposal_version,
            aggregate_level: wire.aggregate_level,
            scope: wire.scope,
            semantic_subtree: wire.semantic_subtree,
            children: wire.children,
            child_descriptors_root: wire.child_descriptors_root,
            child_claims_root: wire.child_claims_root,
            child_journals_root: wire.child_journals_root,
            child_programs_root: wire.child_programs_root,
            child_manifests_root: wire.child_manifests_root,
            dependency_manifest_root: wire.dependency_manifest_root,
            proposal_commitment: wire.proposal_commitment,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }
}

impl<'de> Deserialize<'de> for ProposedValueAggregateV5 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(ProposedValueAggregateWireV5::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}

fn validate_shape(
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

fn child_count(count: usize) -> Result<u8, ValueAggregateErrorV5> {
    require_child_count(count)?;
    u8::try_from(count).map_err(|_| ValueAggregateErrorV5::ArithmeticOverflow("child_count"))
}

fn serialize_children<S>(
    children: &[ValueAggregateChildDescriptorV5],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    children.serialize(serializer)
}

fn deserialize_children<'de, D>(
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
