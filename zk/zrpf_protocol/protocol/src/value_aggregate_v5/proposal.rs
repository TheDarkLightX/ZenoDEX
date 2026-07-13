use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::{
    derive_value_aggregate_roots_v5, proposal_commitment_v5, ProposalCommitmentInputV5,
};
use super::proposal_validation::{
    child_count, deserialize_children, serialize_children, validate_shape,
};
use super::{
    ValueAggregateChildDescriptorV5, ValueAggregateErrorV5, ValueAggregateOperationalCommitmentsV5,
    VALUE_AGGREGATE_PROPOSAL_VERSION_V5,
};
use crate::{CommitmentV3, NodeScopeV3, SemanticSubtreeV2};

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
    operational_commitments: ValueAggregateOperationalCommitmentsV5,
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
    operational_commitments: ValueAggregateOperationalCommitmentsV5,
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
            operational_commitments: roots.operational_commitments,
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
        if self.operational_commitments != roots.operational_commitments {
            return Err(ValueAggregateErrorV5::CommitmentMismatch(
                "operational_commitments",
            ));
        }
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

    pub const fn operational_commitments(&self) -> ValueAggregateOperationalCommitmentsV5 {
        self.operational_commitments
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
            operational_commitments: wire.operational_commitments,
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
