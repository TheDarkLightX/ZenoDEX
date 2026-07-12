use alloc::vec::Vec;

use sha2::{Digest, Sha256};

use super::{ValueAggregateChildDescriptorV5, ValueAggregateErrorV5};
use crate::{CommitmentV3, ProfileIdV3, ProgramIdV3};

const CHILD_DESCRIPTOR_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_child_descriptor.v5";
const CHILD_DESCRIPTORS_ROOT_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_child_descriptors_root.v5";
const CHILD_CLAIMS_ROOT_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_child_claims_root.v5";
const CHILD_JOURNALS_ROOT_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_child_journals_root.v5";
const CHILD_PROGRAMS_ROOT_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_child_programs_root.v5";
const CHILD_MANIFESTS_ROOT_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_child_manifests_root.v5";
const DEPENDENCY_MANIFEST_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_dependency_manifest.v5";
const PROPOSAL_COMMITMENT_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_aggregate_proposal.v5";

pub(super) struct DerivedValueAggregateRootsV5 {
    pub child_descriptors_root: CommitmentV3,
    pub child_claims_root: CommitmentV3,
    pub child_journals_root: CommitmentV3,
    pub child_programs_root: CommitmentV3,
    pub child_manifests_root: CommitmentV3,
    pub dependency_manifest_root: CommitmentV3,
}

pub(super) fn child_descriptor_hash_v5(
    child: &ValueAggregateChildDescriptorV5,
) -> Result<CommitmentV3, ValueAggregateErrorV5> {
    let mut hasher = domain_hasher(CHILD_DESCRIPTOR_DOMAIN_V5)?;
    hasher.update([child.child_level()]);
    hasher.update(child.partition().start().to_be_bytes());
    hasher.update(child.partition().end_exclusive().to_be_bytes());
    hasher.update(child.verified_program_id().as_bytes());
    hasher.update(child.proof_profile_id().as_bytes());
    for value in [
        child.program_manifest_root(),
        child.journal_hash(),
        child.claim_binding(),
        child.semantic_subtree_root(),
    ] {
        hasher.update(value.as_bytes());
    }
    commitment(hasher.finalize().into())
}

pub(super) fn derive_value_aggregate_roots_v5(
    children: &[ValueAggregateChildDescriptorV5],
) -> Result<DerivedValueAggregateRootsV5, ValueAggregateErrorV5> {
    let descriptor_hashes = children
        .iter()
        .map(child_descriptor_hash_v5)
        .collect::<Result<Vec<_>, _>>()?;
    let child_descriptors_root = commitment_root(
        CHILD_DESCRIPTORS_ROOT_DOMAIN_V5,
        descriptor_hashes.iter().map(|value| value.into_bytes()),
    )?;
    let child_claims_root = commitment_root(
        CHILD_CLAIMS_ROOT_DOMAIN_V5,
        children
            .iter()
            .map(|child| child.claim_binding().into_bytes()),
    )?;
    let child_journals_root = commitment_root(
        CHILD_JOURNALS_ROOT_DOMAIN_V5,
        children
            .iter()
            .map(|child| child.journal_hash().into_bytes()),
    )?;
    let child_programs_root = commitment_root(
        CHILD_PROGRAMS_ROOT_DOMAIN_V5,
        children
            .iter()
            .map(|child| child.verified_program_id().into_bytes()),
    )?;
    let child_manifests_root = commitment_root(
        CHILD_MANIFESTS_ROOT_DOMAIN_V5,
        children
            .iter()
            .map(|child| child.program_manifest_root().into_bytes()),
    )?;
    let dependency_manifest_root = dependency_manifest_root(children)?;
    Ok(DerivedValueAggregateRootsV5 {
        child_descriptors_root,
        child_claims_root,
        child_journals_root,
        child_programs_root,
        child_manifests_root,
        dependency_manifest_root,
    })
}

pub(super) struct ProposalCommitmentInputV5<'a> {
    pub proposal_version: u16,
    pub aggregate_level: u8,
    pub scope_hash: CommitmentV3,
    pub semantic_subtree_hash: CommitmentV3,
    pub child_count: u8,
    pub roots: &'a DerivedValueAggregateRootsV5,
}

pub(super) fn proposal_commitment_v5(
    input: ProposalCommitmentInputV5<'_>,
) -> Result<CommitmentV3, ValueAggregateErrorV5> {
    let mut hasher = domain_hasher(PROPOSAL_COMMITMENT_DOMAIN_V5)?;
    hasher.update(input.proposal_version.to_be_bytes());
    hasher.update([input.aggregate_level]);
    hasher.update(input.scope_hash.as_bytes());
    hasher.update(input.semantic_subtree_hash.as_bytes());
    hasher.update([input.child_count]);
    for value in [
        input.roots.child_descriptors_root,
        input.roots.child_claims_root,
        input.roots.child_journals_root,
        input.roots.child_programs_root,
        input.roots.child_manifests_root,
        input.roots.dependency_manifest_root,
    ] {
        hasher.update(value.as_bytes());
    }
    commitment(hasher.finalize().into())
}

fn dependency_manifest_root(
    children: &[ValueAggregateChildDescriptorV5],
) -> Result<CommitmentV3, ValueAggregateErrorV5> {
    let mut dependencies: Vec<(ProgramIdV3, ProfileIdV3, CommitmentV3)> = children
        .iter()
        .map(|child| {
            (
                child.verified_program_id(),
                child.proof_profile_id(),
                child.program_manifest_root(),
            )
        })
        .collect();
    dependencies.sort_unstable();
    dependencies.dedup();
    let mut hasher = domain_hasher(DEPENDENCY_MANIFEST_DOMAIN_V5)?;
    let count = u8::try_from(dependencies.len())
        .map_err(|_| ValueAggregateErrorV5::ArithmeticOverflow("dependency_count"))?;
    hasher.update([count]);
    for (program, profile, manifest) in dependencies {
        hasher.update(program.as_bytes());
        hasher.update(profile.as_bytes());
        hasher.update(manifest.as_bytes());
    }
    commitment(hasher.finalize().into())
}

fn commitment_root(
    domain: &[u8],
    values: impl ExactSizeIterator<Item = [u8; 32]>,
) -> Result<CommitmentV3, ValueAggregateErrorV5> {
    let mut hasher = domain_hasher(domain)?;
    let count = u8::try_from(values.len())
        .map_err(|_| ValueAggregateErrorV5::ArithmeticOverflow("root_count"))?;
    hasher.update([count]);
    for value in values {
        hasher.update(value);
    }
    commitment(hasher.finalize().into())
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, ValueAggregateErrorV5> {
    let length = u16::try_from(domain.len())
        .map_err(|_| ValueAggregateErrorV5::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, ValueAggregateErrorV5> {
    CommitmentV3::new(bytes).map_err(ValueAggregateErrorV5::Structural)
}
