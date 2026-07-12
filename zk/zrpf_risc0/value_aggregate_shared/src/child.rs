use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v4, decode_exact_value_aggregate_proposal_v5, CommitmentV3,
    NodeKindV3, NodeScopeV3, ProposedValueAggregateV5, SemanticSubtreeV2,
    ValueAggregateChildDescriptorInputV5, ValueAggregateChildDescriptorV5,
};
use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;

use crate::{
    GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5,
    ValueAggregateRecompositionPolicyV5,
};

pub(crate) struct RecompositionChildV5 {
    pub descriptor: ValueAggregateChildDescriptorV5,
    pub subtree: SemanticSubtreeV2,
}

pub(crate) fn level_one_children(
    child_bytes: &[Vec<u8>],
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<Vec<RecompositionChildV5>, ValueAggregateRecompositionErrorV5> {
    policy.require_input_count(child_bytes.len())?;
    child_bytes
        .iter()
        .zip(policy.child_identities())
        .enumerate()
        .map(|(index, (bytes, identity))| {
            level_one_child(index, bytes, *identity, policy.expected_scope())
        })
        .collect()
}

pub(crate) fn level_two_children(
    child_bytes: &[Vec<u8>],
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<Vec<RecompositionChildV5>, ValueAggregateRecompositionErrorV5> {
    policy.require_input_count(child_bytes.len())?;
    child_bytes
        .iter()
        .zip(policy.child_identities())
        .enumerate()
        .map(|(index, (bytes, identity))| {
            level_two_child(index, bytes, *identity, policy.expected_scope())
        })
        .collect()
}

pub(crate) fn reject_duplicate_children(
    children: &[RecompositionChildV5],
) -> Result<(), ValueAggregateRecompositionErrorV5> {
    let mut claims = BTreeSet::new();
    let mut journals = BTreeSet::new();
    for child in children {
        if !claims.insert(child.descriptor.claim_binding()) {
            return Err(ValueAggregateRecompositionErrorV5::DuplicateChildClaim);
        }
        if !journals.insert(child.descriptor.journal_hash()) {
            return Err(ValueAggregateRecompositionErrorV5::DuplicateChildJournal);
        }
    }
    Ok(())
}

fn level_one_child(
    index: usize,
    bytes: &[u8],
    identity: GovernedValueChildIdentityV5,
    scope: &NodeScopeV3,
) -> Result<RecompositionChildV5, ValueAggregateRecompositionErrorV5> {
    let journal = decode_exact_node_journal_v4(bytes)
        .map_err(|_| ValueAggregateRecompositionErrorV5::ChildV4JournalDecode(index))?;
    require_v4_identity(index, &journal, identity, scope)?;
    let structural = journal.structural();
    let level = structural.node_level().get();
    if level != 0 {
        return Err(ValueAggregateRecompositionErrorV5::ChildLevelMismatch {
            child: index,
            actual: level,
        });
    }
    let partition = structural.partition();
    if structural.node_kind() != NodeKindV3::Leaf
        || structural.immediate_child_count() != 0
        || structural.leaf_count() != 1
        || partition.end_exclusive().checked_sub(partition.start()) != Some(1)
    {
        return Err(ValueAggregateRecompositionErrorV5::ChildNotSingletonLeaf(
            index,
        ));
    }
    let journal_hash = journal
        .canonical_hash()
        .map_err(|_| ValueAggregateRecompositionErrorV5::ChildCommitmentDerivation(index))?;
    descriptor_from_material(
        index,
        0,
        identity,
        bytes,
        journal_hash,
        journal.semantic_subtree().clone(),
    )
}

fn level_two_child(
    index: usize,
    bytes: &[u8],
    identity: GovernedValueChildIdentityV5,
    scope: &NodeScopeV3,
) -> Result<RecompositionChildV5, ValueAggregateRecompositionErrorV5> {
    let proposal = decode_exact_value_aggregate_proposal_v5(bytes)
        .map_err(|_| ValueAggregateRecompositionErrorV5::ChildV5ProposalDecode(index))?;
    require_level_one_proposal(index, &proposal, scope)?;
    descriptor_from_material(
        index,
        1,
        identity,
        bytes,
        // Exact decoding makes the proposal commitment the canonical journal
        // identity for this proof-neutral V5 wire.
        proposal.proposal_commitment(),
        proposal.semantic_subtree().clone(),
    )
}

fn require_v4_identity(
    index: usize,
    journal: &zenodex_zrpf_protocol_v3::NodeJournalV4,
    identity: GovernedValueChildIdentityV5,
    scope: &NodeScopeV3,
) -> Result<(), ValueAggregateRecompositionErrorV5> {
    if journal.actual_program_id() != identity.expected_program_id() {
        return Err(ValueAggregateRecompositionErrorV5::ChildProgramMismatch(
            index,
        ));
    }
    if journal.proof_profile_id() != identity.expected_profile_id() {
        return Err(ValueAggregateRecompositionErrorV5::ChildProfileMismatch(
            index,
        ));
    }
    if journal.program_manifest_root() != identity.expected_manifest_root() {
        return Err(ValueAggregateRecompositionErrorV5::ChildManifestMismatch(
            index,
        ));
    }
    if journal.structural().scope() != scope {
        return Err(ValueAggregateRecompositionErrorV5::ChildScopeMismatch(
            index,
        ));
    }
    Ok(())
}

fn require_level_one_proposal(
    index: usize,
    proposal: &ProposedValueAggregateV5,
    scope: &NodeScopeV3,
) -> Result<(), ValueAggregateRecompositionErrorV5> {
    if proposal.aggregate_level() != 1 {
        return Err(ValueAggregateRecompositionErrorV5::ChildLevelMismatch {
            child: index,
            actual: proposal.aggregate_level(),
        });
    }
    if proposal.scope() != scope {
        return Err(ValueAggregateRecompositionErrorV5::ChildScopeMismatch(
            index,
        ));
    }
    Ok(())
}

fn descriptor_from_material(
    index: usize,
    child_level: u8,
    identity: GovernedValueChildIdentityV5,
    bytes: &[u8],
    journal_hash: CommitmentV3,
    subtree: SemanticSubtreeV2,
) -> Result<RecompositionChildV5, ValueAggregateRecompositionErrorV5> {
    let claim_binding = derive_risc0_verified_claim_binding_v1(identity.expected_image_id(), bytes)
        .map_err(|_| ValueAggregateRecompositionErrorV5::ClaimBindingDerivation(index))?;
    let subtree_root = subtree
        .canonical_hash()
        .map_err(|_| ValueAggregateRecompositionErrorV5::ChildCommitmentDerivation(index))?;
    let descriptor = ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
        child_level,
        partition: subtree.partition(),
        verified_program_id: identity.expected_program_id(),
        proof_profile_id: identity.expected_profile_id(),
        program_manifest_root: identity.expected_manifest_root(),
        journal_hash,
        claim_binding,
        semantic_subtree_root: subtree_root,
    })?;
    Ok(RecompositionChildV5 {
        descriptor,
        subtree,
    })
}
