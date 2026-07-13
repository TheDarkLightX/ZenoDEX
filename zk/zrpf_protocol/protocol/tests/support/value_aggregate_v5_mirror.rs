#![allow(dead_code)]

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, ProposedValueAggregateV5, ValueAggregateChildDescriptorV5,
    ValueAggregateOperationalCommitmentsV5,
};

pub fn mirror_operational_hash(
    commitments: ValueAggregateOperationalCommitmentsV5,
) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.value_operational_commitments.v5");
    for value in operational_values(commitments) {
        hasher.update(value.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

pub fn mirror_descriptor_hash(child: &ValueAggregateChildDescriptorV5) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.value_child_descriptor.v5");
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
        mirror_operational_hash(child.operational_commitments()),
    ] {
        hasher.update(value.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

pub fn mirror_root(domain: &[u8], values: &[CommitmentV3]) -> CommitmentV3 {
    let mut hasher = domain_hasher(domain);
    hasher.update([u8::try_from(values.len()).unwrap()]);
    for value in values {
        hasher.update(value.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

pub fn mirror_proposal(proposal: &ProposedValueAggregateV5) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.value_aggregate_proposal.v5");
    hasher.update(proposal.proposal_version().to_be_bytes());
    hasher.update([proposal.aggregate_level()]);
    hasher.update(proposal.scope().canonical_hash().unwrap().as_bytes());
    hasher.update(
        proposal
            .semantic_subtree()
            .canonical_hash()
            .unwrap()
            .as_bytes(),
    );
    hasher.update([u8::try_from(proposal.children().len()).unwrap()]);
    for value in [
        proposal.child_descriptors_root(),
        proposal.child_claims_root(),
        proposal.child_journals_root(),
        proposal.child_programs_root(),
        proposal.child_manifests_root(),
        proposal.dependency_manifest_root(),
        mirror_operational_hash(proposal.operational_commitments()),
    ] {
        hasher.update(value.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

pub fn operational_values(
    commitments: ValueAggregateOperationalCommitmentsV5,
) -> [CommitmentV3; 8] {
    [
        commitments.data_availability_root(),
        commitments.data_availability_certificate_root(),
        commitments.conflict_schedule_root(),
        commitments.cross_lane_outbox_root(),
        commitments.cross_lane_inbox_root(),
        commitments.cross_lane_message_ids_root(),
        commitments.carry_queue_pre_root(),
        commitments.carry_queue_post_root(),
    ]
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}
