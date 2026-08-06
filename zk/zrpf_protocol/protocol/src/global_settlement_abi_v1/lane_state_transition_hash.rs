use sha2::{Digest, Sha256};

use super::{LaneStateOpeningBatchV1, LaneStateTransitionErrorV1, LaneStateTransitionWitnessV1};
use crate::{CommitmentV3, SparseMerkleCellTransitionWitnessV1};

const OPENING_BATCH_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.lane_state_opening_batch.v1";
const TRANSITION_WITNESS_ROOT_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.lane_state_transition_witness.v1";

pub(super) fn opening_batch_root_v1(
    batch: &LaneStateOpeningBatchV1,
) -> Result<CommitmentV3, LaneStateTransitionErrorV1> {
    let mut hasher = domain_hasher(OPENING_BATCH_ROOT_DOMAIN_V1)?;
    hasher.update(batch.batch_version().to_be_bytes());
    hasher.update([batch.lane_id().code()]);
    hasher.update(batch.economic_action_id().as_bytes());
    update_commitment(&mut hasher, batch.lane_pre_state_root());
    update_commitment(&mut hasher, batch.lane_post_state_root());
    let count = u8::try_from(batch.witnesses().len())
        .map_err(|_| LaneStateTransitionErrorV1::ArithmeticOverflow("opening_witness_count"))?;
    hasher.update([count]);
    for witness in batch.witnesses() {
        update_witness(&mut hasher, witness);
    }
    commitment(hasher, "lane_state_opening_batch_root")
}

pub(super) fn transition_witness_root_v1(
    witness: &LaneStateTransitionWitnessV1,
) -> Result<CommitmentV3, LaneStateTransitionErrorV1> {
    witness.validate_self_consistency()?;
    let mut hasher = domain_hasher(TRANSITION_WITNESS_ROOT_DOMAIN_V1)?;
    hasher.update([witness.kind_code(), witness.lane_id().code()]);
    hasher.update(witness.economic_action_id().as_bytes());
    update_commitment(&mut hasher, witness.lane_pre_state_root());
    update_commitment(&mut hasher, witness.lane_post_state_root());
    if let Some(batch) = witness.changed_batch() {
        update_commitment(&mut hasher, batch.openings_root());
    }
    commitment(hasher, "lane_state_transition_witness_root")
}

fn update_witness(hasher: &mut Sha256, witness: &SparseMerkleCellTransitionWitnessV1) {
    hasher.update(witness.witness_version().to_be_bytes());
    hasher.update(witness.economic_action_id().as_bytes());
    hasher.update(witness.cell_key().as_bytes());
    hasher.update(witness.pre_value_hash().as_bytes());
    hasher.update(witness.post_value_hash().as_bytes());
    for sibling in witness.sibling_commitments().as_array() {
        update_commitment(hasher, *sibling);
    }
    update_commitment(hasher, witness.claimed_pre_root());
    update_commitment(hasher, witness.claimed_post_root());
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, LaneStateTransitionErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| LaneStateTransitionErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, LaneStateTransitionErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| LaneStateTransitionErrorV1::InvalidDerivedCommitment(field))
}

fn update_commitment(hasher: &mut Sha256, value: CommitmentV3) {
    hasher.update(value.as_bytes());
}
