use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicActionBatchV1, ProposedValueAggregateV5, SettlementEffectPlanV2,
};

use super::OrdinarySpotSettlementCertificateErrorV1;

const PROOF_TREE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.ordinary_spot_certificate_proof_tree.v1";
const SCHEDULE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.ordinary_spot_schedule_certificate.v1";
const EMPTY_CARRY_CONTINUITY_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.ordinary_spot_empty_carry_continuity.v1";

pub(super) fn derive_proof_tree_root_v1(
    proposal: &ProposedValueAggregateV5,
) -> Result<CommitmentV3, OrdinarySpotSettlementCertificateErrorV1> {
    let child_count = u8::try_from(proposal.children().len())
        .map_err(|_| OrdinarySpotSettlementCertificateErrorV1::ArithmeticOverflow("child_count"))?;
    let mut hasher = domain_hasher(PROOF_TREE_DOMAIN_V1)?;
    hasher.update(proposal.proposal_version().to_be_bytes());
    hasher.update([proposal.aggregate_level()]);
    hasher.update([child_count]);
    for root in [
        proposal.child_descriptors_root(),
        proposal.child_claims_root(),
        proposal.child_journals_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    commitment(hasher)
}

pub(super) fn derive_schedule_root_v1(
    conflict_schedule_root: CommitmentV3,
    batch: &EconomicActionBatchV1,
    plan: &SettlementEffectPlanV2,
) -> Result<CommitmentV3, OrdinarySpotSettlementCertificateErrorV1> {
    let action_count = u16::try_from(batch.actions().len()).map_err(|_| {
        OrdinarySpotSettlementCertificateErrorV1::ArithmeticOverflow("action_count")
    })?;
    let mut hasher = domain_hasher(SCHEDULE_DOMAIN_V1)?;
    hasher.update(1_u16.to_be_bytes());
    hasher.update(conflict_schedule_root.as_bytes());
    hasher.update(action_count.to_be_bytes());
    for action in batch.actions() {
        hasher.update(action.action_id()?.as_bytes());
    }
    hasher.update(batch.canonical_commitment()?.as_bytes());
    hasher.update(plan.canonical_commitment()?.as_bytes());
    commitment(hasher)
}

pub(super) fn derive_empty_carry_continuity_root_v1(
    plan: &SettlementEffectPlanV2,
) -> Result<CommitmentV3, OrdinarySpotSettlementCertificateErrorV1> {
    let mut hasher = domain_hasher(EMPTY_CARRY_CONTINUITY_DOMAIN_V1)?;
    hasher.update(1_u16.to_be_bytes());
    hasher.update(0_u16.to_be_bytes());
    hasher.update(plan.message_effects_root().as_bytes());
    hasher.update(0_u16.to_be_bytes());
    hasher.update(plan.carry_effects_root().as_bytes());
    commitment(hasher)
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, OrdinarySpotSettlementCertificateErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| OrdinarySpotSettlementCertificateErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(hasher: Sha256) -> Result<CommitmentV3, OrdinarySpotSettlementCertificateErrorV1> {
    Ok(CommitmentV3::new(hasher.finalize().into())?)
}
