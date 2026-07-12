#[path = "support/spot_certificate_fixture.rs"]
mod fixture;
#[path = "support/spot_certificate_vectors.rs"]
mod vectors;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicActionBatchV1, ProposedValueAggregateV5, SettlementEffectPlanV2,
    SettlementEpochCertificateV1, SettlementSemanticRootV1,
    SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    compose_ordinary_spot_settlement_certificate_v1, derive_spot_settlement_projection_v1,
    OrdinarySpotSettlementCertificateErrorV1,
};

use fixture::{authorization, commitment, proposal, FixtureConfig};
use vectors::{
    CERTIFICATE_JOURNAL_VECTOR, EMPTY_CARRY_ROOT_VECTOR, PROOF_TREE_ROOT_VECTOR,
    SCHEDULE_ROOT_VECTOR,
};

const CLAIM_BINDING_SEED: u8 = 70;
const DA_ROOT_SEED: u8 = 71;

#[test]
fn composer_maps_every_certificate_field_from_checked_sources() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let projection = derive_spot_settlement_projection_v1(&proposal, authorization).unwrap();
    let batch = projection.action_batch();
    let plan = projection.settlement_plan();
    let certificate = compose(&proposal, authorization).unwrap();

    assert_scope_and_semantic_fields(&proposal, &certificate, batch, plan);
    assert_batch_fields(&certificate, batch);
    assert_plan_and_external_fields(&proposal, &certificate, batch, plan);
}

fn assert_scope_and_semantic_fields(
    proposal: &ProposedValueAggregateV5,
    certificate: &SettlementEpochCertificateV1,
    batch: &EconomicActionBatchV1,
    plan: &SettlementEffectPlanV2,
) {
    assert_eq!(
        certificate.certificate_version(),
        SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1
    );
    assert_eq!(certificate.application_id(), batch.application_id());
    assert_eq!(certificate.chain_or_domain_id(), batch.chain_or_domain_id());
    assert_eq!(certificate.epoch_id(), batch.epoch_id());
    assert_eq!(
        certificate.semantic_profile_id().into_bytes(),
        proposal.semantic_subtree().value_profile_id().into_bytes()
    );
    assert_eq!(
        certificate.semantic_journal_hash(),
        plan.source_semantic_journal_hash()
    );
    assert_eq!(
        certificate.semantic_claim_binding(),
        commitment(CLAIM_BINDING_SEED)
    );
    assert_eq!(
        certificate.proof_tree_root(),
        independent_proof_tree_root(proposal)
    );
    assert_eq!(
        certificate.semantic_root(),
        SettlementSemanticRootV1::ValueSubtree(proposal.semantic_subtree().value_subtree_root())
    );
}

fn assert_batch_fields(certificate: &SettlementEpochCertificateV1, batch: &EconomicActionBatchV1) {
    assert_eq!(
        certificate.economic_action_batch_commitment(),
        batch.canonical_commitment().unwrap()
    );
    assert_eq!(
        certificate.economic_action_ids_root(),
        batch.action_ids_root()
    );
    assert_eq!(
        certificate.action_authorization_bindings_root(),
        batch.action_authorization_bindings_root()
    );
    assert_eq!(
        certificate.authorization_grant_spends_root(),
        batch.authorization_grant_spends_root()
    );
    assert_eq!(
        certificate.consumed_object_ids_root(),
        batch.consumed_object_ids_root()
    );
    assert_eq!(certificate.pre_state_root(), batch.pre_state_root());
}

fn assert_plan_and_external_fields(
    proposal: &ProposedValueAggregateV5,
    certificate: &SettlementEpochCertificateV1,
    batch: &EconomicActionBatchV1,
    plan: &SettlementEffectPlanV2,
) {
    assert_eq!(
        certificate.settlement_effect_plan_commitment(),
        plan.canonical_commitment().unwrap()
    );
    assert_eq!(certificate.post_state_root(), plan.post_state_root());
    assert_eq!(certificate.cell_writes_root(), plan.cell_writes_root());
    assert_eq!(certificate.asset_effects_root(), plan.asset_effects_root());
    assert_eq!(certificate.messages_root(), plan.message_effects_root());
    assert_eq!(certificate.carries_root(), plan.carry_effects_root());
    assert_eq!(certificate.rewards_root(), plan.reward_effects_root());
    assert_eq!(certificate.public_policy_hash(), plan.public_policy_hash());
    assert_eq!(
        certificate.data_availability_certificate_root(),
        commitment(DA_ROOT_SEED)
    );
    assert_eq!(
        certificate.schedule_certificate_root(),
        independent_schedule_root(proposal, batch, plan)
    );
    assert_eq!(
        certificate.carry_continuity_certificate_root(),
        independent_empty_carry_root(plan)
    );
    assert_eq!(
        certificate.dependency_manifest_root(),
        proposal.dependency_manifest_root()
    );
}

#[test]
fn derived_roots_and_journal_match_independent_fixed_preimages() {
    let proposal = proposal(FixtureConfig::default());
    let certificate = compose(&proposal, authorization()).unwrap();

    assert_eq!(
        certificate.proof_tree_root(),
        independent_proof_tree_root(&proposal)
    );
    let projection = derive_spot_settlement_projection_v1(&proposal, authorization()).unwrap();
    assert_eq!(
        certificate.schedule_certificate_root(),
        independent_schedule_root(
            &proposal,
            projection.action_batch(),
            projection.settlement_plan(),
        )
    );
    assert_eq!(
        certificate.carry_continuity_certificate_root(),
        independent_empty_carry_root(projection.settlement_plan())
    );
    assert_eq!(
        certificate.canonical_journal_hash().unwrap(),
        independent_journal_hash(&certificate)
    );

    assert_eq!(
        certificate.proof_tree_root().into_bytes(),
        PROOF_TREE_ROOT_VECTOR
    );
    assert_eq!(
        certificate.schedule_certificate_root().into_bytes(),
        SCHEDULE_ROOT_VECTOR
    );
    assert_eq!(
        certificate.carry_continuity_certificate_root().into_bytes(),
        EMPTY_CARRY_ROOT_VECTOR
    );
    assert_eq!(
        certificate.canonical_journal_hash().unwrap().into_bytes(),
        CERTIFICATE_JOURNAL_VECTOR
    );
}

fn compose(
    proposal: &ProposedValueAggregateV5,
    authorization: zenodex_zrpf_risc0_semantic_shared::SpotSettlementAuthorizationInputV1,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    compose_with(
        proposal,
        authorization,
        commitment(CLAIM_BINDING_SEED),
        commitment(DA_ROOT_SEED),
    )
}

fn compose_with(
    proposal: &ProposedValueAggregateV5,
    authorization: zenodex_zrpf_risc0_semantic_shared::SpotSettlementAuthorizationInputV1,
    claim_binding: CommitmentV3,
    da_root: CommitmentV3,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    compose_ordinary_spot_settlement_certificate_v1(proposal, authorization, claim_binding, da_root)
}

fn independent_proof_tree_root(proposal: &ProposedValueAggregateV5) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.ordinary_spot_certificate_proof_tree.v1");
    hasher.update(proposal.proposal_version().to_be_bytes());
    hasher.update([proposal.aggregate_level()]);
    hasher.update([u8::try_from(proposal.children().len()).unwrap()]);
    hasher.update(proposal.child_descriptors_root().as_bytes());
    hasher.update(proposal.child_claims_root().as_bytes());
    hasher.update(proposal.child_journals_root().as_bytes());
    commit(hasher)
}

fn independent_schedule_root(
    proposal: &ProposedValueAggregateV5,
    batch: &zenodex_zrpf_protocol_v3::EconomicActionBatchV1,
    plan: &zenodex_zrpf_protocol_v3::SettlementEffectPlanV2,
) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.ordinary_spot_schedule_certificate.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(
        proposal
            .operational_commitments()
            .conflict_schedule_root()
            .as_bytes(),
    );
    hasher.update(u16::try_from(batch.actions().len()).unwrap().to_be_bytes());
    for action in batch.actions() {
        hasher.update(action.action_id().unwrap().as_bytes());
    }
    hasher.update(batch.canonical_commitment().unwrap().as_bytes());
    hasher.update(plan.canonical_commitment().unwrap().as_bytes());
    commit(hasher)
}

fn independent_empty_carry_root(
    plan: &zenodex_zrpf_protocol_v3::SettlementEffectPlanV2,
) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.ordinary_spot_empty_carry_continuity.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(0_u16.to_be_bytes());
    hasher.update(plan.message_effects_root().as_bytes());
    hasher.update(0_u16.to_be_bytes());
    hasher.update(plan.carry_effects_root().as_bytes());
    commit(hasher)
}

fn independent_journal_hash(certificate: &SettlementEpochCertificateV1) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.settlement_epoch_certificate_journal.v1");
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.semantic_profile_id().as_bytes());
    for root in [
        certificate.semantic_journal_hash(),
        certificate.semantic_claim_binding(),
        certificate.proof_tree_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    hasher.update([1]);
    hasher.update(certificate.semantic_root().root().as_bytes());
    for root in [
        certificate.economic_action_batch_commitment(),
        certificate.economic_action_ids_root(),
        certificate.action_authorization_bindings_root(),
        certificate.authorization_grant_spends_root(),
        certificate.consumed_object_ids_root(),
        certificate.settlement_effect_plan_commitment(),
        certificate.pre_state_root(),
        certificate.post_state_root(),
        certificate.cell_writes_root(),
        certificate.asset_effects_root(),
        certificate.messages_root(),
        certificate.carries_root(),
        certificate.rewards_root(),
        certificate.public_policy_hash(),
        certificate.data_availability_certificate_root(),
        certificate.schedule_certificate_root(),
        certificate.carry_continuity_certificate_root(),
        certificate.dependency_manifest_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    commit(hasher)
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn commit(hasher: Sha256) -> CommitmentV3 {
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}
