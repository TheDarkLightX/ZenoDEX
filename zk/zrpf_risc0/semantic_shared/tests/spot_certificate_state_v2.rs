#[path = "support/spot_certificate_fixture.rs"]
mod fixture;
#[path = "support/spot_certificate_state_v2_fixture.rs"]
mod state_fixture;
#[path = "support/spot_certificate_state_v2_hashes.rs"]
mod state_hashes;

use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, DomainIdV3, EconomicActionIdV1, FullBlobDataAvailabilityErrorV1,
    ProposedValueAggregateV5, SettlementEffectPlanV2, SettlementEpochCertificateV1,
    SparseMerkleCellTransitionWitnessV1, ValueHashV2,
};
use zenodex_zrpf_risc0_semantic_shared::{
    compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2,
    derive_spot_settlement_state_projection_v2, OrdinarySpotSettlementCertificateErrorV1,
    SpotSettlementAuthorizationInputV1,
};

use fixture::{authorization, authorization_with, commitment, proposal, FixtureConfig};
use state_fixture::{
    da_certificate, matching_da_certificate, replay_blob, witness, witness_with,
    DaCertificateMetadataV2, WitnessOverridesV2,
};
use state_hashes::{
    independent_da_certificate_root, independent_journal_hash, independent_schedule_root,
};

const DERIVED_CLAIM_BINDING_SEED: u8 = 70;

#[test]
fn strict_state_bound_composer_maps_sparse_roots_and_validated_da_content() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay = replay_blob(&proposal, authorization, &witness);
    let da_certificate = matching_da_certificate(&proposal, &replay);
    let certificate =
        strict_compose(&proposal, authorization, witness.clone(), &da_certificate).unwrap();
    let projection =
        derive_spot_settlement_state_projection_v2(&proposal, authorization, witness.clone())
            .unwrap();
    let plan = projection.settlement_plan();

    assert_certificate_plan_mapping(&certificate, &proposal, plan);
    assert_eq!(certificate.pre_state_root(), witness.claimed_pre_root());
    assert_eq!(certificate.post_state_root(), witness.claimed_post_root());
    assert_ne!(
        certificate.pre_state_root(),
        proposal.semantic_subtree().raw_subtree_pre_state_root()
    );
    assert_ne!(
        certificate.post_state_root(),
        proposal.semantic_subtree().raw_subtree_post_state_root()
    );
    assert_eq!(
        certificate.data_availability_certificate_root(),
        da_certificate.certificate_root()
    );
    assert_eq!(
        certificate.schedule_certificate_root(),
        independent_schedule_root(&proposal, plan)
    );
    da_certificate.validate_blob(&replay).unwrap();
    assert_ne!(
        da_certificate.certificate_root(),
        proposal
            .operational_commitments()
            .data_availability_certificate_root()
    );
}

#[test]
fn strict_state_bound_da_schedule_and_journal_match_fixed_independent_preimages() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay = replay_blob(&proposal, authorization, &witness);
    let da_certificate = matching_da_certificate(&proposal, &replay);
    let certificate = strict_compose(&proposal, authorization, witness, &da_certificate).unwrap();

    assert_eq!(
        da_certificate.certificate_root().into_bytes(),
        independent_da_certificate_root(&da_certificate)
    );
    assert_eq!(
        certificate.canonical_journal_hash().unwrap(),
        independent_journal_hash(&certificate)
    );
    assert_eq!(
        da_certificate.certificate_root().into_bytes(),
        [
            174, 5, 56, 26, 99, 180, 56, 206, 150, 90, 215, 101, 138, 226, 226, 14, 234, 51, 183,
            214, 156, 25, 185, 189, 172, 2, 109, 36, 132, 29, 53, 141,
        ]
    );
    assert_eq!(
        certificate.schedule_certificate_root().into_bytes(),
        [
            194, 6, 21, 247, 134, 205, 220, 97, 154, 236, 91, 182, 100, 25, 43, 68, 76, 175, 173,
            92, 176, 115, 180, 25, 210, 101, 34, 79, 255, 44, 3, 60,
        ]
    );
    assert_eq!(
        certificate.canonical_journal_hash().unwrap().into_bytes(),
        [
            230, 211, 177, 193, 146, 194, 230, 8, 65, 101, 23, 154, 150, 35, 176, 58, 245, 146,
            148, 153, 154, 33, 58, 243, 167, 167, 222, 205, 97, 201, 108, 98,
        ]
    );
}

#[test]
fn strict_state_bound_composer_rejects_every_da_scope_schema_policy_and_content_mutation() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay = replay_blob(&proposal, authorization, &witness);
    assert_da_metadata_mutations(&proposal, authorization, &witness, &replay);
    assert_da_content_mutation(&proposal, authorization, witness, &replay);
}

fn assert_da_metadata_mutations(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: &SparseMerkleCellTransitionWitnessV1,
    replay: &[u8],
) {
    let matching = DaCertificateMetadataV2::matching(proposal);
    let mutations = [
        (
            DaCertificateMetadataV2 {
                application_id: ApplicationIdV3::new([81; 32]).unwrap(),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityApplicationMismatch,
        ),
        (
            DaCertificateMetadataV2 {
                chain_or_domain_id: DomainIdV3::new([82; 32]).unwrap(),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityDomainMismatch,
        ),
        (
            DaCertificateMetadataV2 {
                epoch_id: matching.epoch_id + 1,
                retention_through_epoch: matching.retention_through_epoch + 1,
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityEpochMismatch,
        ),
        (
            DaCertificateMetadataV2 {
                data_schema_id: commitment(83),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilitySchemaMismatch,
        ),
        (
            DaCertificateMetadataV2 {
                storage_policy_hash: commitment(84),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityStoragePolicyMismatch,
        ),
    ];
    for (metadata, expected) in mutations {
        let certificate = da_certificate(replay, metadata);
        assert_eq!(
            strict_compose(proposal, authorization, witness.clone(), &certificate).unwrap_err(),
            expected
        );
    }
}

fn assert_da_content_mutation(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
    replay: &[u8],
) {
    let matching = DaCertificateMetadataV2::matching(proposal);
    let mut changed_content = replay.to_vec();
    changed_content.push(0);
    let changed_certificate = da_certificate(&changed_content, matching);
    assert_eq!(
        strict_compose(proposal, authorization, witness, &changed_certificate).unwrap_err(),
        OrdinarySpotSettlementCertificateErrorV1::DataAvailability(
            FullBlobDataAvailabilityErrorV1::DataRootMismatch
        )
    );
}

#[test]
fn strict_state_bound_composer_rejects_every_authorization_field_substitution() {
    let proposal = proposal(FixtureConfig::default());
    let baseline_authorization = authorization();
    let witness = witness(&proposal, baseline_authorization);
    let replay = replay_blob(&proposal, baseline_authorization, &witness);
    let da_certificate = matching_da_certificate(&proposal, &replay);
    for (changed_authorization, expected_projection_reject) in [
        (authorization_with(53, 51, 7, 52), true),
        (authorization_with(50, 54, 7, 52), true),
        (authorization_with(50, 51, 8, 52), true),
        (authorization_with(50, 51, 7, 55), false),
    ] {
        let error = strict_compose(
            &proposal,
            changed_authorization,
            witness.clone(),
            &da_certificate,
        )
        .unwrap_err();
        if expected_projection_reject {
            assert!(matches!(
                error,
                OrdinarySpotSettlementCertificateErrorV1::Projection(_)
            ));
        } else {
            assert_eq!(
                error,
                OrdinarySpotSettlementCertificateErrorV1::DataAvailability(
                    FullBlobDataAvailabilityErrorV1::DataRootMismatch
                )
            );
        }
    }
}

#[test]
fn strict_state_bound_composer_rejects_every_sparse_witness_field_substitution() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let baseline_witness = witness(&proposal, authorization);
    let replay = replay_blob(&proposal, authorization, &baseline_witness);
    let da_certificate = matching_da_certificate(&proposal, &replay);
    let mutations = [
        WitnessOverridesV2 {
            economic_action_id: Some(EconomicActionIdV1::new([91; 32]).unwrap()),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            cell_key: Some(commitment(92)),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            pre_value_hash: Some(ValueHashV2::new([93; 32])),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            post_value_hash: Some(ValueHashV2::new([94; 32])),
            ..WitnessOverridesV2::default()
        },
        WitnessOverridesV2 {
            sibling_seed: 95,
            ..WitnessOverridesV2::default()
        },
    ];
    for overrides in mutations {
        let changed_witness = witness_with(&proposal, authorization, overrides);
        assert!(
            strict_compose(&proposal, authorization, changed_witness, &da_certificate,).is_err()
        );
    }
}

#[test]
fn strict_state_bound_composer_maps_sparse_witness_roots() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let baseline_witness = witness(&proposal, authorization);
    let baseline_replay = replay_blob(&proposal, authorization, &baseline_witness);
    let baseline_da = matching_da_certificate(&proposal, &baseline_replay);
    let baseline =
        strict_compose(&proposal, authorization, baseline_witness, &baseline_da).unwrap();
    let changed_witness = witness_with(
        &proposal,
        authorization,
        WitnessOverridesV2 {
            sibling_seed: 91,
            ..WitnessOverridesV2::default()
        },
    );
    let changed_replay = replay_blob(&proposal, authorization, &changed_witness);
    let changed_da = matching_da_certificate(&proposal, &changed_replay);
    let changed = strict_compose(&proposal, authorization, changed_witness, &changed_da).unwrap();
    assert_ne!(changed.pre_state_root(), baseline.pre_state_root());
    assert_ne!(changed.post_state_root(), baseline.post_state_root());
    assert_ne!(
        changed.canonical_journal_hash().unwrap(),
        baseline.canonical_journal_hash().unwrap()
    );
}

#[test]
fn strict_state_bound_composer_maps_caller_supplied_claim_without_authenticating_it() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let witness = witness(&proposal, authorization);
    let replay = replay_blob(&proposal, authorization, &witness);
    let da_certificate = matching_da_certificate(&proposal, &replay);
    let baseline =
        strict_compose(&proposal, authorization, witness.clone(), &da_certificate).unwrap();
    let changed_claim =
        compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2(
            &proposal,
            authorization,
            witness,
            commitment(71),
            &da_certificate,
        )
        .unwrap();
    let mut expected = baseline.to_input();
    expected.semantic_claim_binding = commitment(71);
    assert_eq!(changed_claim.to_input(), expected);
}

#[test]
fn strict_state_bound_composer_binds_v5_conflict_schedule_root() {
    let baseline_proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let baseline_witness = witness(&baseline_proposal, authorization);
    let baseline_replay = replay_blob(&baseline_proposal, authorization, &baseline_witness);
    let baseline_da = matching_da_certificate(&baseline_proposal, &baseline_replay);
    let baseline = strict_compose(
        &baseline_proposal,
        authorization,
        baseline_witness,
        &baseline_da,
    )
    .unwrap();
    let changed_proposal = proposal(FixtureConfig {
        child_conflict_schedule_seed: 92,
        ..FixtureConfig::default()
    });
    let changed_witness = witness(&changed_proposal, authorization);
    let changed_replay = replay_blob(&changed_proposal, authorization, &changed_witness);
    let changed_da = matching_da_certificate(&changed_proposal, &changed_replay);
    let changed_schedule = strict_compose(
        &changed_proposal,
        authorization,
        changed_witness,
        &changed_da,
    )
    .unwrap();
    assert_ne!(
        changed_schedule.schedule_certificate_root(),
        baseline.schedule_certificate_root()
    );
}

fn strict_compose(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
    certificate: &zenodex_zrpf_protocol_v3::FullBlobDataAvailabilityCertificateV1,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2(
        proposal,
        authorization,
        witness,
        commitment(DERIVED_CLAIM_BINDING_SEED),
        certificate,
    )
}

fn assert_certificate_plan_mapping(
    certificate: &SettlementEpochCertificateV1,
    proposal: &ProposedValueAggregateV5,
    plan: &SettlementEffectPlanV2,
) {
    let batch = plan.economic_action_batch();
    assert_eq!(certificate.application_id(), batch.application_id());
    assert_eq!(certificate.chain_or_domain_id(), batch.chain_or_domain_id());
    assert_eq!(certificate.epoch_id(), batch.epoch_id());
    assert_eq!(
        certificate.semantic_journal_hash(),
        plan.source_semantic_journal_hash()
    );
    assert_eq!(
        certificate.semantic_claim_binding(),
        commitment(DERIVED_CLAIM_BINDING_SEED)
    );
    assert_eq!(
        certificate.economic_action_batch_commitment(),
        batch.canonical_commitment().unwrap()
    );
    assert_eq!(
        certificate.settlement_effect_plan_commitment(),
        plan.canonical_commitment().unwrap()
    );
    assert_eq!(certificate.pre_state_root(), batch.pre_state_root());
    assert_eq!(certificate.post_state_root(), plan.post_state_root());
    assert_eq!(certificate.cell_writes_root(), plan.cell_writes_root());
    assert_eq!(certificate.asset_effects_root(), plan.asset_effects_root());
    assert_eq!(certificate.messages_root(), plan.message_effects_root());
    assert_eq!(certificate.carries_root(), plan.carry_effects_root());
    assert_eq!(certificate.rewards_root(), plan.reward_effects_root());
    assert_eq!(certificate.public_policy_hash(), plan.public_policy_hash());
    assert_eq!(
        certificate.dependency_manifest_root(),
        proposal.dependency_manifest_root()
    );
}
