#[path = "support/spot_certificate_fixture.rs"]
mod fixture;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, CommitmentV3, DomainIdV3, FullBlobDataAvailabilityCertificateInputV1,
    FullBlobDataAvailabilityCertificateV1, FullBlobDataAvailabilityErrorV1,
    ProposedValueAggregateV5, SettlementEpochCertificateV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    compose_ordinary_spot_settlement_certificate_v1,
    compose_ordinary_spot_settlement_certificate_with_full_blob_da_v1,
    encode_ordinary_spot_settlement_replay_data_v1,
    ordinary_spot_settlement_replay_data_schema_id_v1, OrdinarySpotSettlementCertificateErrorV1,
    OrdinarySpotSettlementReplayDataV1, SpotSettlementAuthorizationInputV1,
};

use fixture::{authorization, authorization_with, commitment, proposal, FixtureConfig};

const CLAIM_BINDING_SEED: u8 = 70;

#[derive(Clone, Copy)]
struct DaCertificateMetadataV1 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    data_schema_id: CommitmentV3,
    storage_policy_hash: CommitmentV3,
}

impl DaCertificateMetadataV1 {
    fn matching(proposal: &ProposedValueAggregateV5) -> Self {
        let scope = proposal.scope();
        Self {
            application_id: scope.application_id(),
            chain_or_domain_id: scope.chain_or_domain_id(),
            epoch_id: scope.epoch_start(),
            data_schema_id: ordinary_spot_settlement_replay_data_schema_id_v1().unwrap(),
            storage_policy_hash: scope.public_policy_hash(),
        }
    }
}

#[test]
fn strict_composer_validates_exact_replay_content_and_propagates_certificate_root() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let blob = replay_blob(&proposal, authorization);
    let da_certificate = matching_da_certificate(&proposal, &blob);
    let strict = strict_compose(&proposal, authorization, &da_certificate).unwrap();
    let compatibility = compose_ordinary_spot_settlement_certificate_v1(
        &proposal,
        authorization,
        commitment(CLAIM_BINDING_SEED),
        da_certificate.certificate_root(),
    )
    .unwrap();

    assert_eq!(strict, compatibility);
    assert_eq!(
        strict.data_availability_certificate_root(),
        da_certificate.certificate_root()
    );
    da_certificate.validate_blob(&blob).unwrap();
    assert_ne!(
        da_certificate.data_root(),
        proposal.operational_commitments().data_availability_root()
    );
    assert_ne!(
        da_certificate.certificate_root(),
        proposal
            .operational_commitments()
            .data_availability_certificate_root()
    );
}

#[test]
fn strict_da_and_settlement_roots_match_fixed_independent_preimages() {
    let proposal = proposal(FixtureConfig::default());
    let blob = replay_blob(&proposal, authorization());
    let da_certificate = matching_da_certificate(&proposal, &blob);
    let certificate = strict_compose(&proposal, authorization(), &da_certificate).unwrap();

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
            141, 95, 158, 20, 184, 168, 63, 217, 56, 181, 49, 175, 105, 56, 122, 155, 255, 170,
            231, 244, 34, 20, 44, 42, 66, 221, 101, 224, 87, 64, 62, 91,
        ]
    );
    assert_eq!(
        certificate.canonical_journal_hash().unwrap().into_bytes(),
        [
            77, 67, 44, 105, 34, 160, 177, 56, 144, 82, 51, 233, 204, 172, 207, 218, 242, 224, 101,
            193, 60, 226, 157, 100, 87, 139, 248, 53, 70, 121, 255, 247,
        ]
    );
}

#[test]
fn strict_composer_rejects_each_scope_policy_schema_and_content_mutation() {
    let proposal = proposal(FixtureConfig::default());
    let authorization = authorization();
    let blob = replay_blob(&proposal, authorization);
    assert_metadata_mutations_reject(&proposal, authorization, &blob);

    let mut alternate = blob.clone();
    let last = alternate.len() - 1;
    alternate[last] ^= 1;
    let alternate_certificate = matching_da_certificate(&proposal, &alternate);
    assert_eq!(
        strict_compose(&proposal, authorization, &alternate_certificate).unwrap_err(),
        OrdinarySpotSettlementCertificateErrorV1::DataAvailability(
            FullBlobDataAvailabilityErrorV1::DataRootMismatch
        )
    );
}

fn assert_metadata_mutations_reject(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    blob: &[u8],
) {
    let matching = DaCertificateMetadataV1::matching(proposal);
    let mutations = [
        (
            DaCertificateMetadataV1 {
                application_id: ApplicationIdV3::new([91; 32]).unwrap(),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityApplicationMismatch,
        ),
        (
            DaCertificateMetadataV1 {
                chain_or_domain_id: DomainIdV3::new([92; 32]).unwrap(),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityDomainMismatch,
        ),
        (
            DaCertificateMetadataV1 {
                epoch_id: matching.epoch_id + 1,
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityEpochMismatch,
        ),
        (
            DaCertificateMetadataV1 {
                storage_policy_hash: commitment(93),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilityStoragePolicyMismatch,
        ),
        (
            DaCertificateMetadataV1 {
                data_schema_id: commitment(94),
                ..matching
            },
            OrdinarySpotSettlementCertificateErrorV1::DataAvailabilitySchemaMismatch,
        ),
    ];
    for (metadata, expected) in mutations {
        let certificate = da_certificate(blob, metadata);
        assert_eq!(
            strict_compose(proposal, authorization, &certificate).unwrap_err(),
            expected
        );
    }
}

#[test]
fn strict_composer_rejects_da_for_a_different_authorization_plan() {
    let proposal = proposal(FixtureConfig::default());
    let first = authorization();
    let certificate = matching_da_certificate(&proposal, &replay_blob(&proposal, first));
    let changed = authorization_with(50, 51, 8, 52);

    assert_eq!(
        strict_compose(&proposal, changed, &certificate).unwrap_err(),
        OrdinarySpotSettlementCertificateErrorV1::DataAvailability(
            FullBlobDataAvailabilityErrorV1::DataRootMismatch
        )
    );
}

fn replay_blob(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) -> Vec<u8> {
    let replay = OrdinarySpotSettlementReplayDataV1::recompose(proposal, authorization).unwrap();
    encode_ordinary_spot_settlement_replay_data_v1(&replay).unwrap()
}

fn matching_da_certificate(
    proposal: &ProposedValueAggregateV5,
    blob: &[u8],
) -> FullBlobDataAvailabilityCertificateV1 {
    da_certificate(blob, DaCertificateMetadataV1::matching(proposal))
}

fn da_certificate(
    blob: &[u8],
    metadata: DaCertificateMetadataV1,
) -> FullBlobDataAvailabilityCertificateV1 {
    FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
        application_id: metadata.application_id,
        chain_or_domain_id: metadata.chain_or_domain_id,
        epoch_id: metadata.epoch_id,
        data_schema_id: metadata.data_schema_id,
        blob,
        retention_through_epoch: metadata.epoch_id + 10,
        storage_policy_hash: metadata.storage_policy_hash,
    })
    .unwrap()
}

fn strict_compose(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    certificate: &FullBlobDataAvailabilityCertificateV1,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    compose_ordinary_spot_settlement_certificate_with_full_blob_da_v1(
        proposal,
        authorization,
        commitment(CLAIM_BINDING_SEED),
        certificate,
    )
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn independent_da_certificate_root(
    certificate: &FullBlobDataAvailabilityCertificateV1,
) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zenodex.zrpf.full_blob_da.certificate_root.v1");
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.data_schema_id().as_bytes());
    hasher.update(certificate.data_root().as_bytes());
    hasher.update(certificate.blob_length().to_be_bytes());
    hasher.update(certificate.chunk_size().to_be_bytes());
    hasher.update(certificate.chunk_count().to_be_bytes());
    hasher.update(certificate.chunk_root().as_bytes());
    hasher.update(certificate.retention_through_epoch().to_be_bytes());
    hasher.update(certificate.storage_policy_hash().as_bytes());
    hasher.finalize().into()
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
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}
