use tau_state_proof_risc0_shared::DexStateV1;
use zenodex_zrpf_protocol_v3::{
    encode_full_blob_da_certificate_v1, encode_settlement_admission_journal_v1, ApplicationIdV3,
    AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2, AuthorizationGrantIdV1,
    AuthorizationScopeIdV1, AuthorizationSubjectIdV1, AuthorizedEconomicActionV1, CommitmentV3,
    DomainIdV3, EconomicActionBatchV1, EconomicActionRecordInputV1, EconomicActionRecordV1,
    EconomicActionTypeIdV1, FullBlobDataAvailabilityCertificateInputV1,
    FullBlobDataAvailabilityCertificateV1, LedgerCellWriteInputV2, LedgerCellWriteV2, ProfileIdV3,
    SettlementAdmissionJournalV1, SettlementEffectPlanInputV2, SettlementEffectPlanV2,
    SettlementEpochCertificateInputV1, SettlementEpochCertificateV1, SettlementSemanticRootV1,
    ValueHashV2, SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
};
use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementReplayDataV2;
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    encode_source_opened_spot_settlement_replay_v3,
    source_opened_spot_settlement_replay_schema_id_v3,
};
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    encode_bounded_spot_state_root_v7_host_input_v1, BoundedSpotStateRootV7HostInputV1,
};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::SourceOpenedSpotValueLeafEnvelopeV6;

#[path = "../../../../zrpf_risc0/semantic_shared/tests/support/spot_certificate_fixture.rs"]
mod fixture;
#[path = "../../../../zrpf_risc0/semantic_shared/tests/support/spot_certificate_state_v2_fixture.rs"]
mod state_fixture;

pub struct CanonicalComponentsV1 {
    pub source_child_journal: Vec<u8>,
    pub data_availability_certificate: Vec<u8>,
    pub replay: Vec<u8>,
    pub state_root_host_input: Vec<u8>,
}

pub fn canonical_components() -> CanonicalComponentsV1 {
    let replay = canonical_source_opened_replay();
    CanonicalComponentsV1 {
        source_child_journal: canonical_settlement_admission_journal(),
        data_availability_certificate: canonical_da_certificate(&replay),
        replay,
        state_root_host_input: canonical_state_root_host_input(),
    }
}

fn canonical_source_opened_replay() -> Vec<u8> {
    let proposal = fixture::proposal(fixture::FixtureConfig::default());
    let authorization = fixture::authorization();
    let witness = state_fixture::witness(&proposal, authorization);
    let base =
        OrdinarySpotSettlementReplayDataV2::recompose(&proposal, authorization, &witness).unwrap();
    // Canonical framing is the builder's boundary. Source-proof authority is
    // deliberately absent from this host-only fixture.
    let source = SourceOpenedSpotValueLeafEnvelopeV6::new(0, vec![1], vec![2], vec![3]).unwrap();
    encode_source_opened_spot_settlement_replay_v3(&base, &source).unwrap()
}

fn canonical_da_certificate(replay: &[u8]) -> Vec<u8> {
    let certificate =
        FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
            application_id: ApplicationIdV3::new([1; 32]).unwrap(),
            chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
            epoch_id: 27,
            data_schema_id: source_opened_spot_settlement_replay_schema_id_v3().unwrap(),
            blob: replay,
            retention_through_epoch: 37,
            storage_policy_hash: commitment(3),
        })
        .unwrap();
    encode_full_blob_da_certificate_v1(&certificate).unwrap()
}

fn canonical_state_root_host_input() -> Vec<u8> {
    let input = BoundedSpotStateRootV7HostInputV1::new(
        DexStateV1::empty().to_snapshot(),
        [91; 32],
        [92; 32],
    )
    .unwrap();
    encode_bounded_spot_state_root_v7_host_input_v1(&input).unwrap()
}

fn canonical_settlement_admission_journal() -> Vec<u8> {
    let action = action();
    let batch = EconomicActionBatchV1::new(27, commitment(6), vec![action.clone()]).unwrap();
    let plan = SettlementEffectPlanV2::new(SettlementEffectPlanInputV2 {
        source_semantic_journal_hash: commitment(50),
        public_policy_hash: commitment(3),
        post_state_root: commitment(52),
        economic_action_batch: batch,
        ledger_cell_writes: vec![cell_write(&action)],
        asset_effects: vec![asset_effect(&action)],
        message_effects: Vec::new(),
        carry_effects: Vec::new(),
        reward_effects: Vec::new(),
    })
    .unwrap();
    let batch = plan.economic_action_batch();
    let certificate = SettlementEpochCertificateV1::new(SettlementEpochCertificateInputV1 {
        certificate_version: SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
        application_id: batch.application_id(),
        chain_or_domain_id: batch.chain_or_domain_id(),
        epoch_id: batch.epoch_id(),
        semantic_profile_id: ProfileIdV3::new([70; 32]).unwrap(),
        semantic_journal_hash: plan.source_semantic_journal_hash(),
        semantic_claim_binding: commitment(71),
        proof_tree_root: commitment(72),
        semantic_root: SettlementSemanticRootV1::ValueSubtree(commitment(73)),
        economic_action_batch_commitment: batch.canonical_commitment().unwrap(),
        economic_action_ids_root: batch.action_ids_root(),
        action_authorization_bindings_root: batch.action_authorization_bindings_root(),
        authorization_grant_spends_root: batch.authorization_grant_spends_root(),
        consumed_object_ids_root: batch.consumed_object_ids_root(),
        settlement_effect_plan_commitment: plan.canonical_commitment().unwrap(),
        pre_state_root: batch.pre_state_root(),
        post_state_root: plan.post_state_root(),
        cell_writes_root: plan.cell_writes_root(),
        asset_effects_root: plan.asset_effects_root(),
        messages_root: plan.message_effects_root(),
        carries_root: plan.carry_effects_root(),
        rewards_root: plan.reward_effects_root(),
        public_policy_hash: plan.public_policy_hash(),
        data_availability_certificate_root: commitment(74),
        schedule_certificate_root: commitment(75),
        carry_continuity_certificate_root: commitment(76),
        dependency_manifest_root: commitment(77),
    })
    .unwrap();
    let journal = SettlementAdmissionJournalV1::derive(&certificate, &plan).unwrap();
    encode_settlement_admission_journal_v1(&journal).unwrap()
}

fn action() -> AuthorizedEconomicActionV1 {
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        action_type_id: EconomicActionTypeIdV1::new([3; 32]).unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([4; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([5; 32]).unwrap(),
        authorization_nonce: 7,
        valid_from_epoch: 20,
        valid_through_epoch: 30,
        pre_state_root: commitment(6),
        action_semantics_hash: commitment(7),
        effect_commitment: commitment(8),
        consumed_object_ids: vec![commitment(9)],
    })
    .unwrap();
    AuthorizedEconomicActionV1::new(record, AuthorizationGrantIdV1::new([10; 32]).unwrap()).unwrap()
}

fn cell_write(action: &AuthorizedEconomicActionV1) -> LedgerCellWriteV2 {
    LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: action.action_id().unwrap(),
        cell_key: commitment(20),
        pre_value_hash: ValueHashV2::new([21; 32]),
        post_value_hash: ValueHashV2::new([22; 32]),
    })
    .unwrap()
}

fn asset_effect(action: &AuthorizedEconomicActionV1) -> AssetEffectV2 {
    AssetEffectV2::new(AssetEffectInputV2 {
        kind: AssetEffectKindV2::OrdinaryTransfer,
        economic_action_id: action.action_id().unwrap(),
        asset_id: commitment(30),
        debit_atoms: 17,
        credit_atoms: 17,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_scope_id: None,
        action_authorization_binding: None,
    })
    .unwrap()
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}
