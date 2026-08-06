pub use sha2::{Digest, Sha256};
pub use zenodex_zrpf_protocol_v3::{
    bind_economic_command_occurrence_to_active_profile_v1,
    bind_global_economic_state_to_profile_v1, bind_profile_bound_occurrence_to_global_state_v1,
    decode_exact_economic_object_release_pin_proof_v1, decode_exact_global_economic_state_v1,
    encode_economic_object_release_pin_proof_v1, encode_global_economic_state_v1, ApplicationIdV3,
    AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
    AuthorizedEconomicActionV1, CommitmentV3, DomainIdV3, EconomicActionRecordInputV1,
    EconomicActionRecordV1, EconomicActionTypeIdV1, EconomicCommandOccurrenceContentV1,
    EconomicCommandOccurrenceV1, EconomicLaneIdV1, EconomicObjectReleasePinProofV1,
    EconomicObjectReleasePinV1, EconomicOccurrencePositionV1, GlobalEconomicLaneStateRootV1,
    GlobalEconomicPartitionRootsInputV1, GlobalEconomicPartitionRootsV1,
    GlobalEconomicStateContentInputV1, GlobalEconomicStateContentV1, GlobalEconomicStateErrorV1,
    GlobalEconomicStateV1, LaneModuleReleaseIdV1, LaneModuleReleaseStatusV1,
    SparseMerkleSiblingPathV1, ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1,
    GLOBAL_ECONOMIC_STATE_VERSION_V1, MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1,
    MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1, SPARSE_MERKLE_TREE_DEPTH_V1,
};

pub use crate::profile_support::{economic_fixture, profile_id, EconomicRegistryFixture};

pub fn root(seed: u16) -> CommitmentV3 {
    crate::profile_support::root(seed)
}

pub fn application_id(seed: u16) -> ApplicationIdV3 {
    ApplicationIdV3::new(root(seed).into_bytes()).unwrap()
}

pub fn domain_id(seed: u16) -> DomainIdV3 {
    DomainIdV3::new(root(seed).into_bytes()).unwrap()
}

pub fn lane_release_id(seed: u16) -> LaneModuleReleaseIdV1 {
    LaneModuleReleaseIdV1::new(root(seed).into_bytes()).unwrap()
}

pub fn rejection<T, E>(result: Result<T, E>) -> E {
    match result {
        Ok(_) => panic!("expected typed rejection"),
        Err(error) => error,
    }
}

pub fn lane_state_roots(seed: u16) -> Vec<GlobalEconomicLaneStateRootV1> {
    EconomicLaneIdV1::ALL
        .into_iter()
        .enumerate()
        .map(|(index, lane_id)| {
            GlobalEconomicLaneStateRootV1::new(lane_id, root(seed + index as u16))
        })
        .collect()
}

pub fn partition_roots(
    object_release_registry_root: CommitmentV3,
) -> GlobalEconomicPartitionRootsV1 {
    GlobalEconomicPartitionRootsV1::new(GlobalEconomicPartitionRootsInputV1 {
        balances_root: root(300),
        supplies_root: root(301),
        custody_root: root(302),
        liabilities_root: root(303),
        reserves_root: root(304),
        oracle_occurrences_root: root(305),
        replay_state_root: root(306),
        terminal_obligations_root: root(307),
        release_observations_root: root(308),
        history_root: root(309),
        external_outbox_root: root(310),
        object_release_registry_root,
    })
}

pub fn state_content_with_lanes(
    lane_state_roots: Vec<GlobalEconomicLaneStateRootV1>,
) -> Result<GlobalEconomicStateContentV1, GlobalEconomicStateErrorV1> {
    GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
        application_id: application_id(1),
        chain_or_domain_id: domain_id(2),
        height: 500,
        writer_epoch: 9,
        profile_id: profile_id(3),
        lane_state_roots,
        partition_roots: partition_roots(root(900)),
    })
}

pub fn fixture() -> EconomicRegistryFixture {
    economic_fixture(
        &[EconomicLaneIdV1::AssetTransfer],
        EconomicLaneIdV1::AssetTransfer,
        LaneModuleReleaseStatusV1::ActiveNew,
    )
}

pub fn object_pin_proof(
    object_id: CommitmentV3,
    lane_id: EconomicLaneIdV1,
    release_id: LaneModuleReleaseIdV1,
    sibling_seed: u16,
) -> EconomicObjectReleasePinProofV1 {
    let pin = EconomicObjectReleasePinV1::new(object_id, lane_id, release_id);
    let siblings =
        SparseMerkleSiblingPathV1::new([root(sibling_seed); SPARSE_MERKLE_TREE_DEPTH_V1]);
    EconomicObjectReleasePinProofV1::new(pin, siblings).unwrap()
}

pub fn state_for_fixture(
    fixture: &EconomicRegistryFixture,
    object_release_registry_root: CommitmentV3,
) -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1::new(
        GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
            application_id: application_id(1),
            chain_or_domain_id: domain_id(2),
            height: 500,
            writer_epoch: fixture.profile.content().writer_epoch(),
            profile_id: fixture.profile.profile_id(),
            lane_state_roots: lane_state_roots(100),
            partition_roots: partition_roots(object_release_registry_root),
        })
        .unwrap(),
    )
    .unwrap()
}

pub fn occurrence_for_state(
    fixture: &EconomicRegistryFixture,
    state: &GlobalEconomicStateV1,
    consumed_object_ids: Vec<CommitmentV3>,
) -> EconomicCommandOccurrenceV1 {
    occurrence_with_context(
        fixture,
        state.content().application_id(),
        state.content().chain_or_domain_id(),
        CommitmentV3::new(state.state_root().into_bytes()).unwrap(),
        consumed_object_ids,
    )
}

pub fn occurrence_with_context(
    fixture: &EconomicRegistryFixture,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    pre_state_root: CommitmentV3,
    consumed_object_ids: Vec<CommitmentV3>,
) -> EconomicCommandOccurrenceV1 {
    let route = &fixture.route_registry.routes()[0];
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id,
        chain_or_domain_id,
        action_type_id: EconomicActionTypeIdV1::new(
            route.content().command_variant_root().into_bytes(),
        )
        .unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([3; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([4; 32]).unwrap(),
        authorization_nonce: 17,
        valid_from_epoch: 0,
        valid_through_epoch: u64::MAX,
        pre_state_root,
        action_semantics_hash: root(6),
        effect_commitment: root(7),
        consumed_object_ids,
    })
    .unwrap();
    let action =
        AuthorizedEconomicActionV1::new(record, AuthorizationGrantIdV1::new([8; 32]).unwrap())
            .unwrap();
    EconomicCommandOccurrenceV1::new(
        EconomicCommandOccurrenceContentV1::new(
            EconomicOccurrencePositionV1::new(500, 7, 11),
            fixture.profile.profile_id(),
            fixture.profile.content().writer_epoch(),
            route.route_release_id(),
            action,
        )
        .unwrap(),
    )
    .unwrap()
}
