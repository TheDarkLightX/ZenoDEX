pub use serde::Serialize;
pub use sha2::{Digest, Sha256};
pub use zenodex_zrpf_protocol_v3::{
    bind_economic_command_occurrence_to_active_profile_v1,
    decode_exact_economic_command_occurrence_v1, encode_economic_command_occurrence_v1,
    ApplicationIdV3, AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
    AuthorizedEconomicActionV1, CommitmentV3, DomainIdV3, EconomicActionRecordInputV1,
    EconomicActionRecordV1, EconomicActionTypeIdV1, EconomicCommandOccurrenceContentV1,
    EconomicCommandOccurrenceErrorV1, EconomicCommandOccurrenceIdV1, EconomicCommandOccurrenceV1,
    EconomicLaneIdV1, EconomicOccurrencePositionV1, EconomicProfileIdV1,
    EconomicProfileRegistryRootsV1, EconomicProfileSnapshotContentV1, EconomicProfileSnapshotV1,
    EconomicProfileTransitionModeV1, LaneModuleReleaseIdV1, RouteDependencyRoleV1,
    RouteDependencyRolesV1, RouteIssueBurnPolicyV1, RouteModuleDependencyV1, RouteOraclePolicyV1,
    RouteReleaseContentV1, RouteReleaseRegistryV1, RouteReleaseV1, RouteResourceLimitsV1,
    MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1,
};

const OCCURRENCE_ID_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.economic_command_occurrence_id.v1";

pub fn root(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

pub fn route(command_variant_root: CommitmentV3, release_seed: u8) -> RouteReleaseV1 {
    let roles = RouteDependencyRolesV1::new(&[RouteDependencyRoleV1::Primary]).unwrap();
    let dependency = RouteModuleDependencyV1::new(
        EconomicLaneIdV1::AssetTransfer,
        LaneModuleReleaseIdV1::new([release_seed; 32]).unwrap(),
        roles,
        root(31),
        root(32),
        root(33),
    );
    RouteReleaseV1::new(
        RouteReleaseContentV1::new(
            command_variant_root,
            vec![dependency],
            root(34),
            RouteOraclePolicyV1::Forbidden,
            RouteIssueBurnPolicyV1::Forbidden,
            RouteResourceLimitsV1::new(4_096, 2_048, 1_000_000).unwrap(),
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn profile(
    route_registry: &RouteReleaseRegistryV1,
    writer_epoch: u64,
) -> EconomicProfileSnapshotV1 {
    let roots = EconomicProfileRegistryRootsV1::new(
        root(40),
        route_registry.canonical_root().unwrap(),
        root(42),
        root(43),
        root(44),
        root(45),
        root(46),
    );
    EconomicProfileSnapshotV1::new(
        EconomicProfileSnapshotContentV1::new(
            100,
            writer_epoch,
            EconomicProfileTransitionModeV1::Genesis,
            None,
            roots,
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn authorized_action(
    command_variant_root: CommitmentV3,
    nonce: u64,
    consumed_object_ids: Vec<CommitmentV3>,
) -> AuthorizedEconomicActionV1 {
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        action_type_id: EconomicActionTypeIdV1::new(command_variant_root.into_bytes()).unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([3; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([4; 32]).unwrap(),
        authorization_nonce: nonce,
        valid_from_epoch: 0,
        valid_through_epoch: u64::MAX,
        pre_state_root: root(5),
        action_semantics_hash: root(6),
        effect_commitment: root(7),
        consumed_object_ids,
    })
    .unwrap();
    AuthorizedEconomicActionV1::new(record, AuthorizationGrantIdV1::new([8; 32]).unwrap()).unwrap()
}

pub fn occurrence(
    profile: &EconomicProfileSnapshotV1,
    route: &RouteReleaseV1,
) -> EconomicCommandOccurrenceV1 {
    let content = EconomicCommandOccurrenceContentV1::new(
        EconomicOccurrencePositionV1::new(500, 7, 11),
        profile.profile_id(),
        profile.content().writer_epoch(),
        route.route_release_id(),
        authorized_action(
            route.content().command_variant_root(),
            17,
            vec![root(10), root(9)],
        ),
    )
    .unwrap();
    EconomicCommandOccurrenceV1::new(content).unwrap()
}

fn prefixed_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

pub fn manual_occurrence_id(occurrence: &EconomicCommandOccurrenceV1) -> [u8; 32] {
    let content = occurrence.content();
    let position = content.position();
    let mut hasher = prefixed_hasher(OCCURRENCE_ID_DOMAIN_V1);
    hasher.update(occurrence.occurrence_version().to_be_bytes());
    hasher.update(position.height().to_be_bytes());
    hasher.update(position.tx_index().to_be_bytes());
    hasher.update(position.op_index().to_be_bytes());
    hasher.update(content.profile_id().as_bytes());
    hasher.update(content.writer_epoch().to_be_bytes());
    hasher.update(content.route_release_id().as_bytes());
    hasher.update(
        content
            .authorized_action()
            .canonical_hash()
            .unwrap()
            .as_bytes(),
    );
    hasher.finalize().into()
}
