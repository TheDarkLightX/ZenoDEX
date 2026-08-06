use zenodex_zrpf_protocol_v3::{
    EconomicProfileRegistryRootsV1, EconomicProfileSnapshotErrorV1, EconomicProfileTransitionModeV1,
};

use super::support::{hex32, profile, profile_id, registry_roots, root};

#[test]
fn profile_identity_binds_epochs_transition_predecessor_and_every_registry_root() {
    // Arrange
    let predecessor = profile_id(1);
    let roots = registry_roots(10);
    let baseline = profile(
        10,
        20,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(predecessor),
        roots,
    );
    let changed_roots = [
        EconomicProfileRegistryRootsV1::new(
            root(100),
            roots.route_release_registry_root(),
            roots.proof_shape_registry_root(),
            roots.verifier_registry_root(),
            roots.migration_registry_root(),
            roots.policy_registry_root(),
            roots.terminal_registry_root(),
        ),
        EconomicProfileRegistryRootsV1::new(
            roots.economic_lane_registry_root(),
            root(101),
            roots.proof_shape_registry_root(),
            roots.verifier_registry_root(),
            roots.migration_registry_root(),
            roots.policy_registry_root(),
            roots.terminal_registry_root(),
        ),
        EconomicProfileRegistryRootsV1::new(
            roots.economic_lane_registry_root(),
            roots.route_release_registry_root(),
            root(102),
            roots.verifier_registry_root(),
            roots.migration_registry_root(),
            roots.policy_registry_root(),
            roots.terminal_registry_root(),
        ),
        EconomicProfileRegistryRootsV1::new(
            roots.economic_lane_registry_root(),
            roots.route_release_registry_root(),
            roots.proof_shape_registry_root(),
            root(103),
            roots.migration_registry_root(),
            roots.policy_registry_root(),
            roots.terminal_registry_root(),
        ),
        EconomicProfileRegistryRootsV1::new(
            roots.economic_lane_registry_root(),
            roots.route_release_registry_root(),
            roots.proof_shape_registry_root(),
            roots.verifier_registry_root(),
            root(104),
            roots.policy_registry_root(),
            roots.terminal_registry_root(),
        ),
        EconomicProfileRegistryRootsV1::new(
            roots.economic_lane_registry_root(),
            roots.route_release_registry_root(),
            roots.proof_shape_registry_root(),
            roots.verifier_registry_root(),
            roots.migration_registry_root(),
            root(105),
            roots.terminal_registry_root(),
        ),
        EconomicProfileRegistryRootsV1::new(
            roots.economic_lane_registry_root(),
            roots.route_release_registry_root(),
            roots.proof_shape_registry_root(),
            roots.verifier_registry_root(),
            roots.migration_registry_root(),
            roots.policy_registry_root(),
            root(106),
        ),
    ];

    // Act
    let mut identities = vec![
        baseline.profile_id(),
        profile(
            11,
            20,
            EconomicProfileTransitionModeV1::GovernanceUpdate,
            Some(predecessor),
            roots,
        )
        .profile_id(),
        profile(
            10,
            21,
            EconomicProfileTransitionModeV1::GovernanceUpdate,
            Some(predecessor),
            roots,
        )
        .profile_id(),
        profile(
            10,
            20,
            EconomicProfileTransitionModeV1::ProvedMigration,
            Some(predecessor),
            roots,
        )
        .profile_id(),
        profile(
            10,
            20,
            EconomicProfileTransitionModeV1::GovernanceUpdate,
            Some(profile_id(2)),
            roots,
        )
        .profile_id(),
    ];
    identities.extend(changed_roots.into_iter().map(|changed| {
        profile(
            10,
            20,
            EconomicProfileTransitionModeV1::GovernanceUpdate,
            Some(predecessor),
            changed,
        )
        .profile_id()
    }));

    // Assert
    let unique: std::collections::BTreeSet<_> = identities.iter().copied().collect();
    assert_eq!(unique.len(), identities.len());
    assert_eq!(
        hex32(baseline.profile_id().into_bytes()),
        "c856e3c1e624a53f4ad0d6cb54e11abf179940632348050296f6ed0c876a7628"
    );
}

#[test]
fn zero_profile_id_rejects() {
    // Arrange / Act / Assert
    assert_eq!(
        zenodex_zrpf_protocol_v3::EconomicProfileIdV1::new([0; 32]),
        Err(EconomicProfileSnapshotErrorV1::ZeroProfileId)
    );
}
