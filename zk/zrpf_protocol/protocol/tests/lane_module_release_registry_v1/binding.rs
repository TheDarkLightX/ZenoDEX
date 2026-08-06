use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicLaneCommandStatusV1, EconomicLaneIdV1, EconomicLaneRegistryEntryV1,
    LaneModuleReleaseRegistryErrorV1, LaneModuleReleaseStatusV1,
};

use super::support::{hex32, independent_registry_root, registry, release, root};

#[test]
fn registry_root_matches_an_independent_mirror_and_binds_the_global_lane_row() {
    // Arrange
    let registry = registry(vec![
        release(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            LaneModuleReleaseStatusV1::Candidate,
            None,
        ),
        release(
            EconomicLaneIdV1::SpotLiquidity,
            2,
            LaneModuleReleaseStatusV1::ActiveNew,
            None,
        ),
    ]);
    let expected = independent_registry_root(&registry);
    let correct = entry(EconomicLaneIdV1::SpotLiquidity, expected);
    let wrong_lane = entry(EconomicLaneIdV1::AssetTransfer, expected);
    let wrong_root = entry(EconomicLaneIdV1::SpotLiquidity, root(99, 0));

    // Act
    let actual = registry.canonical_root().unwrap();

    // Assert
    assert_eq!(actual, expected);
    assert_eq!(
        hex32(*actual.as_bytes()),
        "73f1c33fa26c0b108b9eaea69023f17cf8f2e147ce2b85276c1027ba0a58a9aa"
    );
    assert_eq!(registry.bind_global_lane_entry(&correct), Ok(()));
    assert!(matches!(
        registry.bind_global_lane_entry(&wrong_lane),
        Err(LaneModuleReleaseRegistryErrorV1::LaneEntryMismatch { .. })
    ));
    assert_eq!(
        registry.bind_global_lane_entry(&wrong_root),
        Err(LaneModuleReleaseRegistryErrorV1::RegistryRootMismatch)
    );
}

#[test]
fn registry_root_binds_lifecycle_status_while_release_identity_does_not() {
    // Arrange
    let candidate = release(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    );
    let shadow = candidate
        .transition_status(LaneModuleReleaseStatusV1::Shadow)
        .unwrap();

    // Act
    let candidate_root = registry(vec![candidate.clone()]).canonical_root().unwrap();
    let shadow_root = registry(vec![shadow.clone()]).canonical_root().unwrap();

    // Assert
    assert_eq!(candidate.release_id(), shadow.release_id());
    assert_ne!(candidate_root, shadow_root);
}

fn entry(lane_id: EconomicLaneIdV1, root: CommitmentV3) -> EconomicLaneRegistryEntryV1 {
    EconomicLaneRegistryEntryV1::new(lane_id, EconomicLaneCommandStatusV1::Enabled, root)
}
