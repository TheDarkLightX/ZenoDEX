use zenodex_zrpf_protocol_v3::{
    EconomicProfileSnapshotContentV1, EconomicProfileSnapshotErrorV1,
    EconomicProfileTransitionModeV1,
};

#[path = "economic_profile_snapshot_v1/binding.rs"]
mod binding;
#[path = "economic_profile_snapshot_v1/codec.rs"]
mod codec;
#[path = "economic_profile_snapshot_v1/identity.rs"]
mod identity;
#[path = "economic_profile_snapshot_v1/successor.rs"]
mod successor;
#[path = "economic_profile_snapshot_v1/support.rs"]
mod support;

use support::{profile_id, registry_roots};

#[test]
fn transition_mode_and_predecessor_cardinality_are_exact() {
    // Arrange
    let predecessor = profile_id(1);

    // Act
    let genesis = EconomicProfileSnapshotContentV1::new(
        0,
        0,
        EconomicProfileTransitionModeV1::Genesis,
        None,
        registry_roots(10),
    );
    let genesis_with_predecessor = EconomicProfileSnapshotContentV1::new(
        1,
        1,
        EconomicProfileTransitionModeV1::Genesis,
        Some(predecessor),
        registry_roots(10),
    );
    let governance_without_predecessor = EconomicProfileSnapshotContentV1::new(
        1,
        1,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        None,
        registry_roots(10),
    );
    let migration_without_predecessor = EconomicProfileSnapshotContentV1::new(
        1,
        1,
        EconomicProfileTransitionModeV1::ProvedMigration,
        None,
        registry_roots(10),
    );

    // Assert
    assert!(genesis.is_ok());
    assert_eq!(
        genesis_with_predecessor,
        Err(EconomicProfileSnapshotErrorV1::GenesisHasPredecessor)
    );
    assert_eq!(
        governance_without_predecessor,
        Err(
            EconomicProfileSnapshotErrorV1::TransitionRequiresPredecessor(
                EconomicProfileTransitionModeV1::GovernanceUpdate
            )
        )
    );
    assert_eq!(
        migration_without_predecessor,
        Err(
            EconomicProfileSnapshotErrorV1::TransitionRequiresPredecessor(
                EconomicProfileTransitionModeV1::ProvedMigration
            )
        )
    );
}

#[test]
fn authority_and_writer_epoch_values_cover_zero_one_and_integer_maximum() {
    // Arrange / Act
    let snapshots: Vec<_> = [0, 1, u64::MAX]
        .into_iter()
        .map(|epoch| {
            EconomicProfileSnapshotContentV1::new(
                epoch,
                epoch,
                EconomicProfileTransitionModeV1::Genesis,
                None,
                registry_roots(20),
            )
            .unwrap()
        })
        .collect();

    // Assert
    assert_eq!(snapshots[0].authority_epoch(), 0);
    assert_eq!(snapshots[1].writer_epoch(), 1);
    assert_eq!(snapshots[2].authority_epoch(), u64::MAX);
    assert_eq!(snapshots[2].writer_epoch(), u64::MAX);
}
