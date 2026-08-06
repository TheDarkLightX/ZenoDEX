use zenodex_zrpf_protocol_v3::{EconomicProfileSnapshotErrorV1, EconomicProfileTransitionModeV1};

use super::support::{profile, registry_roots};

#[test]
fn successor_requires_exact_predecessor_and_strict_epoch_rotation() {
    // Arrange
    let previous = profile(
        10,
        20,
        EconomicProfileTransitionModeV1::Genesis,
        None,
        registry_roots(10),
    );
    let exact = profile(
        11,
        21,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(previous.profile_id()),
        registry_roots(20),
    );
    let wrong_predecessor = profile(
        11,
        21,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(exact.profile_id()),
        registry_roots(20),
    );
    let same_authority_epoch = profile(
        10,
        21,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(previous.profile_id()),
        registry_roots(20),
    );
    let lower_authority_epoch = profile(
        9,
        21,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(previous.profile_id()),
        registry_roots(20),
    );
    let same_writer_epoch = profile(
        11,
        20,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(previous.profile_id()),
        registry_roots(20),
    );
    let lower_writer_epoch = profile(
        11,
        19,
        EconomicProfileTransitionModeV1::GovernanceUpdate,
        Some(previous.profile_id()),
        registry_roots(20),
    );
    let genesis = profile(
        11,
        21,
        EconomicProfileTransitionModeV1::Genesis,
        None,
        registry_roots(20),
    );

    // Act / Assert
    assert_eq!(exact.validate_successor_of(&previous), Ok(()));
    assert_eq!(
        wrong_predecessor.validate_successor_of(&previous),
        Err(EconomicProfileSnapshotErrorV1::PredecessorProfileMismatch)
    );
    for candidate in [same_authority_epoch, lower_authority_epoch] {
        assert_eq!(
            candidate.validate_successor_of(&previous),
            Err(EconomicProfileSnapshotErrorV1::AuthorityEpochNotIncreasing)
        );
    }
    for candidate in [same_writer_epoch, lower_writer_epoch] {
        assert_eq!(
            candidate.validate_successor_of(&previous),
            Err(EconomicProfileSnapshotErrorV1::WriterEpochNotRotated)
        );
    }
    assert_eq!(
        genesis.validate_successor_of(&previous),
        Err(EconomicProfileSnapshotErrorV1::GenesisCannotBeSuccessor)
    );
}
