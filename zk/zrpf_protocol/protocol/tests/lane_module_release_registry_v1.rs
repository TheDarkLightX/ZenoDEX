use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, LaneModuleReleaseErrorV1, LaneModuleReleaseIdV1,
    LaneModuleReleaseRegistryErrorV1, LaneModuleReleaseRegistryV1, LaneModuleReleaseStatusV1,
    LaneModuleReleaseV1, MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1,
};

#[path = "lane_module_release_registry_v1/binding.rs"]
mod binding;
#[path = "lane_module_release_registry_v1/codec.rs"]
mod codec;
#[path = "lane_module_release_registry_v1/support.rs"]
mod support;

use support::{canonical, registry, release};

fn unknown_release_id() -> LaneModuleReleaseIdV1 {
    LaneModuleReleaseIdV1::new([0xff; 32]).expect("fixture release ID is nonzero")
}

#[test]
fn release_count_boundaries_are_zero_one_sixty_four_and_sixty_five() {
    // Arrange
    let one = vec![release(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    )];
    let maximum = canonical(
        (1..=u8::try_from(MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1).unwrap())
            .map(|seed| {
                release(
                    EconomicLaneIdV1::SpotLiquidity,
                    seed,
                    LaneModuleReleaseStatusV1::Candidate,
                    None,
                )
            })
            .collect(),
    );
    let mut above_maximum = maximum.clone();
    above_maximum.push(release(
        EconomicLaneIdV1::SpotLiquidity,
        65,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    ));
    above_maximum = canonical(above_maximum);

    // Act
    let empty = LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, vec![]);
    let one_result = LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, one);
    let maximum_result = LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, maximum);
    let above_result =
        LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, above_maximum);

    // Assert
    assert_eq!(empty, Err(LaneModuleReleaseRegistryErrorV1::EmptyRegistry));
    assert_eq!(one_result.unwrap().releases().len(), 1);
    assert_eq!(
        maximum_result.unwrap().releases().len(),
        MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1
    );
    assert_eq!(
        above_result,
        Err(LaneModuleReleaseRegistryErrorV1::TooManyReleases {
            actual: MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1 + 1,
            maximum: MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1,
        })
    );
}

#[test]
fn lane_identity_release_identity_and_canonical_order_are_exact() {
    // Arrange
    let first = release(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    );
    let second = release(
        EconomicLaneIdV1::SpotLiquidity,
        2,
        LaneModuleReleaseStatusV1::Shadow,
        None,
    );
    let mixed = release(
        EconomicLaneIdV1::AssetTransfer,
        3,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    );
    let mut reversed = canonical(vec![first.clone(), second.clone()]);
    reversed.reverse();

    // Act
    let duplicate = LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        vec![first.clone(), first.clone()],
    );
    let wrong_lane = LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        canonical(vec![first, mixed]),
    );
    let wrong_order = LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, reversed);

    // Assert
    assert!(matches!(
        duplicate,
        Err(LaneModuleReleaseRegistryErrorV1::DuplicateReleaseId(_))
    ));
    assert!(matches!(
        wrong_lane,
        Err(LaneModuleReleaseRegistryErrorV1::MixedLane { .. })
    ));
    assert!(matches!(
        wrong_order,
        Err(LaneModuleReleaseRegistryErrorV1::NonCanonicalReleaseOrder { .. })
    ));
}

#[test]
fn active_new_cardinality_and_new_object_resolution_are_exact() {
    // Arrange
    let candidate = release(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    );
    let active = release(
        EconomicLaneIdV1::SpotLiquidity,
        2,
        LaneModuleReleaseStatusV1::ActiveNew,
        None,
    );
    let other_active = release(
        EconomicLaneIdV1::SpotLiquidity,
        3,
        LaneModuleReleaseStatusV1::ActiveNew,
        None,
    );
    let no_active = registry(vec![candidate.clone()]);
    let one_active = registry(vec![candidate, active.clone()]);
    let before = one_active.clone();

    // Act
    let none = no_active.resolve_new_object_release();
    let resolved = one_active.resolve_new_object_release();
    let duplicate_active = LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        canonical(vec![active.clone(), other_active]),
    );

    // Assert
    assert_eq!(
        none,
        Err(LaneModuleReleaseRegistryErrorV1::NoActiveNewRelease)
    );
    assert_eq!(resolved.unwrap().release_id(), active.release_id());
    assert_eq!(
        duplicate_active,
        Err(LaneModuleReleaseRegistryErrorV1::MultipleActiveNewReleases)
    );
    assert_eq!(one_active, before);
}

#[test]
fn every_migration_predecessor_must_be_reachable_in_the_same_registry() {
    // Arrange
    let genesis = release(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        LaneModuleReleaseStatusV1::DrainOnly,
        None,
    );
    let predecessor_release_id = genesis.release_id();
    let successor = release(
        EconomicLaneIdV1::SpotLiquidity,
        2,
        LaneModuleReleaseStatusV1::ActiveNew,
        Some(predecessor_release_id),
    );

    // Act
    let orphan =
        LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, vec![successor.clone()]);
    let connected = LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        canonical(vec![genesis, successor.clone()]),
    );

    // Assert
    assert_eq!(
        orphan,
        Err(LaneModuleReleaseRegistryErrorV1::MissingPredecessor {
            release_id: successor.release_id(),
            predecessor_release_id,
        })
    );
    assert!(connected.is_ok());
}

#[test]
fn existing_object_resolution_applies_release_status_and_rejects_without_mutation() {
    // Arrange
    let candidate = release(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        LaneModuleReleaseStatusV1::Candidate,
        None,
    );
    let drain = release(
        EconomicLaneIdV1::SpotLiquidity,
        2,
        LaneModuleReleaseStatusV1::DrainOnly,
        None,
    );
    let registry = registry(vec![candidate.clone(), drain.clone()]);
    let before = registry.clone();

    // Act
    let allowed = registry.resolve_existing_object_release(drain.release_id());
    let disallowed = registry.resolve_existing_object_release(candidate.release_id());
    let missing = registry.resolve_existing_object_release(unknown_release_id());

    // Assert
    assert_eq!(allowed.unwrap().release_id(), drain.release_id());
    assert_eq!(
        disallowed,
        Err(LaneModuleReleaseRegistryErrorV1::ReleaseAdmission(
            LaneModuleReleaseErrorV1::StatusDisallowsExistingObject(
                LaneModuleReleaseStatusV1::Candidate
            )
        ))
    );
    assert_eq!(
        missing,
        Err(LaneModuleReleaseRegistryErrorV1::UnknownRelease(
            unknown_release_id()
        ))
    );
    assert_eq!(registry, before);
}

#[test]
fn only_the_release_id_sorted_permutation_is_accepted() {
    // Arrange
    let releases = [
        release(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            LaneModuleReleaseStatusV1::Candidate,
            None,
        ),
        release(
            EconomicLaneIdV1::SpotLiquidity,
            2,
            LaneModuleReleaseStatusV1::Shadow,
            None,
        ),
        release(
            EconomicLaneIdV1::SpotLiquidity,
            3,
            LaneModuleReleaseStatusV1::VerifyOnly,
            None,
        ),
    ];
    let permutations = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let canonical_ids: Vec<_> = canonical(releases.to_vec())
        .iter()
        .map(LaneModuleReleaseV1::release_id)
        .collect();

    // Act
    let accepted = permutations
        .iter()
        .filter(|order| {
            let candidate: Vec<_> = order.iter().map(|index| releases[*index].clone()).collect();
            LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, candidate).is_ok()
        })
        .count();

    // Assert
    assert_eq!(accepted, 1);
    assert_eq!(
        registry(releases.to_vec())
            .releases()
            .iter()
            .map(LaneModuleReleaseV1::release_id)
            .collect::<Vec<_>>(),
        canonical_ids
    );
}
