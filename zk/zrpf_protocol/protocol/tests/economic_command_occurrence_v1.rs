#[path = "economic_command_occurrence_v1/codec.rs"]
mod codec;
#[path = "economic_command_occurrence_v1/support.rs"]
mod support;

use support::*;

#[test]
fn constructor_binds_exact_position_profile_route_and_authorized_action() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);

    // Act.
    let occurrence = occurrence(&active_profile, &governed_route);

    // Assert.
    assert_eq!(
        occurrence.content().position(),
        EconomicOccurrencePositionV1::new(500, 7, 11)
    );
    assert_eq!(
        occurrence.content().profile_id(),
        active_profile.profile_id()
    );
    assert_eq!(occurrence.content().writer_epoch(), 9);
    assert_eq!(
        occurrence.content().route_release_id(),
        governed_route.route_release_id()
    );
    assert_eq!(
        occurrence.occurrence_id().into_bytes(),
        manual_occurrence_id(&occurrence)
    );
    assert_eq!(
        occurrence.occurrence_id().into_bytes(),
        [
            54, 164, 66, 208, 188, 118, 247, 197, 101, 185, 31, 188, 250, 215, 74, 149, 110, 226,
            179, 197, 91, 136, 85, 58, 218, 41, 120, 221, 124, 169, 113, 23,
        ]
    );
    assert_eq!(
        occurrence
            .content()
            .authorized_action()
            .record()
            .consumed_object_ids(),
        &[root(9), root(10)]
    );
}

#[test]
fn position_bva_accepts_zero_and_integer_maxima_with_total_lexicographic_order() {
    // Arrange.
    let minimum = EconomicOccurrencePositionV1::new(0, 0, 0);
    let maximum = EconomicOccurrencePositionV1::new(u64::MAX, u32::MAX, u32::MAX);
    let next_op = EconomicOccurrencePositionV1::new(0, 0, 1);
    let next_tx = EconomicOccurrencePositionV1::new(0, 1, 0);
    let next_height = EconomicOccurrencePositionV1::new(1, 0, 0);

    // Act.
    let mut positions = vec![maximum, next_height, next_tx, next_op, minimum];
    positions.sort_unstable();

    // Assert.
    assert_eq!(
        positions,
        vec![minimum, next_op, next_tx, next_height, maximum]
    );
}

#[test]
fn every_occurrence_envelope_field_separates_identity() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let alternate_route = route(root(20), 22);
    let registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&registry, 9);
    let baseline = occurrence(&active_profile, &governed_route);
    let baseline_id = baseline.occurrence_id();
    let base = baseline.content();
    let positions = [
        EconomicOccurrencePositionV1::new(501, 7, 11),
        EconomicOccurrencePositionV1::new(500, 8, 11),
        EconomicOccurrencePositionV1::new(500, 7, 12),
    ];

    // Act / Assert.
    for position in positions {
        let changed = EconomicCommandOccurrenceV1::new(
            EconomicCommandOccurrenceContentV1::new(
                position,
                base.profile_id(),
                base.writer_epoch(),
                base.route_release_id(),
                base.authorized_action().clone(),
            )
            .unwrap(),
        )
        .unwrap();
        assert_ne!(changed.occurrence_id(), baseline_id);
    }
    for changed in [
        EconomicCommandOccurrenceContentV1::new(
            base.position(),
            EconomicProfileIdV1::new([91; 32]).unwrap(),
            base.writer_epoch(),
            base.route_release_id(),
            base.authorized_action().clone(),
        ),
        EconomicCommandOccurrenceContentV1::new(
            base.position(),
            base.profile_id(),
            base.writer_epoch() + 1,
            base.route_release_id(),
            base.authorized_action().clone(),
        ),
        EconomicCommandOccurrenceContentV1::new(
            base.position(),
            base.profile_id(),
            base.writer_epoch(),
            alternate_route.route_release_id(),
            base.authorized_action().clone(),
        ),
    ] {
        assert_ne!(
            EconomicCommandOccurrenceV1::new(changed.unwrap())
                .unwrap()
                .occurrence_id(),
            baseline_id
        );
    }
    let changed_action = authorized_action(
        governed_route.content().command_variant_root(),
        18,
        vec![root(9), root(10)],
    );
    let changed = EconomicCommandOccurrenceV1::new(
        EconomicCommandOccurrenceContentV1::new(
            base.position(),
            base.profile_id(),
            base.writer_epoch(),
            base.route_release_id(),
            changed_action,
        )
        .unwrap(),
    )
    .unwrap();
    assert_ne!(changed.occurrence_id(), baseline_id);
}

#[test]
fn active_profile_binding_constructs_only_the_exact_structural_witness() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);
    let occurrence = occurrence(&active_profile, &governed_route);

    // Act.
    let bound = bind_economic_command_occurrence_to_active_profile_v1(
        &active_profile,
        &route_registry,
        &occurrence,
    )
    .unwrap();

    // Assert.
    assert_eq!(bound.occurrence(), &occurrence);
    assert_eq!(bound.route_release(), &governed_route);
}

#[test]
fn old_profile_occurrence_rejects_after_atomic_profile_activation() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let old_profile = profile(&route_registry, 9);
    let old_occurrence = occurrence(&old_profile, &governed_route);
    let successor = EconomicProfileSnapshotV1::new(
        EconomicProfileSnapshotContentV1::new(
            101,
            10,
            EconomicProfileTransitionModeV1::GovernanceUpdate,
            Some(old_profile.profile_id()),
            old_profile.content().registry_roots(),
        )
        .unwrap(),
    )
    .unwrap();

    // Act.
    let result = bind_economic_command_occurrence_to_active_profile_v1(
        &successor,
        &route_registry,
        &old_occurrence,
    );

    // Assert.
    assert_eq!(
        result.unwrap_err(),
        EconomicCommandOccurrenceErrorV1::ProfileIdMismatch
    );
    assert_eq!(
        old_occurrence.content().profile_id(),
        old_profile.profile_id()
    );
}

#[test]
fn profile_binding_rejects_writer_registry_route_and_command_substitution() {
    // Arrange.
    let governed_route = route(root(20), 21);
    let route_registry = RouteReleaseRegistryV1::new(vec![governed_route.clone()]).unwrap();
    let active_profile = profile(&route_registry, 9);
    let base = occurrence(&active_profile, &governed_route);
    let wrong_writer = EconomicCommandOccurrenceV1::new(
        EconomicCommandOccurrenceContentV1::new(
            base.content().position(),
            active_profile.profile_id(),
            10,
            governed_route.route_release_id(),
            base.content().authorized_action().clone(),
        )
        .unwrap(),
    )
    .unwrap();
    let foreign_route = route(root(20), 22);
    let foreign_registry = RouteReleaseRegistryV1::new(vec![foreign_route.clone()]).unwrap();
    let unknown_route_occurrence = EconomicCommandOccurrenceV1::new(
        EconomicCommandOccurrenceContentV1::new(
            base.content().position(),
            active_profile.profile_id(),
            9,
            foreign_route.route_release_id(),
            base.content().authorized_action().clone(),
        )
        .unwrap(),
    )
    .unwrap();
    let mismatched_command = EconomicCommandOccurrenceV1::new(
        EconomicCommandOccurrenceContentV1::new(
            base.content().position(),
            active_profile.profile_id(),
            9,
            governed_route.route_release_id(),
            authorized_action(root(99), 17, vec![root(9), root(10)]),
        )
        .unwrap(),
    )
    .unwrap();

    // Act / Assert.
    assert_eq!(
        bind_economic_command_occurrence_to_active_profile_v1(
            &active_profile,
            &route_registry,
            &wrong_writer,
        )
        .unwrap_err(),
        EconomicCommandOccurrenceErrorV1::WriterEpochMismatch
    );
    assert_eq!(
        bind_economic_command_occurrence_to_active_profile_v1(
            &active_profile,
            &foreign_registry,
            &unknown_route_occurrence,
        )
        .unwrap_err(),
        EconomicCommandOccurrenceErrorV1::RouteRegistryRootMismatch
    );
    assert_eq!(
        bind_economic_command_occurrence_to_active_profile_v1(
            &active_profile,
            &route_registry,
            &unknown_route_occurrence,
        )
        .unwrap_err(),
        EconomicCommandOccurrenceErrorV1::UnknownRouteRelease
    );
    assert_eq!(
        bind_economic_command_occurrence_to_active_profile_v1(
            &active_profile,
            &route_registry,
            &mismatched_command,
        )
        .unwrap_err(),
        EconomicCommandOccurrenceErrorV1::CommandVariantMismatch
    );
}
