use super::support::*;

#[test]
fn exact_profile_registries_state_and_object_pin_construct_an_opaque_witness() {
    // Arrange.
    let fixture = fixture();
    let object_id = root(800);
    let release_id = fixture.module_registries[0].releases()[0].release_id();
    let proof = object_pin_proof(object_id, EconomicLaneIdV1::AssetTransfer, release_id, 700);
    let state = state_for_fixture(&fixture, proof.derive_registry_root().unwrap());
    let occurrence = occurrence_for_state(&fixture, &state, vec![object_id]);
    let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
        &fixture.profile,
        &fixture.route_registry,
        &occurrence,
    )
    .unwrap();
    let profile_state = bind_global_economic_state_to_profile_v1(
        &state,
        &fixture.profile,
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    )
    .unwrap();
    let proofs = [proof];

    // Act.
    let bound = bind_profile_bound_occurrence_to_global_state_v1(
        profile_occurrence,
        profile_state,
        &proofs,
    )
    .unwrap();

    // Assert.
    assert_eq!(bound.global_state(), &state);
    assert_eq!(bound.profile_bound_occurrence().occurrence(), &occurrence);
    assert_eq!(bound.object_release_pin_proofs(), &proofs);
    assert_eq!(
        bound.profile_state().lane_registry(),
        &fixture.lane_registry
    );
    assert_eq!(
        bound.profile_state().route_registry(),
        &fixture.route_registry
    );
}

#[test]
fn application_domain_and_pre_state_root_are_exact_binding_inputs() {
    // Arrange.
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let profile_state = || {
        bind_global_economic_state_to_profile_v1(
            &state,
            &fixture.profile,
            &fixture.lane_registry,
            &fixture.module_registries,
            &fixture.route_registry,
        )
        .unwrap()
    };
    let cases = [
        (
            application_id(99),
            state.content().chain_or_domain_id(),
            CommitmentV3::new(state.state_root().into_bytes()).unwrap(),
            GlobalEconomicStateErrorV1::ApplicationMismatch,
        ),
        (
            state.content().application_id(),
            domain_id(99),
            CommitmentV3::new(state.state_root().into_bytes()).unwrap(),
            GlobalEconomicStateErrorV1::ChainOrDomainMismatch,
        ),
        (
            state.content().application_id(),
            state.content().chain_or_domain_id(),
            root(999),
            GlobalEconomicStateErrorV1::PreStateRootMismatch,
        ),
    ];

    // Act.
    let actual: Vec<_> = cases
        .into_iter()
        .map(|(application_id, domain_id, pre_state_root, expected)| {
            let occurrence = occurrence_with_context(
                &fixture,
                application_id,
                domain_id,
                pre_state_root,
                vec![],
            );
            let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
                &fixture.profile,
                &fixture.route_registry,
                &occurrence,
            )
            .unwrap();
            let rejection = rejection(bind_profile_bound_occurrence_to_global_state_v1(
                profile_occurrence,
                profile_state(),
                &[],
            ));
            (rejection, expected)
        })
        .collect();

    // Assert.
    assert!(actual
        .into_iter()
        .all(|(rejection, expected)| rejection == expected));
}

#[test]
fn state_profile_writer_and_registry_drift_reject_before_authority_construction() {
    // Arrange.
    let fixture = fixture();
    let state = state_for_fixture(&fixture, root(900));
    let foreign_fixture = economic_fixture(
        &[EconomicLaneIdV1::SpotLiquidity],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let mut wrong_writer_content = state.content().clone();
    wrong_writer_content = GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
        writer_epoch: state.content().writer_epoch() + 1,
        application_id: wrong_writer_content.application_id(),
        chain_or_domain_id: wrong_writer_content.chain_or_domain_id(),
        height: wrong_writer_content.height(),
        profile_id: wrong_writer_content.profile_id(),
        lane_state_roots: wrong_writer_content.lane_state_roots().to_vec(),
        partition_roots: wrong_writer_content.partition_roots(),
    })
    .unwrap();
    let wrong_writer = GlobalEconomicStateV1::new(wrong_writer_content).unwrap();

    // Act.
    let wrong_profile = bind_global_economic_state_to_profile_v1(
        &state,
        &foreign_fixture.profile,
        &foreign_fixture.lane_registry,
        &foreign_fixture.module_registries,
        &foreign_fixture.route_registry,
    );
    let writer = bind_global_economic_state_to_profile_v1(
        &wrong_writer,
        &fixture.profile,
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    );
    let foreign_registry = bind_global_economic_state_to_profile_v1(
        &state,
        &fixture.profile,
        &foreign_fixture.lane_registry,
        &foreign_fixture.module_registries,
        &foreign_fixture.route_registry,
    );

    // Assert.
    assert_eq!(
        rejection(wrong_profile),
        GlobalEconomicStateErrorV1::ProfileMismatch
    );
    assert_eq!(
        rejection(writer),
        GlobalEconomicStateErrorV1::WriterEpochMismatch
    );
    assert!(matches!(
        rejection(foreign_registry),
        GlobalEconomicStateErrorV1::EconomicProfileBinding(_)
    ));
}

#[test]
fn occurrence_state_and_pin_relations_fail_closed_by_outcome_partition() {
    // Arrange.
    let fixture = fixture();
    let object_id = root(800);
    let release_id = fixture.module_registries[0].releases()[0].release_id();
    let proof = object_pin_proof(object_id, EconomicLaneIdV1::AssetTransfer, release_id, 700);
    let state = state_for_fixture(&fixture, proof.derive_registry_root().unwrap());

    // Act / Assert: zero consumed objects and zero proofs are exact.
    let empty_occurrence = occurrence_for_state(&fixture, &state, vec![]);
    let empty_profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
        &fixture.profile,
        &fixture.route_registry,
        &empty_occurrence,
    )
    .unwrap();
    let empty_profile_state = bind_global_economic_state_to_profile_v1(
        &state,
        &fixture.profile,
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    )
    .unwrap();
    assert!(bind_profile_bound_occurrence_to_global_state_v1(
        empty_profile_occurrence,
        empty_profile_state,
        &[],
    )
    .is_ok());

    // Arrange reusable one-object witnesses.
    let occurrence = occurrence_for_state(&fixture, &state, vec![object_id]);
    let reject = |proofs: &[EconomicObjectReleasePinProofV1]| {
        let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
            &fixture.profile,
            &fixture.route_registry,
            &occurrence,
        )
        .unwrap();
        let profile_state = bind_global_economic_state_to_profile_v1(
            &state,
            &fixture.profile,
            &fixture.lane_registry,
            &fixture.module_registries,
            &fixture.route_registry,
        )
        .unwrap();
        rejection(bind_profile_bound_occurrence_to_global_state_v1(
            profile_occurrence,
            profile_state,
            proofs,
        ))
    };
    let wrong_object =
        object_pin_proof(root(801), EconomicLaneIdV1::AssetTransfer, release_id, 700);
    let wrong_root = object_pin_proof(object_id, EconomicLaneIdV1::AssetTransfer, release_id, 701);

    // Act / Assert.
    assert_eq!(
        reject(&[]),
        GlobalEconomicStateErrorV1::ObjectPinProofCountMismatch {
            actual: 0,
            expected: 1,
        }
    );
    assert_eq!(
        reject(&[proof.clone(), proof.clone()]),
        GlobalEconomicStateErrorV1::ObjectPinProofCountMismatch {
            actual: 2,
            expected: 1,
        }
    );
    assert_eq!(
        reject(&[wrong_object]),
        GlobalEconomicStateErrorV1::ObjectPinObjectMismatch { position: 0 }
    );
    assert_eq!(
        reject(&[wrong_root]),
        GlobalEconomicStateErrorV1::ObjectPinRegistryRootMismatch { position: 0 }
    );
}

#[test]
fn unknown_or_lifecycle_disallowed_creating_release_rejects_even_with_valid_membership() {
    // Arrange unknown release.
    let fixture = fixture();
    let object_id = root(800);
    let unknown_release = lane_release_id(999);
    let unknown_proof = object_pin_proof(
        object_id,
        EconomicLaneIdV1::AssetTransfer,
        unknown_release,
        700,
    );
    let unknown_state = state_for_fixture(&fixture, unknown_proof.derive_registry_root().unwrap());
    let unknown_occurrence = occurrence_for_state(&fixture, &unknown_state, vec![object_id]);
    let unknown_profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
        &fixture.profile,
        &fixture.route_registry,
        &unknown_occurrence,
    )
    .unwrap();
    let unknown_profile_state = bind_global_economic_state_to_profile_v1(
        &unknown_state,
        &fixture.profile,
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    )
    .unwrap();

    // Act unknown release.
    let unknown_proofs = [unknown_proof];
    let unknown = rejection(bind_profile_bound_occurrence_to_global_state_v1(
        unknown_profile_occurrence,
        unknown_profile_state,
        &unknown_proofs,
    ));

    // Assert unknown release.
    assert_eq!(
        unknown,
        GlobalEconomicStateErrorV1::UnknownCreatingRelease {
            lane_id: EconomicLaneIdV1::AssetTransfer,
            release_id: unknown_release,
        }
    );

    // Arrange lifecycle-disallowed release and an independently governed route.
    let shadow_fixture = economic_fixture(
        &[EconomicLaneIdV1::AssetTransfer],
        EconomicLaneIdV1::AssetTransfer,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let shadow_release = crate::profile_support::module_release(
        EconomicLaneIdV1::SpotLiquidity,
        990,
        LaneModuleReleaseStatusV1::Shadow,
    );
    let shadow_proof = object_pin_proof(
        object_id,
        EconomicLaneIdV1::SpotLiquidity,
        shadow_release.release_id(),
        710,
    );
    let mut module_registries = shadow_fixture.module_registries.clone();
    module_registries[1] = zenodex_zrpf_protocol_v3::LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        vec![shadow_release.clone()],
    )
    .unwrap();
    let entries = module_registries
        .iter()
        .map(|registry| {
            zenodex_zrpf_protocol_v3::EconomicLaneRegistryEntryV1::new(
                registry.lane_id(),
                if registry.lane_id() == EconomicLaneIdV1::AssetTransfer {
                    zenodex_zrpf_protocol_v3::EconomicLaneCommandStatusV1::Enabled
                } else {
                    zenodex_zrpf_protocol_v3::EconomicLaneCommandStatusV1::Disabled
                },
                registry.canonical_root().unwrap(),
            )
        })
        .collect();
    let lane_registry =
        zenodex_zrpf_protocol_v3::GlobalEconomicLaneRegistryV1::new(entries).unwrap();
    let profile_roots = zenodex_zrpf_protocol_v3::EconomicProfileRegistryRootsV1::new(
        lane_registry.canonical_commitment().unwrap(),
        shadow_fixture.route_registry.canonical_root().unwrap(),
        root(600),
        root(601),
        root(602),
        root(603),
        root(604),
    );
    let profile = crate::profile_support::profile(
        0,
        0,
        zenodex_zrpf_protocol_v3::EconomicProfileTransitionModeV1::Genesis,
        None,
        profile_roots,
    );
    let state = GlobalEconomicStateV1::new(
        GlobalEconomicStateContentV1::new(GlobalEconomicStateContentInputV1 {
            application_id: application_id(1),
            chain_or_domain_id: domain_id(2),
            height: 500,
            writer_epoch: 0,
            profile_id: profile.profile_id(),
            lane_state_roots: lane_state_roots(100),
            partition_roots: partition_roots(shadow_proof.derive_registry_root().unwrap()),
        })
        .unwrap(),
    )
    .unwrap();
    let occurrence = {
        let fixture_view = EconomicRegistryFixture {
            profile,
            lane_registry,
            module_registries,
            route_registry: shadow_fixture.route_registry,
        };
        let occurrence = occurrence_for_state(&fixture_view, &state, vec![object_id]);
        let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
            &fixture_view.profile,
            &fixture_view.route_registry,
            &occurrence,
        )
        .unwrap();
        let profile_state = bind_global_economic_state_to_profile_v1(
            &state,
            &fixture_view.profile,
            &fixture_view.lane_registry,
            &fixture_view.module_registries,
            &fixture_view.route_registry,
        )
        .unwrap();
        let shadow_proofs = [shadow_proof];
        let result = rejection(bind_profile_bound_occurrence_to_global_state_v1(
            profile_occurrence,
            profile_state,
            &shadow_proofs,
        ));
        (result, shadow_release)
    };

    // Assert lifecycle rejection.
    assert!(matches!(
        occurrence.0,
        GlobalEconomicStateErrorV1::CreatingReleaseAdmission {
            lane_id: EconomicLaneIdV1::SpotLiquidity,
            ..
        }
    ));
}
