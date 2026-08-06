use super::support::*;
use zenodex_zrpf_protocol_v3::{
    bind_economic_command_occurrence_to_active_profile_v1,
    bind_global_economic_state_to_profile_v1, bind_profile_bound_occurrence_to_global_state_v1,
    derive_sparse_merkle_leaf_commitment_v1, SparseMerkleSiblingPathV1,
    SPARSE_MERKLE_TREE_DEPTH_V1,
};

#[test]
fn zero_objects_select_active_new_and_reject_caller_proposed_drain_route() {
    // Arrange.
    let fixture = coexisting_fixture();
    let state = state_for_fixture(&fixture.registries, root(999));

    // Act.
    let active = bind_selected_route(&fixture.registries, &state, fixture.active_route_id, &[]);
    let proposed_drain =
        bind_selected_route(&fixture.registries, &state, fixture.drain_route_id, &[]);

    // Assert.
    assert!(active.is_ok());
    assert_eq!(
        rejection(proposed_drain),
        GlobalEconomicStateErrorV1::ProposedRouteMismatch {
            expected: fixture.active_route_id,
            actual: fixture.drain_route_id,
        }
    );
}

#[test]
fn old_object_pin_selects_drain_route_and_rejects_active_substitution() {
    // Arrange.
    let fixture = coexisting_fixture();
    let object_id = root(800);
    let proof = object_pin_proof(
        object_id,
        EconomicLaneIdV1::AssetTransfer,
        fixture.drain_release_id,
        700,
    );
    let state = state_for_fixture(&fixture.registries, proof.derive_registry_root().unwrap());
    let proofs = [proof];

    // Act.
    let drain = bind_selected_route(&fixture.registries, &state, fixture.drain_route_id, &proofs);
    let substituted = bind_selected_route(
        &fixture.registries,
        &state,
        fixture.active_route_id,
        &proofs,
    );

    // Assert.
    assert!(drain.is_ok());
    assert_eq!(
        rejection(substituted),
        GlobalEconomicStateErrorV1::ProposedRouteMismatch {
            expected: fixture.drain_route_id,
            actual: fixture.active_route_id,
        }
    );
}

#[test]
fn active_release_pin_remains_on_the_active_route() {
    // Arrange.
    let fixture = coexisting_fixture();
    let object_id = root(800);
    let proof = object_pin_proof(
        object_id,
        EconomicLaneIdV1::AssetTransfer,
        fixture.active_release_id,
        700,
    );
    let state = state_for_fixture(&fixture.registries, proof.derive_registry_root().unwrap());
    let proofs = [proof];

    // Act.
    let result = bind_selected_route(
        &fixture.registries,
        &state,
        fixture.active_route_id,
        &proofs,
    );

    // Assert.
    assert!(result.is_ok());
}

#[test]
fn conflicting_same_lane_release_pins_reject_before_route_selection() {
    // Arrange.
    let fixture = coexisting_fixture();
    let (proofs, registry_root) =
        paired_release_pin_proofs(fixture.active_release_id, fixture.drain_release_id);
    let state = state_for_fixture(&fixture.registries, registry_root);

    // Act.
    let result = bind_selected_route(
        &fixture.registries,
        &state,
        fixture.active_route_id,
        &proofs,
    );

    // Assert.
    assert_eq!(
        rejection(result),
        GlobalEconomicStateErrorV1::ConflictingPinnedReleases(EconomicLaneIdV1::AssetTransfer,)
    );
}

#[test]
fn drain_only_route_without_a_pinned_object_has_no_match() {
    // Arrange.
    let fixture = economic_fixture(
        &[EconomicLaneIdV1::AssetTransfer],
        EconomicLaneIdV1::AssetTransfer,
        LaneModuleReleaseStatusV1::DrainOnly,
    );
    let route_id = fixture.route_registry.routes()[0].route_release_id();
    let state = state_for_fixture(&fixture, root(999));

    // Act.
    let result = bind_selected_route(&fixture, &state, route_id, &[]);

    // Assert.
    assert_eq!(
        rejection(result),
        GlobalEconomicStateErrorV1::NoMatchingLifecycleRoute
    );
}

#[test]
fn two_active_routes_for_one_command_reject_as_ambiguous() {
    // Arrange.
    let (fixture, proposed_route_id) = ambiguous_active_fixture();
    let state = state_for_fixture(&fixture, root(999));

    // Act.
    let result = bind_selected_route(&fixture, &state, proposed_route_id, &[]);

    // Assert.
    assert_eq!(
        rejection(result),
        GlobalEconomicStateErrorV1::AmbiguousLifecycleRoute
    );
}

fn bind_selected_route<'a>(
    fixture: &'a EconomicRegistryFixture,
    state: &'a GlobalEconomicStateV1,
    route_id: RouteReleaseIdV1,
    proofs: &'a [EconomicObjectReleasePinProofV1],
) -> Result<(), GlobalEconomicStateErrorV1> {
    let route = fixture
        .route_registry
        .routes()
        .iter()
        .find(|route| route.route_release_id() == route_id)
        .unwrap();
    let consumed_object_ids = proofs.iter().map(|proof| proof.pin().object_id()).collect();
    let occurrence = occurrence_for_selected_route(fixture, state, route, consumed_object_ids);
    let profile_occurrence = bind_economic_command_occurrence_to_active_profile_v1(
        &fixture.profile,
        &fixture.route_registry,
        &occurrence,
    )
    .unwrap();
    let profile_state = bind_global_economic_state_to_profile_v1(
        state,
        &fixture.profile,
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    )
    .unwrap();
    bind_profile_bound_occurrence_to_global_state_v1(profile_occurrence, profile_state, proofs)
        .map(|_| ())
}

fn occurrence_for_selected_route(
    fixture: &EconomicRegistryFixture,
    state: &GlobalEconomicStateV1,
    route: &RouteReleaseV1,
    consumed_object_ids: Vec<CommitmentV3>,
) -> EconomicCommandOccurrenceV1 {
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: state.content().application_id(),
        chain_or_domain_id: state.content().chain_or_domain_id(),
        action_type_id: EconomicActionTypeIdV1::new(
            route.content().command_variant_root().into_bytes(),
        )
        .unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new([3; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([4; 32]).unwrap(),
        authorization_nonce: 17,
        valid_from_epoch: 0,
        valid_through_epoch: u64::MAX,
        pre_state_root: CommitmentV3::new(state.state_root().into_bytes()).unwrap(),
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

fn paired_release_pin_proofs(
    first_release_id: LaneModuleReleaseIdV1,
    second_release_id: LaneModuleReleaseIdV1,
) -> ([EconomicObjectReleasePinProofV1; 2], CommitmentV3) {
    let mut first_bytes = root(810).into_bytes();
    first_bytes[31] = 2;
    let mut second_bytes = first_bytes;
    second_bytes[31] = 3;
    let first_object = CommitmentV3::new(first_bytes).unwrap();
    let second_object = CommitmentV3::new(second_bytes).unwrap();
    let first_pin = EconomicObjectReleasePinV1::new(
        first_object,
        EconomicLaneIdV1::AssetTransfer,
        first_release_id,
    );
    let second_pin = EconomicObjectReleasePinV1::new(
        second_object,
        EconomicLaneIdV1::AssetTransfer,
        second_release_id,
    );
    let first_leaf =
        derive_sparse_merkle_leaf_commitment_v1(first_object, first_pin.value_hash().unwrap())
            .unwrap();
    let second_leaf =
        derive_sparse_merkle_leaf_commitment_v1(second_object, second_pin.value_hash().unwrap())
            .unwrap();
    let mut first_siblings = [root(700); SPARSE_MERKLE_TREE_DEPTH_V1];
    let mut second_siblings = first_siblings;
    first_siblings[SPARSE_MERKLE_TREE_DEPTH_V1 - 1] = second_leaf;
    second_siblings[SPARSE_MERKLE_TREE_DEPTH_V1 - 1] = first_leaf;
    let first_proof = EconomicObjectReleasePinProofV1::new(
        first_pin,
        SparseMerkleSiblingPathV1::new(first_siblings),
    )
    .unwrap();
    let second_proof = EconomicObjectReleasePinProofV1::new(
        second_pin,
        SparseMerkleSiblingPathV1::new(second_siblings),
    )
    .unwrap();
    let registry_root = first_proof.derive_registry_root().unwrap();
    assert_eq!(second_proof.derive_registry_root().unwrap(), registry_root);
    ([first_proof, second_proof], registry_root)
}
