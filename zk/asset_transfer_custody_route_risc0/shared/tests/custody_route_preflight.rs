//! Native custody-route preflight evidence: positive, independent negative,
//! boundary, canonical-parity, and rejection-before-preparation cases. Every
//! prepared value is ordinary data; no receipt, image, release, or publication
//! authority is claimed or exercised here.

mod support;

#[path = "support/oversize.rs"]
mod resource_bounds;

use support::{bundle_root, custody_rows, root, unknown_root, Governance, Options};
use zenodex_asset_lane_custody_coordinator_risc0_shared::{
    prepare_asset_lane_custody_coordinator_v1, AssetLaneCustodyCoordinatorGuestErrorV1,
};
use zenodex_asset_transfer_custody_route_risc0_shared::*;
use zenodex_global_settlement_abi_v1::*;

const SHARED_VECTOR_BYTES: &[u8] =
    include_bytes!("../../../../tests/data/asset_transfer_custody_release_binding_v1_golden.json");

fn abi(field: &'static str) -> AssetTransferCustodyRouteErrorV1 {
    AssetTransferCustodyRouteErrorV1::Abi(AbiErrorV1::InvalidBinding(field))
}

fn global(code: GlobalAllocationBindingRejectCodeV1) -> AssetTransferCustodyRouteErrorV1 {
    AssetTransferCustodyRouteErrorV1::GlobalBinding(code)
}

fn matching_input(custody_atoms: u128) -> AssetTransferCustodyRouteInputV1 {
    support::input(&Options::matching(custody_rows(custody_atoms)))
}

fn balance(state: &GlobalEconomicStateV1, owner: &str) -> u128 {
    state
        .balances
        .iter()
        .find(|row| row.owner == owner)
        .map(|row| row.amount_atoms)
        .unwrap_or(0)
}

fn prepare_bytes(
    input: &AssetTransferCustodyRouteInputV1,
) -> Result<PreparedAssetTransferCustodyRouteV1, AssetTransferCustodyRouteErrorV1> {
    prepare_asset_transfer_custody_route_from_bytes_v1(
        &canonical_bytes_v1(input).expect("route input must encode"),
    )
}

fn allocation(
    input: &AssetTransferCustodyRouteInputV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AbiResultV1<Option<GlobalAllocationBindingRejectCodeV1>> {
    check_asset_transfer_global_allocation_v1(AssetTransferGlobalAllocationCandidateV1 {
        accepted,
        occurrence: &input.occurrence,
        predecessor: &input.pre_state,
        current: &input.post_state,
    })
}

/// Typed, canonical-byte, and canonical-encoding entries all refuse `mutate`d
/// input with the same error and produce no prepared result or bytes.
fn assert_rejects(
    valid: &AssetTransferCustodyRouteInputV1,
    mutate: impl FnOnce(&mut AssetTransferCustodyRouteInputV1),
    expected: AssetTransferCustodyRouteErrorV1,
) {
    let mut changed = valid.clone();
    mutate(&mut changed);
    assert_ne!(&changed, valid, "the mutation must change the input");
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(changed.clone()),
        Err(expected.clone())
    );
    assert_eq!(prepare_bytes(&changed), Err(expected.clone()));
    assert_eq!(
        canonical_asset_transfer_custody_route_input_bytes_v1(&changed),
        Err(expected)
    );
}

#[test]
fn matching_roots_and_nonzero_custody_prepare_the_route_from_retained_components() {
    let input = matching_input(7);
    support::assert_coherent(&input);
    let prepared = prepare_asset_transfer_custody_route_v1(input.clone())
        .expect("matching refreshed roots with nonzero custody must prepare");
    assert_eq!(prepared.input(), &input);

    // The custody coordinator preflight value is returned unchanged.
    let lane = prepare_asset_lane_custody_coordinator_v1(input.lane_input.clone())
        .expect("the custody coordinator must prepare the fixture lane input");
    assert_eq!(prepared.lane(), &lane);
    assert_eq!(
        prepared.lane_journal_bytes(),
        lane.lane_journal_bytes.as_slice()
    );
    assert_eq!(
        prepared.module_journal_bytes(),
        lane.module_journal_bytes.as_slice()
    );
    assert_eq!(allocation(&input, &lane.module_accepted), Ok(None));

    // The route journal binds the exact states, occurrence, and lane journal.
    let journal = prepared.route_journal();
    assert_eq!(journal.schema, GLOBAL_SETTLEMENT_ABI_V1);
    assert_eq!(
        journal.pre_state_root,
        input.pre_state.state_root().unwrap()
    );
    assert_eq!(
        journal.post_state_root,
        input.post_state.state_root().unwrap()
    );
    assert_eq!(
        journal.command_occurrence_id,
        input.occurrence.occurrence_id().unwrap()
    );
    let route = &input.routes.routes[0];
    assert_eq!(journal.route_release_id, route.route_release_id);
    assert_eq!(
        journal.ordered_lane_journal_roots,
        vec![lane.lane_accepted.lane_journal.journal_root().unwrap()]
    );
    assert_eq!(
        journal.effect_plan_root,
        lane.lane_accepted.lane_journal.effect_plan_root
    );
    assert_eq!(
        prepared.route_journal_bytes(),
        canonical_bytes_v1(journal).unwrap().as_slice()
    );
    let decoded: RouteCompositionJournalV1 =
        serde_json::from_slice(prepared.route_journal_bytes()).unwrap();
    assert_eq!(&decoded, journal);

    // Projection and refinement equal the existing V1 helpers on the same data.
    let projection = project_route_global_state_v1(RouteGlobalStateProjectionCandidateV1 {
        profile: &input.profile,
        lanes: &input.lanes,
        coordinators: &input.coordinators,
        routes: &input.routes,
        route,
        lane_journals: std::slice::from_ref(&lane.lane_accepted.lane_journal),
        route_journal: journal,
        pre_state: &input.pre_state,
        post_state: &input.post_state,
    })
    .unwrap();
    assert_eq!(prepared.projection(), &projection);
    assert_eq!(
        prepared.projection_root(),
        &projection.projection_root().unwrap()
    );
    assert_eq!(
        projection.ordered_lane_ids(),
        vec![LaneIdV1::ASSET_TRANSFER]
    );
    let refinement = refine_route_global_economic_state_effects_v1(
        &GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &input.pre_state,
            post_state: &input.post_state,
            effect_plan: &lane.lane_accepted.effects,
            consumed_occurrences: std::slice::from_ref(&input.occurrence),
            route_journals: std::slice::from_ref(journal),
        },
    )
    .unwrap();
    assert_eq!(prepared.refinement(), &refinement);
    assert_eq!(
        prepared.refinement_root(),
        &refinement.refinement_root().unwrap()
    );
    assert_eq!(refinement.pre_state_root(), &journal.pre_state_root);
    assert_eq!(refinement.post_state_root(), &journal.post_state_root);
    assert_eq!(
        refinement.effect_plan_root(),
        &lane.lane_accepted.effects.effect_plan_root().unwrap()
    );

    // Custody-complete economics: the physical total includes the custody row
    // and the custody frame is identical before and after the transfer.
    let conservation = &lane.lane_accepted.effects.asset_conservation;
    assert_eq!(conservation.len(), 1);
    assert_eq!(conservation[0].owned_and_custodied_pre_atoms, 122);
    assert_eq!(conservation[0].owned_and_custodied_post_atoms, 122);
    assert_eq!(conservation[0].supply_post_atoms, 122);
    assert_eq!(
        input.pre_state.custody,
        input.lane_input.module_input.custody
    );
    assert_eq!(input.post_state.custody, input.pre_state.custody);
    assert_eq!(balance(&input.post_state, "alice"), 68);
    assert_eq!(balance(&input.post_state, "bob"), 40);
    assert_eq!(balance(&input.post_state, "treasury"), 7);

    // Expected image metadata is copied from the selected releases only.
    let coordinator = &input.coordinators.releases[0];
    assert_eq!(coordinator.lane_id, LaneIdV1::ASSET_TRANSFER);
    assert_eq!(
        prepared.expected_coordinator_image_id(),
        &coordinator.guest_image_id
    );
    assert_eq!(prepared.expected_route_image_id(), &route.guest_image_id);
    assert_ne!(prepared.expected_coordinator_image_id(), &bundle_root());
    assert_ne!(prepared.expected_route_image_id(), &bundle_root());
}

#[test]
fn legacy_transition_totals_differ_from_the_custody_family_only_with_custody_rows() {
    let input = matching_input(7);
    let module_input = &input.lane_input.module_input;
    let legacy = match transition_asset_transfer_lane_module_v1(module_input).unwrap() {
        AssetTransferLaneModuleResultV1::Accepted(accepted) => *accepted,
        other => panic!("legacy transition must accept: {other:?}"),
    };
    let custody = match transition_asset_transfer_lane_module_custody_v1(module_input).unwrap() {
        AssetTransferLaneModuleResultV1::Accepted(accepted) => *accepted,
        other => panic!("custody transition must accept: {other:?}"),
    };
    assert_eq!(
        legacy.effects.asset_conservation[0].owned_and_custodied_post_atoms,
        115
    );
    assert_eq!(
        custody.effects.asset_conservation[0].owned_and_custodied_post_atoms,
        122
    );
    assert_eq!(legacy.post_state, custody.post_state);
    assert_ne!(legacy, custody);
    let prepared = prepare_asset_transfer_custody_route_v1(input.clone()).unwrap();
    assert_eq!(prepared.lane().module_accepted, custody);

    // Without custody rows the two families produce the same value.
    let zero = matching_input(0);
    let zero_module = &zero.lane_input.module_input;
    assert_eq!(
        transition_asset_transfer_lane_module_v1(zero_module).unwrap(),
        transition_asset_transfer_lane_module_custody_v1(zero_module).unwrap()
    );
}

#[test]
fn custody_zero_and_one_atom_prepare_and_a_zero_atom_custody_row_rejects() {
    let zero = matching_input(0);
    assert!(zero.lane_input.module_input.custody.is_empty());
    let prepared = prepare_asset_transfer_custody_route_v1(zero).unwrap();
    assert!(prepared.input().post_state.custody.is_empty());
    let row = &prepared.lane().lane_accepted.effects.asset_conservation[0];
    assert_eq!(row.owned_and_custodied_post_atoms, 115);

    let one = matching_input(1);
    let prepared = prepare_asset_transfer_custody_route_v1(one.clone()).unwrap();
    let row = &prepared.lane().lane_accepted.effects.asset_conservation[0];
    assert_eq!(row.owned_and_custodied_pre_atoms, 116);
    assert_eq!(row.owned_and_custodied_post_atoms, 116);
    assert_eq!(
        prepared.input().post_state.custody,
        one.lane_input.module_input.custody
    );

    // A zero-atom custody row is rejected by exact input validation before the
    // coordinator runs.
    assert_rejects(
        &one,
        |input| input.lane_input.module_input.custody[0].amount_atoms = 0,
        abi("asset lane custody"),
    );
}

#[test]
fn typed_and_canonical_byte_preparation_agree_exactly() {
    let input = matching_input(7);
    let typed = prepare_asset_transfer_custody_route_v1(input.clone()).unwrap();
    let bytes = canonical_asset_transfer_custody_route_input_bytes_v1(&input).unwrap();
    assert_eq!(bytes, canonical_bytes_v1(&input).unwrap());
    let ceiling = MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1;
    assert!(bytes.len() <= ceiling);
    let decoded: AssetTransferCustodyRouteInputV1 = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(decoded, input);
    let raw = prepare_asset_transfer_custody_route_from_bytes_v1(&bytes).unwrap();
    assert_eq!(raw, typed);
    assert_eq!(raw.route_journal_bytes(), typed.route_journal_bytes());
    assert_eq!(raw.lane_journal_bytes(), typed.lane_journal_bytes());
    assert_eq!(raw.module_journal_bytes(), typed.module_journal_bytes());
    assert_eq!(raw.projection_root(), typed.projection_root());
    assert_eq!(raw.refinement_root(), typed.refinement_root());
    // Preparation is pure: repeating it yields the same ordinary value.
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(input).unwrap(),
        typed
    );
}

#[test]
fn unknown_and_mixed_roots_reject_before_custody_preparation_and_global_checks() {
    let mut module_only = Options::matching(custody_rows(7));
    module_only.module.specification_root = unknown_root();
    let mut coordinator_only = Options::matching(custody_rows(7));
    coordinator_only.coordinator.specification_root = unknown_root();
    let mut route_only = Options::matching(custody_rows(7));
    route_only.route.specification_root = unknown_root();
    let mut all_unknown = Options::matching(custody_rows(7));
    for role in all_unknown.roles_mut() {
        role.specification_root = unknown_root();
    }
    let mut only_module_matches = Options::matching(custody_rows(7));
    only_module_matches.coordinator.specification_root = unknown_root();
    only_module_matches.route.specification_root = unknown_root();
    let mut only_coordinator_matches = Options::matching(custody_rows(7));
    only_coordinator_matches.module.specification_root = unknown_root();
    only_coordinator_matches.route.specification_root = unknown_root();
    let mut only_route_matches = Options::matching(custody_rows(7));
    only_route_matches.module.specification_root = unknown_root();
    only_route_matches.coordinator.specification_root = unknown_root();

    for (options, field) in [
        (module_only, "custody semantics module specification root"),
        (
            coordinator_only,
            "custody semantics coordinator specification root",
        ),
        (route_only, "custody semantics route specification root"),
        (all_unknown, "custody semantics module specification root"),
        (
            only_module_matches,
            "custody semantics coordinator specification root",
        ),
        (
            only_coordinator_matches,
            "custody semantics module specification root",
        ),
        (
            only_route_matches,
            "custody semantics module specification root",
        ),
        (
            Options::opaque(custody_rows(7)),
            "custody semantics module specification root",
        ),
    ] {
        let input = support::input(&options);
        support::assert_coherent(&input);
        let expected = abi(field);
        assert_eq!(
            prepare_asset_transfer_custody_route_v1(input.clone()),
            Err(expected.clone())
        );
        assert_eq!(prepare_bytes(&input), Err(expected.clone()));
        assert_eq!(
            canonical_asset_transfer_custody_route_input_bytes_v1(&input),
            Err(expected)
        );
        // The refusal is exactly the retained semantic guard's.
        assert_eq!(
            require_asset_transfer_custody_semantics_v1(
                &input.profile,
                &input.lanes,
                &input.coordinators,
                &input.routes,
                &input.occurrence,
            ),
            Err(AbiErrorV1::InvalidBinding(field))
        );
        // Seam: the custody coordinator and the exact global allocation both
        // accept this coherent input on their own, so the guard is the only
        // refusing check and it ran before either of them.
        let lane = prepare_asset_lane_custody_coordinator_v1(input.lane_input.clone())
            .expect("the custody coordinator is indifferent to specification roots");
        assert_eq!(allocation(&input, &lane.module_accepted), Ok(None));
    }
}

#[test]
fn version_image_source_and_toolchain_identities_never_select_the_route() {
    let mut spoofed = Options::matching(custody_rows(7));
    for role in spoofed.roles_mut() {
        role.specification_root = unknown_root();
        role.semantic_version = "CUSTODY_COMPLETE_V1".to_owned();
        role.guest_image_id = bundle_root();
        role.source_root = bundle_root();
        role.toolchain_root = bundle_root();
    }
    let spoofed = support::input(&spoofed);
    support::assert_coherent(&spoofed);
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(spoofed),
        Err(abi("custody semantics module specification root"))
    );

    // Conversely those identities are inert once the specification roots match,
    // and the expected image metadata is whatever the selected releases carry.
    let mut inert = Options::matching(custody_rows(7));
    for role in inert.roles_mut() {
        role.semantic_version = "0.0.0-legacy".to_owned();
        role.guest_image_id = unknown_root();
        role.source_root = unknown_root();
        role.toolchain_root = unknown_root();
    }
    let inert = support::input(&inert);
    support::assert_coherent(&inert);
    let prepared = prepare_asset_transfer_custody_route_v1(inert)
        .expect("identities other than the specification root are inert");
    assert_eq!(prepared.expected_coordinator_image_id(), &unknown_root());
    assert_eq!(prepared.expected_route_image_id(), &unknown_root());
}

#[test]
fn each_governed_binding_mismatch_rejects_with_no_prepared_result() {
    let valid = matching_input(7);
    assert_rejects(
        &valid,
        |input| input.occurrence.route_release_id = unknown_root(),
        abi("caller-selected route does not match governed route"),
    );
    assert_rejects(
        &valid,
        |input| input.lane_input.module_input.context.module_release_id = unknown_root(),
        abi("asset transfer policy registry module release"),
    );
    assert_rejects(
        &valid,
        |input| input.lane_input.coordinator_context.coordinator_release_id = unknown_root(),
        abi("custody route exact command and release"),
    );
    assert_rejects(
        &valid,
        |input| input.profile.root_image_id = root(900),
        abi("profile content-derived id"),
    );
    assert_rejects(
        &valid,
        |input| {
            input.lane_input.coordinator_context.compatible_modules[0].module_release_id =
                unknown_root();
        },
        abi("custody route exact command and release"),
    );
    assert_rejects(
        &valid,
        |input| input.occurrence.command_body_hash = root(0xbad),
        abi("custody route exact command and release"),
    );
    assert_rejects(
        &valid,
        |input| input.occurrence.subject_id = "mallory".to_owned(),
        abi("custody route exact command and release"),
    );
    assert_rejects(
        &valid,
        |input| input.occurrence.grant_root = root(77),
        abi("custody route exact command and release"),
    );

    // Coherently rebuilt governance that is not active for new objects.
    let mut shadow = Options::matching(custody_rows(7));
    shadow.profile_status = ProfileStatusV1::SHADOW;
    let shadow = support::input(&shadow);
    support::assert_coherent(&shadow);
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(shadow),
        Err(abi("custody route active profile"))
    );
    let mut drained_route = Options::matching(custody_rows(7));
    drained_route.route_status = (ReleaseStatusV1::DRAIN_ONLY, false);
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(support::input(&drained_route)),
        Err(abi("active profile route status"))
    );
    let mut drained_lane = Options::matching(custody_rows(7));
    drained_lane.lane_status = (ReleaseStatusV1::DRAIN_ONLY, false);
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(support::input(&drained_lane)),
        Err(abi("active route lane release"))
    );
}

#[test]
fn only_the_single_asset_transfer_route_lane_is_governed() {
    let mut options = Options::matching(custody_rows(7));
    options.extra_route_lane = true;
    let two_lanes = support::input(&options);
    support::assert_coherent(&two_lanes);
    assert_eq!(
        two_lanes.routes.routes[0].ordered_lanes,
        [LaneIdV1::ASSET_TRANSFER, LaneIdV1::SPOT_LIQUIDITY]
    );
    let expected = abi("custody route selected release scope");
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(two_lanes.clone()),
        Err(expected.clone())
    );
    assert_eq!(prepare_bytes(&two_lanes), Err(expected));

    // A route without lanes is not a governed route at all.
    let mut no_lanes = matching_input(7);
    let route = &mut no_lanes.routes.routes[0];
    route.ordered_lanes.clear();
    route.module_release_ids.clear();
    route.dependency_roles.clear();
    route.port_schema_roots.clear();
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(no_lanes),
        Err(AssetTransferCustodyRouteErrorV1::Abi(
            AbiErrorV1::InvalidBounds("route module count")
        ))
    );
}

#[test]
fn global_state_drift_after_custody_preparation_rejects_through_exact_allocation() {
    use zenodex_global_settlement_abi_v1::GlobalAllocationBindingRejectCodeV1::*;
    let valid = matching_input(7);
    // Conserved but misattributed movement.
    assert_rejects(
        &valid,
        |input| {
            input.post_state.balances[0].amount_atoms += 1;
            input.post_state.balances[1].amount_atoms -= 1;
        },
        global(GLOBAL_PROJECTION_ROWS_DRIFT),
    );
    // The custody frame must be identical before and after the transfer.
    assert_rejects(
        &valid,
        |input| input.post_state.custody[0].amount_atoms += 1,
        global(GLOBAL_PROJECTION_ROWS_DRIFT),
    );
    assert_rejects(
        &valid,
        |input| input.post_state.replay_state.clear(),
        global(GLOBAL_REPLAY_CONTINUITY_DRIFT),
    );
    assert_rejects(
        &valid,
        |input| input.post_state.history_root = root(999),
        global(GLOBAL_UNSUPPORTED_STATE),
    );
    // An occurrence that passes every exact binding but names another command
    // instance drifts from the coordinator-bound occurrence id.
    assert_rejects(
        &valid,
        |input| input.occurrence.nonce += 1,
        global(GLOBAL_OCCURRENCE_DRIFT),
    );
}

#[test]
fn exact_selected_module_journal_ceiling_applies_to_all_route_entries() {
    let prepared = prepare_asset_transfer_custody_route_v1(matching_input(7)).unwrap();
    let journal_size = prepared.module_journal_bytes().len();
    for at_limit in [true, false] {
        let mut options = Options::matching(custody_rows(7));
        options.module_max_journal_bytes =
            u64::try_from(journal_size - usize::from(!at_limit)).unwrap();
        let input = support::input(&options);
        support::assert_coherent(&input);
        let lane = prepare_asset_lane_custody_coordinator_v1(input.lane_input.clone()).unwrap();
        assert_eq!(lane.module_journal_bytes.len(), journal_size);
        let expected = if at_limit {
            Ok(())
        } else {
            Err(AssetTransferCustodyRouteErrorV1::Bounds)
        };
        assert_eq!(
            prepare_asset_transfer_custody_route_v1(input.clone()).map(|_| ()),
            expected
        );
        assert_eq!(prepare_bytes(&input).map(|_| ()), expected);
        assert_eq!(
            canonical_asset_transfer_custody_route_input_bytes_v1(&input).map(|_| ()),
            expected
        );
    }
}

#[test]
fn release_journal_bounds_reject_after_preparation_with_no_prepared_result() {
    let mut route_bound = Options::matching(custody_rows(7));
    route_bound.route_max_journal_bytes = 1;
    let input = support::input(&route_bound);
    support::assert_coherent(&input);
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(input),
        Err(AssetTransferCustodyRouteErrorV1::Bounds)
    );
    let mut coordinator_bound = Options::matching(custody_rows(7));
    coordinator_bound.coordinator_max_journal_bytes = 1;
    let input = support::input(&coordinator_bound);
    support::assert_coherent(&input);
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(input),
        Err(AssetTransferCustodyRouteErrorV1::Bounds)
    );
}

#[test]
fn wire_bounds_canonical_forms_and_schema_failures_leave_no_prepared_result() {
    use zenodex_asset_transfer_custody_route_risc0_shared::AssetTransferCustodyRouteErrorV1::{
        Bounds, Decode, NonCanonical, Schema,
    };
    let input = matching_input(7);
    let bytes = canonical_asset_transfer_custody_route_input_bytes_v1(&input).unwrap();
    assert_eq!(
        ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1,
        "zenodex/asset-transfer-route-guest-input/v1"
    );
    assert_eq!(
        MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1,
        8 * 1024 * 1024
    );

    // Sizes 0, 1, the maximum accepted size, and one byte beyond it.
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&[]),
        Err(Bounds)
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(b"{"),
        Err(Decode)
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&vec![
            b' ';
            MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1
        ]),
        Err(Decode)
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&vec![
            b' ';
            MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1
                + 1
        ]),
        Err(Bounds)
    );

    // Equivalent but noncanonical forms decode to the same value and reject:
    // trailing whitespace, pretty whitespace, key order, and string spelling.
    let mut trailing = bytes.clone();
    trailing.push(b'\n');
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&trailing),
        Err(NonCanonical)
    );
    let value: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let pretty = serde_json::to_vec_pretty(&value).unwrap();
    assert_ne!(pretty, bytes);
    assert_eq!(
        serde_json::from_slice::<AssetTransferCustodyRouteInputV1>(&pretty).unwrap(),
        input
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&pretty),
        Err(NonCanonical)
    );
    let text = String::from_utf8(bytes.clone()).unwrap();
    let schema_suffix = format!(",\"schema\":\"{ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1}\"}}");
    let body = text
        .strip_suffix(&schema_suffix)
        .expect("canonical bytes end with the schema key")
        .strip_prefix('{')
        .expect("canonical bytes are one object");
    let reordered =
        format!("{{\"schema\":\"{ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1}\",{body}}}");
    assert_eq!(
        serde_json::from_str::<AssetTransferCustodyRouteInputV1>(&reordered).unwrap(),
        input
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(reordered.as_bytes()),
        Err(NonCanonical)
    );
    let escaped = text.replacen(
        "\"subject_id\":\"alice\"",
        "\"subject_id\":\"\\u0061lice\"",
        1,
    );
    assert_ne!(escaped, text);
    assert_eq!(
        serde_json::from_str::<AssetTransferCustodyRouteInputV1>(&escaped).unwrap(),
        input
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(escaped.as_bytes()),
        Err(NonCanonical)
    );

    // Decode failures: truncation and an unknown field.
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&bytes[..bytes.len() - 1]),
        Err(Decode)
    );
    let mut unknown = value;
    unknown
        .as_object_mut()
        .unwrap()
        .insert("verified".to_owned(), serde_json::Value::Bool(true));
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&serde_json::to_vec(&unknown).unwrap()),
        Err(Decode)
    );

    // Schema failures on the route wire and on the nested lane wire.
    assert_rejects(
        &input,
        |input| input.schema = "zenodex/asset-transfer-route-guest-input/v2".to_owned(),
        Schema,
    );
    assert_rejects(
        &input,
        |input| input.lane_input.schema = "unsupported-schema".to_owned(),
        AssetTransferCustodyRouteErrorV1::Lane(AssetLaneCustodyCoordinatorGuestErrorV1::Schema),
    );
}

#[test]
fn shared_python_custody_vector_governance_prepares_the_native_route() {
    let vector: serde_json::Value = serde_json::from_slice(SHARED_VECTOR_BYTES).unwrap();
    assert_eq!(
        vector["schema"],
        "zenodex/asset-transfer-custody-binding-test-vector/v1"
    );
    assert_eq!(vector["authority"], "NONE");
    let field = |name: &str| vector[name].clone();
    let governance = Governance {
        profile: serde_json::from_value(field("profile")).unwrap(),
        lanes: serde_json::from_value(field("lanes")).unwrap(),
        coordinators: serde_json::from_value(field("coordinators")).unwrap(),
        routes: serde_json::from_value(field("routes")).unwrap(),
        policy_registry: serde_json::from_value(field("policy_registry")).unwrap(),
        asset_policy_registry: serde_json::from_value(field("asset_policy_registry")).unwrap(),
        occurrence: serde_json::from_value(field("occurrence")).unwrap(),
        module_input: serde_json::from_value(field("module_input")).unwrap(),
    };
    let expected: AssetTransferLaneModuleAcceptedV1 =
        serde_json::from_value(field("accepted")).unwrap();
    let placeholder_pre_state_root = governance.occurrence.pre_state_root.clone();
    let input = governance.route_input();
    support::assert_coherent(&input);
    let prepared = prepare_asset_transfer_custody_route_v1(input.clone())
        .expect("the shared Python-produced custody governance must prepare natively");
    let accepted = &prepared.lane().module_accepted;

    // Occurrence-independent economics equal the Python-produced value exactly.
    assert_eq!(accepted.post_state, expected.post_state);
    assert_eq!(accepted.effects.rows, expected.effects.rows);
    assert_eq!(
        accepted.effects.asset_conservation,
        expected.effects.asset_conservation
    );
    assert_eq!(
        accepted.effects.fee_conservation,
        expected.effects.fee_conservation
    );
    assert_eq!(accepted.effects.lane_writes, expected.effects.lane_writes);
    assert_eq!(
        accepted.private_port.pre_state,
        expected.private_port.pre_state
    );
    assert_eq!(
        accepted.private_port.post_state,
        expected.private_port.post_state
    );
    assert_eq!(
        accepted.effects.asset_conservation[0].owned_and_custodied_post_atoms,
        122
    );

    // The route binds the occurrence to the exact pre-state root instead of the
    // vector's placeholder, so occurrence-bound identities differ while the
    // selected release identities are copied unchanged.
    assert_ne!(input.occurrence.pre_state_root, placeholder_pre_state_root);
    assert_ne!(
        accepted.module_journal.command_occurrence_id,
        expected.module_journal.command_occurrence_id
    );
    assert_eq!(
        accepted.module_journal.module_release_id,
        expected.module_journal.module_release_id
    );
    assert_eq!(
        Some(prepared.expected_coordinator_image_id().as_str()),
        vector["coordinators"]["releases"][0]["guest_image_id"].as_str()
    );
    assert_eq!(
        Some(prepared.expected_route_image_id().as_str()),
        vector["routes"]["routes"][0]["guest_image_id"].as_str()
    );
}
