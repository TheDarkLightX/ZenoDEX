#[path = "../../test_support/mod.rs"]
mod support;
use zenodex_asset_transfer_route_composer_risc0_shared::*;
use zenodex_global_settlement_abi_v1::RouteCompositionJournalV1;

fn fixture() -> AssetTransferRouteGuestInputV1 {
    support::input(support::root(800), support::root(801), support::root(802))
}

#[test]
fn governed_transfer_binds_full_states_and_existing_exact_journal() {
    let input = fixture();
    let bytes = canonical_asset_transfer_route_input_bytes_v1(&input).unwrap();
    let prepared = prepare_asset_transfer_route_from_bytes_v1(&bytes).unwrap();
    let journal: RouteCompositionJournalV1 =
        serde_json::from_slice(prepared.route_journal_bytes()).unwrap();
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
    assert_eq!(
        input
            .post_state
            .balances
            .iter()
            .map(|r| r.amount_atoms)
            .sum::<u128>(),
        115
    );
    assert_eq!(
        input
            .post_state
            .balances
            .iter()
            .find(|r| r.owner == "alice")
            .unwrap()
            .amount_atoms,
        68
    );
    assert_eq!(
        input
            .post_state
            .balances
            .iter()
            .find(|r| r.owner == "bob")
            .unwrap()
            .amount_atoms,
        40
    );
    assert_eq!(
        input
            .post_state
            .balances
            .iter()
            .find(|r| r.owner == "treasury")
            .unwrap()
            .amount_atoms,
        7
    );
    if let Some(path) = std::env::var_os("ZENODEX_ROUTE_REFERENCE_OUTPUT") {
        std::fs::write(path, serde_json::to_vec_pretty(&serde_json::json!({
            "input": input, "lane_journal": serde_json::from_slice::<serde_json::Value>(prepared.lane_journal_bytes()).unwrap(),
            "route_journal": journal, "projection_root": prepared.projection_root(), "refinement_root": prepared.refinement_root(),
            "effect_plan": zenodex_asset_lane_coordinator_risc0_shared::prepare_asset_lane_coordinator_v1(prepared.input().lane_input.clone()).unwrap().lane_accepted.effects,
        })).unwrap()).unwrap();
    }
}

#[test]
fn conserved_but_misattributed_movement_and_omitted_replay_reject() {
    let valid = fixture();
    let mut changed = valid.clone();
    changed.post_state.balances[0].amount_atoms += 1;
    changed.post_state.balances[1].amount_atoms -= 1;
    assert!(matches!(
        prepare_asset_transfer_route_v1(changed),
        Err(AssetTransferRouteGuestErrorV1::GlobalBinding(_))
    ));
    let mut changed = valid.clone();
    changed.post_state.replay_state.clear();
    assert!(matches!(
        prepare_asset_transfer_route_v1(changed),
        Err(AssetTransferRouteGuestErrorV1::GlobalBinding(_))
    ));
    let mut changed = valid.clone();
    changed.post_state.history_root = support::root(999);
    assert!(matches!(
        prepare_asset_transfer_route_v1(changed),
        Err(AssetTransferRouteGuestErrorV1::GlobalBinding(_))
    ));
    let mut changed = valid;
    changed.occurrence.subject_id = "mallory".to_owned();
    assert!(prepare_asset_transfer_route_v1(changed).is_err());
}

#[test]
fn wrong_profile_release_and_ambiguous_encoding_reject() {
    let valid = fixture();
    let mut changed = valid.clone();
    changed.profile.root_image_id = support::root(900);
    assert!(prepare_asset_transfer_route_v1(changed).is_err());
    let mut changed = valid.clone();
    changed
        .lane_input
        .coordinator_context
        .coordinator_release_id = support::root(901);
    assert!(prepare_asset_transfer_route_v1(changed).is_err());
    let bytes = canonical_asset_transfer_route_input_bytes_v1(&valid).unwrap();
    let mut trailing = bytes.clone();
    trailing.push(b' ');
    assert!(matches!(
        prepare_asset_transfer_route_from_bytes_v1(&trailing),
        Err(AssetTransferRouteGuestErrorV1::NonCanonical)
    ));
    assert!(prepare_asset_transfer_route_from_bytes_v1(&bytes[..bytes.len() - 1]).is_err());
    assert!(matches!(
        prepare_asset_transfer_route_from_bytes_v1(&vec![
            0;
            MAX_ASSET_TRANSFER_ROUTE_INPUT_BYTES_V1
                + 1
        ]),
        Err(AssetTransferRouteGuestErrorV1::Bounds)
    ));
    let mut extra: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    extra
        .as_object_mut()
        .unwrap()
        .insert("verified".to_owned(), serde_json::Value::Bool(true));
    assert!(matches!(
        prepare_asset_transfer_route_from_bytes_v1(&serde_json::to_vec(&extra).unwrap()),
        Err(AssetTransferRouteGuestErrorV1::Decode)
    ));
}
