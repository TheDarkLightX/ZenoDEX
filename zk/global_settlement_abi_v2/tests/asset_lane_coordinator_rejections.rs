#[path = "support/asset_lane_coordinator.rs"]
mod support;

use serde_json::Value;
use support::{command, fixture, typed_vector, vector_bytes};
use zenodex_global_settlement_abi_v2::{
    decode_canonical_v2, transition_asset_lane_v2, AbiErrorV2, AssetLaneContextV2,
    AssetLaneCoordinatorRejectCodeV2, AssetLaneRejectCodeV2, AssetLaneResultV2, AssetLaneRouteV2,
    AssetLaneStateV2, AssetTransferCommandV2, AssetTransferRejectCodeV2,
    ManagedAssetLifecycleCommandV2, MAX_ASSET_LANE_ASSETS_V2,
};

#[test]
fn python_and_rust_share_reject_precedence_route_code_and_exact_noop() {
    let fixture = fixture();
    assert_eq!(
        fixture
            .rejections
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        [
            "01_registry_binding_precedes_transfer_leaf",
            "02_transfer_leaf_unauthorized",
            "03_managed_leaf_authorization_root",
        ]
    );
    for (name, case) in &fixture.rejections {
        let context: AssetLaneContextV2 = typed_vector(&case.vectors, "context");
        let state: AssetLaneStateV2 = typed_vector(&case.vectors, "pre_state");
        let command = command(&case.vectors, &case.command_type);
        let result = transition_asset_lane_v2(&context, &state, &command)
            .expect("golden coordinator rejection must execute");
        let AssetLaneResultV2::Rejected(rejected) = result else {
            panic!("golden {name} unexpectedly accepted");
        };
        assert_eq!(rejected.route().as_str(), case.expected_route);
        assert_eq!(rejected.code().as_str(), case.expected_code);
        assert_eq!(
            rejected.pre_state_root(),
            &case.vectors["pre_state"].expected_root
        );
        assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
        assert!(rejected.effects().is_empty());
        assert_eq!(rejected.production_authority(), "NONE");
        assert_eq!(rejected.profile_authentication(), "SHADOW");
    }
}

#[test]
fn aggregate_decoders_reject_unknown_missing_schema_and_trailing_mutants() {
    let fixture = fixture();
    let case = &fixture.accepted["transfer"];
    let mut unknown_state = case.vectors["pre_state"].canonical.clone();
    unknown_state
        .as_object_mut()
        .expect("state object")
        .insert("unknown".to_owned(), Value::Bool(true));
    assert!(decode_canonical_v2::<AssetLaneStateV2>(
        &serde_json::to_vec(&unknown_state).expect("unknown-state bytes")
    )
    .is_err());

    let mut missing_registry = case.vectors["pre_state"].canonical.clone();
    missing_registry
        .as_object_mut()
        .expect("state object")
        .remove("origin_registry");
    assert!(decode_canonical_v2::<AssetLaneStateV2>(
        &serde_json::to_vec(&missing_registry).expect("missing-state bytes")
    )
    .is_err());

    let mut old_schema = case.vectors["pre_state"].canonical.clone();
    old_schema["schema"] = Value::String("zenodex/asset-lane-state/v1".to_owned());
    assert!(decode_canonical_v2::<AssetLaneStateV2>(
        &serde_json::to_vec(&old_schema).expect("old-schema bytes")
    )
    .is_err());

    let raw = vector_bytes(&case.vectors, "context");
    let mut trailing = raw.clone();
    trailing.push(b'\n');
    assert!(decode_canonical_v2::<AssetLaneContextV2>(&trailing).is_err());
}

#[test]
fn aggregate_context_and_amount_decoders_preserve_width_and_presence_rules() {
    let fixture = fixture();
    let case = &fixture.accepted["transfer"];
    let mut missing_occurrence = case.vectors["context"].canonical.clone();
    missing_occurrence
        .as_object_mut()
        .expect("context object")
        .remove("occurrence");
    assert!(decode_canonical_v2::<AssetLaneContextV2>(
        &serde_json::to_vec(&missing_occurrence).expect("missing-occurrence bytes")
    )
    .is_err());

    let mut bool_epoch = case.vectors["context"].canonical.clone();
    bool_epoch["writer_epoch"] = Value::Bool(true);
    let mut over_u64_epoch = case.vectors["context"].canonical.clone();
    over_u64_epoch["writer_epoch"] =
        serde_json::from_str("18446744073709551616").expect("u64 overflow JSON number");
    for mutant in [bool_epoch, over_u64_epoch] {
        assert!(decode_canonical_v2::<AssetLaneContextV2>(
            &serde_json::to_vec(&mutant).expect("invalid epoch bytes")
        )
        .is_err());
    }

    let mut over_u128_balance = case.vectors["pre_state"].canonical.clone();
    over_u128_balance["balances"][0]["amount_atoms"] =
        serde_json::from_str("340282366920938463463374607431768211456")
            .expect("u128 overflow JSON number");
    assert!(decode_canonical_v2::<AssetLaneStateV2>(
        &serde_json::to_vec(&over_u128_balance).expect("u128 overflow bytes")
    )
    .is_err());

    let mut nullable_occurrence = case.vectors["context"].canonical.clone();
    nullable_occurrence["occurrence"] = Value::Null;
    let decoded: AssetLaneContextV2 = decode_canonical_v2(
        &serde_json::to_vec(&nullable_occurrence).expect("nullable occurrence bytes"),
    )
    .expect("explicit nullable occurrence must decode");
    assert_eq!(decoded.occurrence, None);
}

#[test]
fn transition_validates_public_rust_aggregate_before_leaf_dispatch() {
    let fixture = fixture();
    let case = &fixture.accepted["transfer"];
    let context: AssetLaneContextV2 = typed_vector(&case.vectors, "context");
    let mut state: AssetLaneStateV2 = typed_vector(&case.vectors, "pre_state");
    let command = command(&case.vectors, &case.command_type);
    state.schema = "zenodex/asset-lane-state/v1".to_owned();

    assert_eq!(
        transition_asset_lane_v2(&context, &state, &command),
        Err(AbiErrorV2::InvalidSchema("asset lane state"))
    );
}

#[test]
fn direct_typed_registry_bounds_precede_invalid_inner_rows() {
    let fixture = fixture();
    let case = &fixture.accepted["transfer"];
    let mut state: AssetLaneStateV2 = typed_vector(&case.vectors, "pre_state");
    let mut invalid = state.origin_registry.assets[0].clone();
    invalid.asset.clear();

    state.origin_registry.assets = vec![invalid.clone(); MAX_ASSET_LANE_ASSETS_V2];
    assert_eq!(
        state.validate(),
        Err(AbiErrorV2::InvalidToken("asset origin asset"))
    );

    state.origin_registry.assets.push(invalid);
    assert_eq!(
        state.validate(),
        Err(AbiErrorV2::InvalidBounds(
            "asset lane origin registry assets"
        ))
    );
}

#[test]
fn typed_routes_keep_coordinator_and_leaf_codes_distinct() {
    assert_ne!(
        AssetLaneRejectCodeV2::Coordinator(
            AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH
        ),
        AssetLaneRejectCodeV2::Transfer(AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH)
    );
    assert_eq!(AssetLaneRouteV2::COORDINATOR.as_str(), "COORDINATOR");
}

#[test]
fn leaf_command_decoders_remain_closed_before_coordinator_wrapping() {
    let fixture = fixture();
    let transfer = &fixture.accepted["transfer"];
    let managed = &fixture.accepted["managed_issue"];
    let _: AssetTransferCommandV2 = typed_vector(&transfer.vectors, "command");
    let _: ManagedAssetLifecycleCommandV2 = typed_vector(&managed.vectors, "command");

    let mut unknown = transfer.vectors["command"].canonical.clone();
    unknown
        .as_object_mut()
        .expect("command object")
        .insert("unknown".to_owned(), Value::Bool(true));
    assert!(decode_canonical_v2::<AssetTransferCommandV2>(
        &serde_json::to_vec(&unknown).expect("unknown command bytes")
    )
    .is_err());
}
