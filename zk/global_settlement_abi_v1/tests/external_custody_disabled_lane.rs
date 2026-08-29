use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    transition_external_custody_disabled_v1, ExternalCustodyCommandKindV1,
    ExternalCustodyCommandV1, ExternalCustodyDisabledStateV1, LaneTransitionRejectCodeV1,
    EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1, EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1,
};

fn command(kind: ExternalCustodyCommandKindV1) -> ExternalCustodyCommandV1 {
    ExternalCustodyCommandV1 {
        kind,
        destination_id: "tau:testnet:destination-1".to_owned(),
        external_object_id: "tau:testnet:object-1".to_owned(),
    }
}

#[test]
fn every_registered_external_command_rejects_as_an_exact_noop() {
    // Arrange
    let state = ExternalCustodyDisabledStateV1::new();

    // Act
    let results: Vec<_> = EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1
        .iter()
        .copied()
        .map(|kind| transition_external_custody_disabled_v1(&state, &command(kind)).unwrap())
        .collect();

    // Assert
    assert_eq!(EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1.len(), 9);
    for result in results {
        result.validate().unwrap();
        assert_eq!(result.code, LaneTransitionRejectCodeV1::DISABLED_FEATURE);
        assert_eq!(result.pre_state_root, state.state_root().unwrap());
        assert_eq!(result.post_state_root, state.state_root().unwrap());
        assert!(result.effects.is_empty());
    }
}

#[test]
fn disabled_state_and_command_roots_match_python_vectors() {
    // Arrange
    let state = ExternalCustodyDisabledStateV1::new();
    let command = command(ExternalCustodyCommandKindV1::REGISTERED_EXTERNAL_LOCK);

    // Act / Assert
    assert_eq!(
        state.state_root().unwrap().as_str(),
        "0x760d222dd2e3dde6b65195d6f9a20b6d855a51743a194d9766481b042ae8d51d"
    );
    assert_eq!(
        command.command_root().unwrap().as_str(),
        "0x2cfc6d872fec25afe477e87be2b924cb27cc7c7aff97e00e7d4ff08bd1b75c8f"
    );
}

#[test]
fn serde_boundary_rejects_unknown_fields_and_unknown_commands() {
    // Arrange
    let state_with_extra = json!({
        "schema": EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1,
        "registry_entries": [],
        "pending_external_obligations": [],
        "outbox_acknowledgments": [],
        "unexpected": true
    });
    let unknown_command = json!({
        "kind": "UNREGISTERED_EXTERNAL_TELEPORT",
        "destination_id": "tau:testnet:destination-1",
        "external_object_id": "tau:testnet:object-1"
    });

    // Act / Assert
    assert!(serde_json::from_value::<ExternalCustodyDisabledStateV1>(state_with_extra).is_err());
    assert!(serde_json::from_value::<ExternalCustodyCommandV1>(unknown_command).is_err());
}

#[test]
fn nonempty_disabled_state_is_unrepresentable_at_the_typed_boundary() {
    // Arrange
    let nonempty = json!({
        "schema": EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1,
        "registry_entries": ["destination"],
        "pending_external_obligations": [],
        "outbox_acknowledgments": []
    });

    // Act
    let decoded: ExternalCustodyDisabledStateV1 = serde_json::from_value(nonempty).unwrap();

    // Assert
    assert!(decoded.validate().is_err());
}
