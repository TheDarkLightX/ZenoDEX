from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import m6_command_lane_registry_v1 as registry_module
from src.core.m6_command_lane_registry_v1 import (
    ACTIVE_PLAN_REGISTRY_SHA256_V1,
    ADMISSION_RECEIPT_ARTIFACT_SHA256_V1,
    CAPABILITY_MANIFEST_SHA256_V1,
    DECISION_TABLE_V1,
    EXPECTED_LANE_DISPOSITIONS_V1,
    GOVERNED_ROUTE_IDS_V1,
    MAX_OWNED_JSON_NODES_V1,
    REQUIREMENTS_ARTIFACT_SHA256_V1,
    REQUIREMENTS_REGISTRY_ROOT_V1,
    CommandLaneDecisionV1,
    CommandLaneRegistryRejectV1,
    CommandLaneSourceSnapshotV1,
    ResearchMappingStatusV1,
    TargetKindV1,
    build_registry_artifact_v1,
    check_registry_artifact_v1,
    decision_root_v1,
    registry_root_v1,
    validate_registry_artifact_v1,
)
from src.core.m6_safe_mount_types_v1 import GlobalCommandKindV1
from src.state.canonical import canonical_json_bytes


def _snapshot() -> CommandLaneSourceSnapshotV1:
    return CommandLaneSourceSnapshotV1(
        captured_head="c0fb36c62b20293ebc54fc530f3dfe2e8046576d",
        rechecked_head="c0fb36c62b20293ebc54fc530f3dfe2e8046576d",
        safe_mount_source_tree="c55b34c5c3ca07f9019cc4fcb50cd623d9a6e7e8",
        safe_mount_source_blob="06007c01c43076d3a43118209d7349ba928f0bf4",
        active_plan_registry_sha256=ACTIVE_PLAN_REGISTRY_SHA256_V1,
        admission_receipt_artifact_sha256=ADMISSION_RECEIPT_ARTIFACT_SHA256_V1,
        capability_manifest_sha256=CAPABILITY_MANIFEST_SHA256_V1,
        requirements_artifact_sha256=REQUIREMENTS_ARTIFACT_SHA256_V1,
        requirements_registry_root=REQUIREMENTS_REGISTRY_ROOT_V1,
        lane_dispositions=EXPECTED_LANE_DISPOSITIONS_V1,
        route_ids=GOVERNED_ROUTE_IDS_V1,
    )


def test_bdd_given_closed_source_enum_when_registry_is_built_then_every_command_is_once_mapped() -> (
    None
):
    # Arrange
    snapshot = _snapshot()

    # Act
    artifact = build_registry_artifact_v1(snapshot)

    # Assert
    assert artifact["command_enum"] == [command.value for command in GlobalCommandKindV1]
    assert len(artifact["decisions"]) == len(GlobalCommandKindV1)
    assert artifact["registered_command_mapping_complete"] is True
    assert artifact["whole_economy_command_vocabulary_complete"] is False
    assert artifact["requirements_target_coverage_complete"] is False
    assert artifact["semantic_launch_alignment_complete"] is False
    assert artifact["release_backed"] is False
    assert artifact["mounted"] is False
    assert artifact["value_movement_claim_allowed"] is False


def test_bdd_given_governed_routes_when_decisions_are_built_then_buy_and_burn_is_never_a_treasury_burn() -> (
    None
):
    # Arrange
    decisions = {decision.command: decision for decision in DECISION_TABLE_V1}

    # Act
    buy_and_burn = decisions[GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN]
    liquidation = decisions[GlobalCommandKindV1.ZUSD_LIQUIDATE]
    funding = decisions[GlobalCommandKindV1.PERP_FUNDING]
    perp_liquidation = decisions[GlobalCommandKindV1.PERP_LIQUIDATE]

    # Assert
    assert (buy_and_burn.target_kind, buy_and_burn.target_id) == (
        TargetKindV1.GOVERNED_ROUTE,
        "fee_funded_zdex_purchase_and_burn",
    )
    assert (liquidation.target_kind, liquidation.target_id) == (
        TargetKindV1.GOVERNED_ROUTE,
        "zusd_liquidation_settlement",
    )
    assert (funding.target_kind, funding.target_id) == (
        TargetKindV1.GOVERNED_ROUTE,
        "perps_epoch_settlement",
    )
    assert (perp_liquidation.target_kind, perp_liquidation.target_id) == (
        TargetKindV1.LANE,
        "PERPS_MARKET",
    )


def test_bdd_given_enabled_external_commands_when_manifest_lane_is_disabled_then_conflicts_are_quarantined() -> (
    None
):
    # Arrange
    artifact = build_registry_artifact_v1(_snapshot())

    # Act
    conflicts = artifact["semantic_conflicts"]

    # Assert
    assert conflicts == [
        {
            "code": "SOURCE_RESEARCH_ENABLED_TARGET_DISABLED",
            "command": "tau_escrow_deposit",
            "resolution": "QUARANTINED_NO_RELEASE",
            "source_status": "SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE",
            "target_disposition": "DISABLED_PENDING_COMPLETE_PROFILE",
            "target_id": "EXTERNAL_CUSTODY",
            "target_kind": "LANE",
        },
        {
            "code": "SOURCE_RESEARCH_ENABLED_TARGET_DISABLED",
            "command": "tau_withdrawal",
            "resolution": "QUARANTINED_NO_RELEASE",
            "source_status": "SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE",
            "target_disposition": "DISABLED_PENDING_COMPLETE_PROFILE",
            "target_id": "EXTERNAL_CUSTODY",
            "target_kind": "LANE",
        },
        {
            "code": "SOURCE_RESEARCH_ENABLED_TARGET_DISABLED",
            "command": "tau_withdrawal_ack",
            "resolution": "QUARANTINED_NO_RELEASE",
            "source_status": "SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE",
            "target_disposition": "DISABLED_PENDING_COMPLETE_PROFILE",
            "target_id": "EXTERNAL_CUSTODY",
            "target_kind": "LANE",
        },
    ]


def test_bva_given_target_coverage_when_current_vocabulary_is_closed_then_absent_lanes_and_route_are_explicit() -> (
    None
):
    # Arrange
    artifact = build_registry_artifact_v1(_snapshot())

    # Act
    gaps = artifact["target_coverage_gaps"]

    # Assert
    assert gaps == [
        {
            "code": "NO_GLOBAL_COMMAND_VOCABULARY",
            "target_id": "ASSET_TRANSFER",
            "target_kind": "LANE",
        },
        {
            "code": "NO_GLOBAL_COMMAND_VOCABULARY",
            "target_id": "FARM_INCENTIVES",
            "target_kind": "LANE",
        },
        {
            "code": "NO_GLOBAL_COMMAND_VOCABULARY",
            "target_id": "ZDEX_TOKENOMICS",
            "target_kind": "LANE",
        },
        {
            "code": "NO_GLOBAL_COMMAND_VOCABULARY",
            "target_id": "STRATEGY_ESCROW",
            "target_kind": "LANE",
        },
        {
            "code": "NO_GLOBAL_COMMAND_VOCABULARY",
            "target_id": "strategy_triggered_spot_swap",
            "target_kind": "GOVERNED_ROUTE",
        },
    ]


@pytest.mark.parametrize(
    ("mutant", "code"),
    [
        (DECISION_TABLE_V1 + (DECISION_TABLE_V1[0],), "DUPLICATE_COMMAND"),
        (DECISION_TABLE_V1[:-1], "COMMAND_SET_DRIFT"),
        (tuple(reversed(DECISION_TABLE_V1)), "NONCANONICAL_DECISION_ORDER"),
    ],
)
def test_mutation_given_decision_table_mutants_when_root_is_derived_then_registry_rejects(
    mutant: tuple[CommandLaneDecisionV1, ...], code: str
) -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        decision_root_v1(mutant)

    # Assert
    assert raised.value.code == code


def test_mutation_given_disabled_command_marked_enabled_when_root_is_derived_then_rejects() -> None:
    # Arrange
    mutant = list(DECISION_TABLE_V1)
    disabled_index = next(
        index
        for index, decision in enumerate(mutant)
        if decision.command is GlobalCommandKindV1.ZUSD_LIQUIDATE
    )
    mutant[disabled_index] = replace(
        mutant[disabled_index],
        status=ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_UNRESOLVED_NO_RELEASE,
    )

    # Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        decision_root_v1(tuple(mutant))

    # Assert
    assert raised.value.code == "DISABLED_TO_ACTIVE"


def test_adversarial_given_nondecision_row_when_root_is_derived_then_typed_rejects() -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        decision_root_v1((object(),))  # type: ignore[arg-type]

    # Assert
    assert raised.value.code == "DECISION_TYPE"


def test_mutation_given_unknown_target_when_decision_is_constructed_then_rejects() -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        CommandLaneDecisionV1(
            GlobalCommandKindV1.SPOT_SWAP,
            TargetKindV1.LANE,
            "TREASURY_BURN",
            ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_UNRESOLVED_NO_RELEASE,
        )

    # Assert
    assert raised.value.code == "UNKNOWN_LANE_TARGET"


def test_mutation_given_wrong_known_lane_when_decision_root_is_checked_then_rejects() -> None:
    # Arrange
    mutant = list(DECISION_TABLE_V1)
    mutant[0] = replace(mutant[0], target_id="ASSET_TRANSFER")

    # Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        decision_root_v1(tuple(mutant))

    # Assert
    assert raised.value.code == "DECISION_ROOT_DRIFT"


def test_mutation_given_rebound_decision_table_when_registry_is_built_then_rejects(
    monkeypatch,
) -> None:
    # Arrange
    mutant = list(DECISION_TABLE_V1)
    mutant[0] = replace(mutant[0], target_id="ASSET_TRANSFER")
    monkeypatch.setattr(registry_module, "DECISION_TABLE_V1", tuple(mutant))

    # Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        build_registry_artifact_v1(_snapshot())

    # Assert
    assert raised.value.code == "DECISION_ROOT_DRIFT"


def test_metamorphic_given_equivalent_dictionary_order_when_artifact_is_validated_then_canonical_projection_is_unchanged() -> (
    None
):
    # Arrange
    snapshot = _snapshot()
    canonical = build_registry_artifact_v1(snapshot)
    reordered = {key: canonical[key] for key in reversed(tuple(canonical))}

    # Act
    validation_result = validate_registry_artifact_v1(reordered, snapshot)

    # Assert
    assert validation_result is None
    assert reordered == canonical


def test_mutation_given_manifest_disposition_drift_when_snapshot_is_constructed_then_rejects() -> (
    None
):
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        replace(
            _snapshot(),
            lane_dispositions=(
                ("ASSET_TRANSFER", "ACTIVE_NEW"),
                *EXPECTED_LANE_DISPOSITIONS_V1[1:],
            ),
        )

    # Assert
    assert raised.value.code == "TARGET_DISPOSITION_DRIFT"


def test_mutation_given_manifest_route_drift_when_snapshot_is_constructed_then_rejects() -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        replace(_snapshot(), route_ids=("treasury_burn",))

    # Assert
    assert raised.value.code == "ROUTE_SET_DRIFT"


def test_adversarial_given_hostile_route_string_when_snapshot_is_built_then_equality_is_not_invoked() -> (
    None
):
    class ExplodingString(str):
        def __eq__(self, _other: object) -> bool:
            raise AssertionError("hostile equality executed")

    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        replace(
            _snapshot(),
            route_ids=(
                ExplodingString("fee_funded_zdex_purchase_and_burn"),
                *GOVERNED_ROUTE_IDS_V1[1:],
            ),
        )

    # Assert
    assert raised.value.code == "ROUTE_SET_TYPE"


@pytest.mark.parametrize("value", ("a" * 39, "a" * 41, "A" * 40))
def test_bva_given_malformed_git_object_id_when_snapshot_is_built_then_rejects(
    value: str,
) -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        replace(_snapshot(), safe_mount_source_blob=value)

    # Assert
    assert raised.value.code == "SOURCE_BINDING_TYPE"


def test_stateful_given_head_changes_during_capture_when_snapshot_is_built_then_rejects() -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        replace(_snapshot(), rechecked_head="f" * 40)

    # Assert
    assert raised.value.code == "HEAD_CHANGED_DURING_CAPTURE"


def test_adversarial_given_duck_typed_snapshot_when_registry_is_built_then_properties_are_not_read() -> (
    None
):
    class HostileSnapshot:
        @property
        def captured_head(self) -> str:
            raise AssertionError("hostile property executed")

    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        build_registry_artifact_v1(HostileSnapshot())  # type: ignore[arg-type]

    # Assert
    assert raised.value.code == "SOURCE_SNAPSHOT_TYPE"


def test_adversarial_given_post_construction_snapshot_mutation_when_built_then_revalidates() -> (
    None
):
    # Arrange
    snapshot = _snapshot()
    object.__setattr__(snapshot, "admission_receipt_artifact_sha256", "f" * 64)

    # Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        build_registry_artifact_v1(snapshot)

    # Assert
    assert raised.value.code == "ADMISSION_RECEIPT_SHA_DRIFT"


def test_metamorphic_given_source_pin_changes_when_registry_is_built_then_full_root_changes() -> (
    None
):
    # Arrange
    first = build_registry_artifact_v1(_snapshot())
    second = build_registry_artifact_v1(replace(_snapshot(), safe_mount_source_blob="f" * 40))

    # Act
    first_root = first["registry_root"]
    second_root = second["registry_root"]

    # Assert
    assert first["decision_root"] == second["decision_root"]
    assert first_root != second_root


def test_mutation_given_self_referential_root_input_when_root_is_derived_then_rejects() -> None:
    # Arrange / Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        registry_root_v1({"registry_root": "forged"})

    # Assert
    assert raised.value.code == "REGISTRY_ROOT_INPUT"


def test_bva_given_owned_json_node_budget_when_at_maximum_then_root_is_derived() -> None:
    # Arrange
    leaf_count = MAX_OWNED_JSON_NODES_V1 - 2

    # Act
    root = registry_root_v1({"payload": [0] * leaf_count})

    # Assert
    assert len(root) == 64


def test_bva_given_owned_json_node_budget_when_one_over_maximum_then_rejects() -> None:
    # Arrange
    leaf_count = MAX_OWNED_JSON_NODES_V1 - 1

    # Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        registry_root_v1({"payload": [0] * leaf_count})

    # Assert
    assert raised.value.code == "ARTIFACT_NODE_COUNT"


def test_adversarial_given_hostile_artifact_value_when_validated_then_equality_is_not_invoked() -> (
    None
):
    class ExplodingEquality:
        def __eq__(self, _other: object) -> bool:
            raise AssertionError("hostile equality executed")

    # Arrange
    artifact = build_registry_artifact_v1(_snapshot())
    artifact["production_authority"] = ExplodingEquality()

    # Act
    with pytest.raises(CommandLaneRegistryRejectV1) as raised:
        validate_registry_artifact_v1(artifact, _snapshot())

    # Assert
    assert raised.value.code == "ARTIFACT_VALUE_TYPE"


def test_mutation_given_unrelated_raw_bytes_when_artifact_is_checked_then_rejects() -> None:
    # Arrange
    artifact = build_registry_artifact_v1(_snapshot())

    # Act
    report = check_registry_artifact_v1(artifact, b"{}", _snapshot())

    # Assert
    assert report.ok is False
    assert report.findings[0]["code"] == "RAW_ARTIFACT_BINDING_DRIFT"


def test_mutation_given_nonbytes_raw_artifact_when_checked_then_rejects() -> None:
    # Arrange
    artifact = build_registry_artifact_v1(_snapshot())

    # Act
    report = check_registry_artifact_v1(
        artifact,
        bytearray(canonical_json_bytes(artifact)),  # type: ignore[arg-type]
        _snapshot(),
    )

    # Assert
    assert report.ok is False
    assert report.findings[0]["code"] == "RAW_ARTIFACT_TYPE"
