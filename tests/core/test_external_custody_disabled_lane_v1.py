from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.external_custody_disabled_lane_v1 import (
    EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1,
    ExternalCustodyCommandKindV1,
    ExternalCustodyCommandV1,
    ExternalCustodyDisabledStateV1,
    transition_external_custody_disabled_v1,
)
from src.core.global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
)
from src.core.m6_command_lane_registry_v1 import (
    DECISION_TABLE_V1,
    ResearchMappingStatusV1,
)
from src.core.m6_safe_mount_types_v1 import GlobalCommandKindV1


def _command(kind: ExternalCustodyCommandKindV1) -> ExternalCustodyCommandV1:
    return ExternalCustodyCommandV1(
        kind=kind,
        destination_id="tau:testnet:destination-1",
        external_object_id="tau:testnet:object-1",
    )


def test_every_registered_external_command_rejects_as_an_exact_noop() -> None:
    # Arrange
    state = ExternalCustodyDisabledStateV1()

    # Act
    results = tuple(
        transition_external_custody_disabled_v1(state, _command(kind))
        for kind in ExternalCustodyCommandKindV1
    )

    # Assert
    assert len(EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1) == 9
    assert EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1 == tuple(ExternalCustodyCommandKindV1)
    assert all(type(result) is LaneTransitionRejectedV1 for result in results)
    assert all(result.code is LaneTransitionRejectCodeV1.DISABLED_FEATURE for result in results)
    assert all(result.pre_state_root == state.state_root for result in results)
    assert all(result.post_state_root == state.state_root for result in results)
    assert all(result.effects == GlobalEconomicEffectPlanV1.empty() for result in results)


def test_disabled_state_is_the_unique_empty_registry_state() -> None:
    # Arrange / Act
    state = ExternalCustodyDisabledStateV1()

    # Assert
    assert state.registry_entries == ()
    assert state.pending_external_obligations == ()
    assert state.outbox_acknowledgments == ()
    assert state.to_canonical() == {
        "schema": "zenodex/external-custody-disabled-state/v1",
        "registry_entries": (),
        "pending_external_obligations": (),
        "outbox_acknowledgments": (),
    }


def test_disabled_state_and_command_roots_are_stable_parity_vectors() -> None:
    # Arrange
    state = ExternalCustodyDisabledStateV1()
    command = _command(ExternalCustodyCommandKindV1.REGISTERED_EXTERNAL_LOCK)

    # Act / Assert
    assert state.state_root == "0x760d222dd2e3dde6b65195d6f9a20b6d855a51743a194d9766481b042ae8d51d"
    assert command.command_root == "0x2cfc6d872fec25afe477e87be2b924cb27cc7c7aff97e00e7d4ff08bd1b75c8f"


def test_transition_snapshots_exact_owned_types_before_deciding() -> None:
    # Arrange
    state = ExternalCustodyDisabledStateV1()
    command = _command(ExternalCustodyCommandKindV1.EXTERNAL_TIMEOUT)

    class StateSubclass(ExternalCustodyDisabledStateV1):
        pass

    class CommandSubclass(ExternalCustodyCommandV1):
        pass

    # Act / Assert
    with pytest.raises(TypeError, match="state must be the exact typed value"):
        transition_external_custody_disabled_v1(StateSubclass(), command)
    with pytest.raises(TypeError, match="command must be the exact typed value"):
        transition_external_custody_disabled_v1(
            state,
            CommandSubclass(command.kind, command.destination_id, command.external_object_id),
        )


def test_disabled_rejection_cannot_be_forged_with_effects_or_state_change() -> None:
    # Arrange
    state = ExternalCustodyDisabledStateV1()
    different_root = replace(_command(ExternalCustodyCommandKindV1.EXTERNAL_REFUND), external_object_id="tau:testnet:object-2").command_root

    # Act / Assert
    with pytest.raises(ValueError, match="preserve the exact pre-state root"):
        LaneTransitionRejectedV1(
            LaneTransitionRejectCodeV1.DISABLED_FEATURE,
            state.state_root,
            different_root,
            GlobalEconomicEffectPlanV1.empty(),
        )


def test_legacy_tau_external_commands_remain_quarantined_from_a_release() -> None:
    # Arrange
    legacy_external_commands = {
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
    }

    # Act
    decisions = tuple(
        decision for decision in DECISION_TABLE_V1 if decision.command in legacy_external_commands
    )

    # Assert
    assert {decision.command for decision in decisions} == legacy_external_commands
    assert all(decision.target_id == "EXTERNAL_CUSTODY" for decision in decisions)
    assert all(
        decision.status
        is ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE
        for decision in decisions
    )
