from __future__ import annotations

import pytest

from src.core.current_profile_lane_gate_v1 import (
    CurrentProfileLaneCommandV1,
    CurrentProfileLaneStateV1,
    transition_current_profile_lane_v1,
)
from src.core.global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneTransitionRejectCodeV1,
)
from src.core.lane_capability_registry_v1 import LANE_CAPABILITY_REGISTRY_V1


def _root(value: int) -> str:
    return f"0x{value:064x}"


def test_current_profile_is_total_and_fail_closed_for_all_103_capabilities() -> None:
    # Arrange / Act
    results = tuple(
        (
            row.lane_id,
            transition_current_profile_lane_v1(
                CurrentProfileLaneStateV1(row.lane_id, _root(1)),
                CurrentProfileLaneCommandV1(row.lane_id, capability_id, _root(2)),
            ),
        )
        for row in LANE_CAPABILITY_REGISTRY_V1
        for capability_id in row.capability_ids
    )

    # Assert
    assert len(results) == 103
    for lane_id, rejected in results:
        expected = (
            LaneTransitionRejectCodeV1.DISABLED_FEATURE
            if lane_id is LaneIdV1.EXTERNAL_CUSTODY
            else LaneTransitionRejectCodeV1.POLICY_REJECT
        )
        assert rejected.code is expected
        assert rejected.pre_state_root == _root(1)
        assert rejected.post_state_root == _root(1)
        assert rejected.effects == GlobalEconomicEffectPlanV1.empty()


def test_cross_lane_state_command_pair_rejects_without_effects() -> None:
    # Arrange
    state = CurrentProfileLaneStateV1(LaneIdV1.ASSET_TRANSFER, _root(3))
    command = CurrentProfileLaneCommandV1(
        LaneIdV1.SPOT_LIQUIDITY,
        "exact_in_swap",
        _root(4),
    )

    # Act
    rejected = transition_current_profile_lane_v1(state, command)

    # Assert
    assert rejected.code is LaneTransitionRejectCodeV1.INVALID_CONTEXT
    assert rejected.pre_state_root == _root(3)
    assert rejected.post_state_root == _root(3)
    assert rejected.effects == GlobalEconomicEffectPlanV1.empty()


def test_unknown_and_cross_lane_capabilities_are_unconstructable() -> None:
    # Arrange / Act / Assert
    with pytest.raises(ValueError, match="unknown lane capability"):
        CurrentProfileLaneCommandV1(
            LaneIdV1.ASSET_TRANSFER,
            "exact_in_swap",
            _root(5),
        )
    with pytest.raises(ValueError, match="unknown lane capability"):
        CurrentProfileLaneCommandV1(
            LaneIdV1.FARM_INCENTIVES,
            "teleport_supply",
            _root(5),
        )


def test_current_profile_gate_command_root_matches_rust_vector() -> None:
    # Arrange
    command = CurrentProfileLaneCommandV1(
        LaneIdV1.ZDEX_TOKENOMICS,
        "atomic_purchase_and_burn",
        _root(6),
    )

    # Act / Assert
    assert command.command_root == (
        "0x32e3980f3a32fe0aefcb60bf64b138853d9ace775a7a16ce91976c152f8fbf1a"
    )
