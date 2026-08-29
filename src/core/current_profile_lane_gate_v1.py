"""Total fail-closed gate for the current 12-lane economic profile.

Every capability in the closed 103-capability registry has a deterministic
current-profile outcome. The eleven economically unresolved lanes reject as
``POLICY_REJECT``. The empty external lane rejects as ``DISABLED_FEATURE``.
Cross-lane state/command pairs reject as ``INVALID_CONTEXT``. Every outcome
preserves the supplied committed lane root and emits no economic effect.

This gate keeps partial and donor implementations outside settlement authority
until a governed profile selects their economics and release bindings. It is
not an implementation of the rejected feature semantics and grants no proof,
mount, migration, publication, or value-moving authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_settlement_types_v1 import (
    LaneIdV1,
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
    _require_root,
    hash_global_v1,
)
from .lane_capability_registry_v1 import (
    LANE_CAPABILITY_REGISTRY_V1,
    LaneCapabilityDispositionV1,
    lane_capability_registry_root_v1,
    resolve_lane_capability_v1,
)

CURRENT_PROFILE_LANE_COMMAND_SCHEMA_V1: Final = (
    "zenodex/current-profile-lane-command/v1"
)


@dataclass(frozen=True, slots=True)
class CurrentProfileLaneStateV1:
    lane_id: LaneIdV1
    lane_state_root: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("current-profile state lane id must be exact")
        if type(self.lane_state_root) is not str:
            raise TypeError("current-profile lane state root must be exact text")
        _require_root(self.lane_state_root, name="current-profile lane state root")


@dataclass(frozen=True, slots=True)
class CurrentProfileLaneCommandV1:
    lane_id: LaneIdV1
    capability_id: str
    command_body_hash: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("current-profile command lane id must be exact")
        if type(self.capability_id) is not str:
            raise TypeError("current-profile capability id must be exact text")
        if type(self.command_body_hash) is not str:
            raise TypeError("current-profile command body hash must be exact text")
        resolve_lane_capability_v1(self.lane_id, self.capability_id)
        _require_root(self.command_body_hash, name="current-profile command body hash")

    @property
    def command_root(self) -> str:
        return hash_global_v1(
            "current-profile-lane-command-v1",
            {
                "schema": CURRENT_PROFILE_LANE_COMMAND_SCHEMA_V1,
                "registry_root": lane_capability_registry_root_v1(),
                "lane_id": self.lane_id,
                "capability_id": self.capability_id,
                "command_body_hash": self.command_body_hash,
            },
        )


def _lane_disposition_v1(lane_id: LaneIdV1) -> LaneCapabilityDispositionV1:
    return LANE_CAPABILITY_REGISTRY_V1[tuple(LaneIdV1).index(lane_id)].disposition


def transition_current_profile_lane_v1(
    pre_state: CurrentProfileLaneStateV1,
    command: CurrentProfileLaneCommandV1,
) -> LaneTransitionRejectedV1:
    """Evaluate one current-profile capability as an exact no-effect reject."""

    if type(pre_state) is not CurrentProfileLaneStateV1:
        raise TypeError("current-profile lane state must be the exact typed value")
    if type(command) is not CurrentProfileLaneCommandV1:
        raise TypeError("current-profile lane command must be the exact typed value")
    pre_state.__post_init__()
    command.__post_init__()
    if pre_state.lane_id is not command.lane_id:
        code = LaneTransitionRejectCodeV1.INVALID_CONTEXT
    elif (
        _lane_disposition_v1(command.lane_id)
        is LaneCapabilityDispositionV1.DISABLED_PENDING_COMPLETE_PROFILE
    ):
        code = LaneTransitionRejectCodeV1.DISABLED_FEATURE
    else:
        code = LaneTransitionRejectCodeV1.POLICY_REJECT
    return LaneTransitionRejectedV1.reject(code, pre_state.lane_state_root)


__all__ = [
    "CURRENT_PROFILE_LANE_COMMAND_SCHEMA_V1",
    "CurrentProfileLaneCommandV1",
    "CurrentProfileLaneStateV1",
    "transition_current_profile_lane_v1",
]
