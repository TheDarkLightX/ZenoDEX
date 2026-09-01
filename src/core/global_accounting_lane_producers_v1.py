"""Registered-empty lane fragment producers (wave A: EXTERNAL_CUSTODY, PROOF_REWARDS).

A registered-empty lane has exactly one representable typed state, the empty
one, and its committed lane root must be that state's root. The producer is a
pure function of the committed ``LaneStateRootV1``: it certifies that the lane
is registered as empty, disabled, and committed at the empty state's root, and
returns the exact-empty fragment the certificate checker requires. Any other
root, an enabled lane, or an unregistered lane rejects with a closed code and
produces nothing.

Research-only evidence. It grants no writer, verifier, release, or
publication authority, and no lane producer is receipt-backed.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_accounting_allocation_certificate_v1 import (
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
    REGISTERED_EMPTY_LANE_ROOTS_V1,
    LaneAllocationFragmentV1,
    LaneProducerKindV1,
)
from .global_settlement_types_v1 import LaneIdV1, LaneStateRootV1, _require_root

REGISTERED_EMPTY_PRODUCER_LANES_V1: Final[tuple[LaneIdV1, ...]] = tuple(
    lane
    for lane in LaneIdV1
    if LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane][0]
    in (LaneProducerKindV1.REGISTERED_EMPTY_DISABLED, LaneProducerKindV1.REGISTERED_EMPTY_BLOCKED)
)


class LaneProducerRejectCodeV1(str, Enum):
    """Closed reject codes of the registered-empty producers, in check precedence."""

    LANE_NOT_REGISTERED_EMPTY = "LANE_NOT_REGISTERED_EMPTY"
    LANE_ENABLED = "LANE_ENABLED"
    REGISTERED_EMPTY_ROOT_DRIFT = "REGISTERED_EMPTY_ROOT_DRIFT"


LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1: Final[dict[LaneProducerRejectCodeV1, str]] = {
    LaneProducerRejectCodeV1.LANE_NOT_REGISTERED_EMPTY: "lane has no registered-empty producer",
    LaneProducerRejectCodeV1.LANE_ENABLED: "registered-empty lane is enabled",
    LaneProducerRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT: "committed lane root is not the empty lane state root",
}


@dataclass(frozen=True, slots=True)
class LaneProducerRejectedV1:
    """A producer refusal: nothing is produced and the committed lane root is echoed unchanged."""

    code: LaneProducerRejectCodeV1
    lane_id: LaneIdV1
    committed_lane_root: str

    def __post_init__(self) -> None:
        if type(self.code) is not LaneProducerRejectCodeV1:
            raise TypeError("lane producer reject code is not closed")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane producer lane id is not closed")
        _require_root(self.committed_lane_root, name="lane producer committed lane root", allow_zero=True)

    @property
    def message(self) -> str:
        return LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1[self.code]

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "lane_id": self.lane_id,
            "message": self.message,
            "committed_lane_root": self.committed_lane_root,
        }


def produce_registered_empty_fragment_v1(
    lane_root: LaneStateRootV1,
) -> LaneAllocationFragmentV1 | LaneProducerRejectedV1:
    """Produce the exact-empty fragment of a registered-empty lane from its committed root."""

    if type(lane_root) is not LaneStateRootV1:
        raise TypeError("lane producer input must be the exact LaneStateRootV1")
    registered_kind, _ = LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane_root.lane_id]
    empty_root = REGISTERED_EMPTY_LANE_ROOTS_V1.get(lane_root.lane_id)
    if lane_root.lane_id not in REGISTERED_EMPTY_PRODUCER_LANES_V1 or empty_root is None:
        return LaneProducerRejectedV1(LaneProducerRejectCodeV1.LANE_NOT_REGISTERED_EMPTY, lane_root.lane_id, lane_root.state_root)
    if lane_root.enabled:
        return LaneProducerRejectedV1(LaneProducerRejectCodeV1.LANE_ENABLED, lane_root.lane_id, lane_root.state_root)
    if lane_root.state_root != empty_root:
        return LaneProducerRejectedV1(LaneProducerRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT, lane_root.lane_id, lane_root.state_root)
    return LaneAllocationFragmentV1(
        lane_id=lane_root.lane_id,
        module_release_id=lane_root.module_release_id,
        enabled=False,
        lane_state_root=lane_root.state_root,
        producer_kind=registered_kind,
        binding_root=lane_root.state_root,
    )


__all__ = [
    "LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1",
    "REGISTERED_EMPTY_PRODUCER_LANES_V1",
    "LaneProducerRejectCodeV1",
    "LaneProducerRejectedV1",
    "produce_registered_empty_fragment_v1",
]
