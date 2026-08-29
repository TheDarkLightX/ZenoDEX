"""Closed disabled transition for the empty registered-external lane.

The current M6 profile contains no approved external destination, finality
policy, or mint/release adapter.  This functional core therefore represents
the only safe current state: an empty registry with no pending external
obligation and no acknowledgment.  Every registered external command rejects
as ``DISABLED_FEATURE`` with the exact pre-state root and empty effects.

This module is research-only evidence.  It supplies no writer, adapter,
receipt-verifier, release, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
    _require_token,
    hash_global_v1,
)

EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1: Final = (
    "zenodex/external-custody-disabled-state/v1"
)


class ExternalCustodyCommandKindV1(str, Enum):
    """Complete command vocabulary for the currently disabled lane."""

    REGISTERED_EXTERNAL_LOCK = "registered_external_lock"
    REGISTERED_EXTERNAL_BURN = "registered_external_burn"
    REGISTERED_EXTERNAL_RELEASE = "registered_external_release"
    REGISTERED_EXTERNAL_MINT = "registered_external_mint"
    EXTERNAL_FINALITY = "external_finality"
    EXTERNAL_TIMEOUT = "external_timeout"
    EXTERNAL_REFUND = "external_refund"
    OUTBOX_ACKNOWLEDGMENT = "outbox_acknowledgment"
    DESTINATION_IDEMPOTENCY = "destination_idempotency"


EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1: Final = tuple(ExternalCustodyCommandKindV1)


@dataclass(frozen=True, slots=True)
class ExternalCustodyCommandV1:
    """One attempted command against the empty external registry."""

    kind: ExternalCustodyCommandKindV1
    destination_id: str
    external_object_id: str

    def __post_init__(self) -> None:
        if type(self.kind) is not ExternalCustodyCommandKindV1:
            raise TypeError("external command kind must be the exact closed enum")
        for field_name in ("destination_id", "external_object_id"):
            value = getattr(self, field_name)
            if type(value) is not str:
                raise TypeError(f"external command {field_name} must be exact text")
            _require_token(value, name=f"external command {field_name}")

    @property
    def command_root(self) -> str:
        return hash_global_v1("external-custody-command-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "destination_id": self.destination_id,
            "external_object_id": self.external_object_id,
        }


@dataclass(frozen=True, slots=True)
class ExternalCustodyDisabledStateV1:
    """The unique representable state for an empty external registry."""

    registry_entries: tuple[()] = ()
    pending_external_obligations: tuple[()] = ()
    outbox_acknowledgments: tuple[()] = ()

    def __post_init__(self) -> None:
        for field_name in (
            "registry_entries",
            "pending_external_obligations",
            "outbox_acknowledgments",
        ):
            value = getattr(self, field_name)
            if type(value) is not tuple or value != ():
                raise ValueError(
                    f"disabled external state {field_name} must be the exact empty tuple"
                )

    @property
    def state_root(self) -> str:
        return hash_global_v1("external-custody-disabled-state-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1,
            "registry_entries": self.registry_entries,
            "pending_external_obligations": self.pending_external_obligations,
            "outbox_acknowledgments": self.outbox_acknowledgments,
        }


def transition_external_custody_disabled_v1(
    pre_state: ExternalCustodyDisabledStateV1,
    command: ExternalCustodyCommandV1,
) -> LaneTransitionRejectedV1:
    """Reject every closed command without consuming or emitting anything."""

    if type(pre_state) is not ExternalCustodyDisabledStateV1:
        raise TypeError("external disabled state must be the exact typed value")
    if type(command) is not ExternalCustodyCommandV1:
        raise TypeError("external disabled command must be the exact typed value")
    pre_state.__post_init__()
    command.__post_init__()
    return LaneTransitionRejectedV1.reject(
        LaneTransitionRejectCodeV1.DISABLED_FEATURE,
        pre_state.state_root,
    )


__all__ = [
    "EXTERNAL_CUSTODY_DISABLED_COMMANDS_V1",
    "EXTERNAL_CUSTODY_DISABLED_STATE_SCHEMA_V1",
    "ExternalCustodyCommandKindV1",
    "ExternalCustodyCommandV1",
    "ExternalCustodyDisabledStateV1",
    "transition_external_custody_disabled_v1",
]
