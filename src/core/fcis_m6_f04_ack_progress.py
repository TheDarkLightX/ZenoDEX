"""Prior-state acknowledgment monotonicity for the F04 pending-ack gap.

The F04 whole-layout fixed point cannot decide whether an absent
acknowledgment is a legitimate pending-delivery state when only the current
layout is available.  F04A adds the missing prior-state relation for an
ack-only update:

* every prior acknowledgment must still exist byte-for-byte;
* a new acknowledgment must be source-valid under F02;
* the authoritative history, authority, evidence, nullifier, and outbox
  projections must be unchanged;
* pending effects remain explicit when acknowledgments are absent.

This closes the prior-state deletion ambiguity for acknowledgment-only
progress.  It does not turn a current snapshot without prior evidence into a
universal missing-row theorem, and it does not mount a datastore writer.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final, TypeAlias

from .fcis_m6_f04_fixed_point import (
    F04FixedPointSuccessV1,
    check_whole_layout_fixed_point,
)

FCIS_M6_F04_ACK_PROGRESS_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f04/ack-progress/v1"
_ROOT_HEX: Final[frozenset[str]] = frozenset("0123456789abcdef")


class F04AckProgressCodeV1(Enum):
    """Stable outcomes for prior-state acknowledgment progress."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    PRIOR_REOPEN_REJECTED = "prior_reopen_rejected"
    CURRENT_REOPEN_REJECTED = "current_reopen_rejected"
    HISTORY_CHANGED = "history_changed"
    ACK_REMOVED = "ack_removed"
    ACK_MUTATED = "ack_mutated"


class F04AckProgressStatusV1(Enum):
    """Whether the current effect set still contains pending deliveries."""

    PENDING = "pending"
    ACKED = "acked"


class F04AckProgressError(ValueError):
    """Raised when an F04A value is outside its closed schema."""


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _ROOT_HEX for character in value[2:])
    ):
        raise F04AckProgressError(f"{name} must be a lowercase 32-byte root")
    return value


@dataclass(frozen=True, slots=True)
class F04AckProgressSuccessV1:
    """Prior-state checked ack-only progression with explicit pending effects."""

    prior_layout_root: str
    current_layout_root: str
    status: F04AckProgressStatusV1
    added_ack_effect_ids: tuple[str, ...]
    pending_effect_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        _root(self.prior_layout_root, "prior_layout_root")
        _root(self.current_layout_root, "current_layout_root")
        if type(self.status) is not F04AckProgressStatusV1:
            raise F04AckProgressError("ack progress status has the wrong exact type")
        for name, values in (
            ("added_ack_effect_ids", self.added_ack_effect_ids),
            ("pending_effect_ids", self.pending_effect_ids),
        ):
            if type(values) is not tuple or any(type(value) is not str for value in values):
                raise F04AckProgressError(f"{name} must be an exact string tuple")
            for value in values:
                _root(value, f"{name} item")
            if tuple(sorted(values)) != values or len(set(values)) != len(values):
                raise F04AckProgressError(f"{name} must be ordered and unique")
        if self.status is F04AckProgressStatusV1.PENDING and not self.pending_effect_ids:
            raise F04AckProgressError("pending status requires a pending effect")
        if self.status is F04AckProgressStatusV1.ACKED and self.pending_effect_ids:
            raise F04AckProgressError("acked status cannot retain pending effects")


@dataclass(frozen=True, slots=True)
class F04AckProgressRejectV1:
    """Typed prior-state rejection without a current authority value."""

    code: F04AckProgressCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F04AckProgressCodeV1:
            raise F04AckProgressError("ack progress code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F04AckProgressError("ack progress path must be an exact string tuple")


F04AckProgressResultV1: TypeAlias = F04AckProgressSuccessV1 | F04AckProgressRejectV1


def _reject(code: F04AckProgressCodeV1, *path: str) -> F04AckProgressRejectV1:
    return F04AckProgressRejectV1(code, path)


def _without_acks(value: F04FixedPointSuccessV1) -> object:
    return replace(value.history, acks=())


def _non_ack_layout_projection(value: F04FixedPointSuccessV1) -> tuple[object, ...]:
    header = value.layout.header
    header_projection = (
        header.genesis_state_root,
        header.current_state_root,
        header.deployment_config_root,
        header.verifier_profile_root,
        header.current_authority_state_root,
        header.current_authority_epoch_index,
        header.history_count,
        header.evidence_count,
        header.nullifier_count,
        header.outbox_count,
        header.authority_count,
    )
    return (
        _without_acks(value),
        header_projection,
        value.layout.authority_rows,
        value.layout.history_rows,
        value.layout.evidence_rows,
        value.layout.nullifier_rows,
        value.layout.outbox_rows,
    )


def _ack_map(value: F04FixedPointSuccessV1) -> dict[str, object]:
    return {row.effect_id: row for row in value.layout.ack_rows}


def check_f04_ack_progress(
    prior_payload: object,
    current_payload: object,
) -> F04AckProgressResultV1:
    """Require monotone acknowledgment progress between two F04 fixed points."""

    if type(prior_payload) is not bytes or type(current_payload) is not bytes:
        return _reject(F04AckProgressCodeV1.WRONG_EXACT_TYPE, "payload")
    prior = check_whole_layout_fixed_point(prior_payload)
    if type(prior) is not F04FixedPointSuccessV1:
        return _reject(F04AckProgressCodeV1.PRIOR_REOPEN_REJECTED, "prior")
    current = check_whole_layout_fixed_point(current_payload)
    if type(current) is not F04FixedPointSuccessV1:
        return _reject(F04AckProgressCodeV1.CURRENT_REOPEN_REJECTED, "current")

    if _non_ack_layout_projection(prior) != _non_ack_layout_projection(current):
        return _reject(F04AckProgressCodeV1.HISTORY_CHANGED, "current", "non_ack_projection")

    prior_acks = _ack_map(prior)
    current_acks = _ack_map(current)
    prior_ids = set(prior_acks)
    current_ids = set(current_acks)
    removed = sorted(prior_ids - current_ids)
    if removed:
        return _reject(F04AckProgressCodeV1.ACK_REMOVED, "current", "ack_rows")
    for effect_id in sorted(prior_ids & current_ids):
        if prior_acks[effect_id] != current_acks[effect_id]:
            return _reject(F04AckProgressCodeV1.ACK_MUTATED, "current", "ack_rows", effect_id)

    effect_ids = {row.record.effect_id for row in current.layout.outbox_rows}
    pending = tuple(sorted(effect_ids - current_ids))
    added = tuple(sorted(current_ids - prior_ids))
    status = F04AckProgressStatusV1.PENDING if pending else F04AckProgressStatusV1.ACKED
    try:
        return F04AckProgressSuccessV1(
            prior_layout_root=prior.layout.layout_root,
            current_layout_root=current.layout.layout_root,
            status=status,
            added_ack_effect_ids=added,
            pending_effect_ids=pending,
        )
    except (F04AckProgressError, TypeError, ValueError, ArithmeticError):
        return _reject(F04AckProgressCodeV1.CURRENT_REOPEN_REJECTED, "current", "ack_progress")


__all__ = (
    "FCIS_M6_F04_ACK_PROGRESS_SCHEMA_V1",
    "F04AckProgressCodeV1",
    "F04AckProgressError",
    "F04AckProgressResultV1",
    "F04AckProgressStatusV1",
    "F04AckProgressRejectV1",
    "F04AckProgressSuccessV1",
    "check_f04_ack_progress",
)
