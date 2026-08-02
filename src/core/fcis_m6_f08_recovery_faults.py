"""PRE/POST/reject recovery observations for the unmounted FCIS M6 lane.

F08 is a value-level crash and physical-corruption model.  It validates exact
PRE and POST layouts through F04, then classifies one observed byte string. A
valid observation is either byte-identical PRE or byte-identical POST. Any
corruption or third valid layout returns a rejection/lock observation with no
partial history and no value-moving capability.

The module does not claim that a production datastore exposes only these
states. An adapter must refine this relation with transaction, WAL, fsync, and
fault-injection evidence.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from .fcis_m6_f04_fixed_point import (
    F04FixedPointCodeV1,
    F04FixedPointRejectV1,
    F04FixedPointSuccessV1,
    check_whole_layout_fixed_point,
)

FCIS_M6_F08_RECOVERY_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f08/recovery/v1"
_ROOT_HEX: Final[frozenset[str]] = frozenset("0123456789abcdef")


class F08RecoveryOutcomeV1(Enum):
    """Only durable observations admitted after a crash or reopen."""

    PRE = "pre"
    POST = "post"
    REJECTED_LOCKED = "rejected_locked"


class F08RecoveryCodeV1(Enum):
    """Stable setup failures for the PRE/POST recovery relation."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    PRE_SETUP_REJECTED = "pre_setup_rejected"
    POST_SETUP_REJECTED = "post_setup_rejected"
    PRE_POST_NOT_DISTINCT = "pre_post_not_distinct"


class F08RecoveryError(ValueError):
    """Raised when an F08 observation is outside its closed schema."""


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _ROOT_HEX for character in value[2:])
    ):
        raise F08RecoveryError(f"{name} must be a lowercase 32-byte root")
    return value


@dataclass(frozen=True, slots=True)
class F08RecoveryObservationV1:
    """Crash observation with an explicit lock and no partial value."""

    outcome: F08RecoveryOutcomeV1
    observed_layout_root: str | None
    rejection_code: F04FixedPointCodeV1 | None
    rejection_path: tuple[str, ...]
    requires_fresh_authorization: bool
    can_accept_value_movement: bool

    def __post_init__(self) -> None:
        if type(self.outcome) is not F08RecoveryOutcomeV1:
            raise F08RecoveryError("recovery outcome has the wrong exact type")
        if self.observed_layout_root is not None:
            _root(self.observed_layout_root, "observed_layout_root")
        if self.rejection_code is not None and type(self.rejection_code) is not F04FixedPointCodeV1:
            raise F08RecoveryError("rejection code has the wrong exact type")
        if type(self.rejection_path) is not tuple or any(
            type(part) is not str for part in self.rejection_path
        ):
            raise F08RecoveryError("rejection path must be an exact string tuple")
        if type(self.requires_fresh_authorization) is not bool:
            raise F08RecoveryError("authorization latch must be an exact bool")
        if type(self.can_accept_value_movement) is not bool:
            raise F08RecoveryError("movement capability must be an exact bool")
        if not self.requires_fresh_authorization:
            raise F08RecoveryError("every F08 observation must require fresh authorization")
        if self.can_accept_value_movement:
            raise F08RecoveryError("F08 recovery observation cannot move value")
        if self.outcome is F08RecoveryOutcomeV1.REJECTED_LOCKED:
            if self.observed_layout_root is not None or self.rejection_code is None:
                raise F08RecoveryError("rejected recovery cannot expose a partial layout")
        elif self.observed_layout_root is None or self.rejection_code is not None:
            raise F08RecoveryError("PRE/POST recovery must expose only its exact root")


@dataclass(frozen=True, slots=True)
class F08RecoverySetupRejectV1:
    """Typed failure when the PRE/POST reference pair is not valid."""

    code: F08RecoveryCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F08RecoveryCodeV1:
            raise F08RecoveryError("F08 setup code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F08RecoveryError("F08 setup path must be an exact string tuple")


F08RecoveryResultV1: TypeAlias = F08RecoveryObservationV1 | F08RecoverySetupRejectV1


def _locked(
    *,
    rejection_code: F04FixedPointCodeV1,
    rejection_path: tuple[str, ...],
) -> F08RecoveryObservationV1:
    return F08RecoveryObservationV1(
        outcome=F08RecoveryOutcomeV1.REJECTED_LOCKED,
        observed_layout_root=None,
        rejection_code=rejection_code,
        rejection_path=rejection_path,
        requires_fresh_authorization=True,
        can_accept_value_movement=False,
    )


def _checked_layout(payload: bytes) -> F04FixedPointSuccessV1 | F04FixedPointRejectV1:
    result = check_whole_layout_fixed_point(payload)
    if type(result) is F04FixedPointSuccessV1:
        return result
    return cast(F04FixedPointRejectV1, result)


def observe_f08_recovery(
    pre_payload: object,
    post_payload: object,
    observed_payload: object,
) -> F08RecoveryResultV1:
    """Classify one crash observation against exact PRE and POST values."""

    if type(pre_payload) is not bytes or type(post_payload) is not bytes:
        return F08RecoverySetupRejectV1(F08RecoveryCodeV1.WRONG_EXACT_TYPE, ("reference",))
    if type(observed_payload) is not bytes:
        return _locked(
            rejection_code=F04FixedPointCodeV1.WRONG_EXACT_TYPE,
            rejection_path=("observed",),
        )
    pre = _checked_layout(pre_payload)
    if type(pre) is not F04FixedPointSuccessV1:
        return F08RecoverySetupRejectV1(
            F08RecoveryCodeV1.PRE_SETUP_REJECTED,
            ("pre", pre.code.value),
        )
    post = _checked_layout(post_payload)
    if type(post) is not F04FixedPointSuccessV1:
        return F08RecoverySetupRejectV1(
            F08RecoveryCodeV1.POST_SETUP_REJECTED,
            ("post", post.code.value),
        )
    if pre_payload == post_payload:
        return F08RecoverySetupRejectV1(
            F08RecoveryCodeV1.PRE_POST_NOT_DISTINCT,
            ("pre", "post"),
        )
    if observed_payload == pre_payload:
        return F08RecoveryObservationV1(
            outcome=F08RecoveryOutcomeV1.PRE,
            observed_layout_root=pre.layout.layout_root,
            rejection_code=None,
            rejection_path=(),
            requires_fresh_authorization=True,
            can_accept_value_movement=False,
        )
    if observed_payload == post_payload:
        return F08RecoveryObservationV1(
            outcome=F08RecoveryOutcomeV1.POST,
            observed_layout_root=post.layout.layout_root,
            rejection_code=None,
            rejection_path=(),
            requires_fresh_authorization=True,
            can_accept_value_movement=False,
        )
    observed = _checked_layout(observed_payload)
    if type(observed) is F04FixedPointRejectV1:
        return _locked(
            rejection_code=observed.code,
            rejection_path=("observed", *observed.path),
        )
    return _locked(
        rejection_code=F04FixedPointCodeV1.FIXED_POINT_MISMATCH,
        rejection_path=("observed", "third_layout"),
    )


__all__ = (
    "FCIS_M6_F08_RECOVERY_SCHEMA_V1",
    "F08RecoveryCodeV1",
    "F08RecoveryError",
    "F08RecoveryObservationV1",
    "F08RecoveryOutcomeV1",
    "F08RecoveryResultV1",
    "F08RecoverySetupRejectV1",
    "observe_f08_recovery",
)
