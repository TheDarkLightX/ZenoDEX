"""Whole-layout canonical fixed-point gate for the F03 reopen relation.

F04 is the narrow caller-facing gate for durable-layout bytes.  It preserves
the F03 partial relation and independently materializes the accepted history
again before exposing a success value.  A selected layout root is never used
as a substitute for complete canonical equality.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

from .fcis_m6_f02_history_encoder import (
    F02AuthorizedHistoryV1,
    F02DurableLayoutV1,
    F02HistoryEncoderError,
    encode_history,
    encode_layout_v1,
)
from .fcis_m6_f03_reopen import (
    F03ReopenCodeV1,
    F03ReopenRejectV1,
    F03ReopenSuccessV1,
    reopen_layout_bytes,
)

FCIS_M6_F04_FIXED_POINT_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f04/fixed-point/v1"


class F04FixedPointCodeV1(Enum):
    """Stable F04 gate outcomes."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    REOPEN_REJECTED = "reopen_rejected"
    FIXED_POINT_MISMATCH = "fixed_point_mismatch"


class F04FixedPointError(ValueError):
    """Raised when a F04 result is constructed outside its typed contract."""


@dataclass(frozen=True, slots=True)
class F04FixedPointRejectV1:
    """Typed failure without a partial history or authority witness."""

    code: F04FixedPointCodeV1
    path: tuple[str, ...]
    source_code: F03ReopenCodeV1 | None

    def __post_init__(self) -> None:
        if type(self.code) is not F04FixedPointCodeV1:
            raise F04FixedPointError("fixed-point code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F04FixedPointError("fixed-point path must be an exact string tuple")
        if self.source_code is not None and type(self.source_code) is not F03ReopenCodeV1:
            raise F04FixedPointError("source rejection code has the wrong exact type")


@dataclass(frozen=True, slots=True)
class F04FixedPointSuccessV1:
    """Complete history/layout pair that passed independent byte equality."""

    history: F02AuthorizedHistoryV1
    layout: F02DurableLayoutV1
    canonical_layout_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.history) is not F02AuthorizedHistoryV1:
            raise F04FixedPointError("fixed-point history has the wrong exact type")
        if type(self.layout) is not F02DurableLayoutV1:
            raise F04FixedPointError("fixed-point layout has the wrong exact type")
        if type(self.canonical_layout_bytes) is not bytes:
            raise F04FixedPointError("fixed-point bytes have the wrong exact type")
        self.history.__post_init__()
        self.layout.__post_init__()
        if encode_history(self.history) != self.layout:
            raise F04FixedPointError("fixed-point layout is not source-derived")
        if encode_layout_v1(self.layout) != self.canonical_layout_bytes:
            raise F04FixedPointError("fixed-point bytes are not canonical")


F04FixedPointResultV1: TypeAlias = F04FixedPointSuccessV1 | F04FixedPointRejectV1


def _reject(
    code: F04FixedPointCodeV1,
    path: tuple[str, ...],
    source_code: F03ReopenCodeV1 | None = None,
) -> F04FixedPointRejectV1:
    return F04FixedPointRejectV1(code=code, path=path, source_code=source_code)


def check_whole_layout_fixed_point(payload: object) -> F04FixedPointResultV1:
    """Accept only bytes equal to a complete source-derived F02 layout."""

    if type(payload) is not bytes:
        return _reject(F04FixedPointCodeV1.WRONG_EXACT_TYPE, ("payload",))

    reopened = reopen_layout_bytes(payload)
    if type(reopened) is F03ReopenRejectV1:
        return _reject(
            F04FixedPointCodeV1.REOPEN_REJECTED,
            reopened.path,
            reopened.code,
        )
    if type(reopened) is not F03ReopenSuccessV1:
        return _reject(F04FixedPointCodeV1.REOPEN_REJECTED, ("reopen",))

    try:
        materialized = encode_history(reopened.history)
        canonical_bytes = encode_layout_v1(materialized)
    except (F02HistoryEncoderError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(F04FixedPointCodeV1.FIXED_POINT_MISMATCH, ("layout",))

    if (
        materialized.layout_root != reopened.layout_root
        or canonical_bytes != payload
        or canonical_bytes != reopened.canonical_layout_bytes
    ):
        return _reject(F04FixedPointCodeV1.FIXED_POINT_MISMATCH, ("layout",))

    try:
        return F04FixedPointSuccessV1(
            history=reopened.history,
            layout=materialized,
            canonical_layout_bytes=canonical_bytes,
        )
    except (F04FixedPointError, F02HistoryEncoderError, TypeError, ValueError, ArithmeticError):
        return _reject(F04FixedPointCodeV1.FIXED_POINT_MISMATCH, ("layout",))


__all__ = (
    "FCIS_M6_F04_FIXED_POINT_SCHEMA_V1",
    "F04FixedPointCodeV1",
    "F04FixedPointError",
    "F04FixedPointRejectV1",
    "F04FixedPointResultV1",
    "F04FixedPointSuccessV1",
    "check_whole_layout_fixed_point",
)
