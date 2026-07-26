"""Immutable semantic state-read evidence for FCIS support profile v5.

The trace is produced by the exact sequential evaluator.  It is independent of
the declared support set.  Local transition primitives extend it from the exact
keys they read or compare; the support-root checker later proves containment.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import final


def _canonical_pairs_v5(
    name: str,
    values: tuple[tuple[str, str], ...],
) -> tuple[tuple[str, str], ...]:
    if type(values) is not tuple:
        raise TypeError(f"{name} must be an exact tuple")
    for value in values:
        if (
            type(value) is not tuple
            or len(value) != 2
            or type(value[0]) is not str
            or not value[0]
            or type(value[1]) is not str
            or not value[1]
        ):
            raise TypeError(f"{name} must contain exact nonempty string pairs")
    if values != tuple(sorted(values)) or len(values) != len(set(values)):
        raise ValueError(f"{name} must be canonical and duplicate-free")
    return values


def _canonical_strings_v5(name: str, values: tuple[str, ...]) -> tuple[str, ...]:
    if type(values) is not tuple or any(type(value) is not str or not value for value in values):
        raise TypeError(f"{name} must be an exact tuple of nonempty strings")
    if values != tuple(sorted(values)) or len(values) != len(set(values)):
        raise ValueError(f"{name} must be canonical and duplicate-free")
    return values


@final
@dataclass(frozen=True, slots=True)
class FCISStateReadTraceV5:
    """Canonical semantic cell reads observed during one exact evaluation."""

    balance_keys: tuple[tuple[str, str], ...] = ()
    pool_ids: tuple[str, ...] = ()
    lp_keys: tuple[tuple[str, str], ...] = ()
    nonce_keys: tuple[str, ...] = ()
    reads_fee_accumulator: bool = False

    def __post_init__(self) -> None:
        _canonical_pairs_v5("trace balance keys", self.balance_keys)
        _canonical_strings_v5("trace pool ids", self.pool_ids)
        _canonical_pairs_v5("trace LP keys", self.lp_keys)
        _canonical_strings_v5("trace nonce keys", self.nonce_keys)
        if type(self.reads_fee_accumulator) is not bool:
            raise TypeError("trace fee flag must be an exact bool")


def extend_fcis_state_read_trace_v5(
    trace: FCISStateReadTraceV5,
    *,
    balance_keys: tuple[tuple[str, str], ...] = (),
    pool_ids: tuple[str, ...] = (),
    lp_keys: tuple[tuple[str, str], ...] = (),
    nonce_keys: tuple[str, ...] = (),
    reads_fee_accumulator: bool = False,
) -> FCISStateReadTraceV5:
    """Return a new trace; the supplied trace remains unchanged."""

    if type(trace) is not FCISStateReadTraceV5:
        raise TypeError("trace extension requires an exact trace")
    _canonical_pairs_v5("new balance keys", balance_keys)
    _canonical_strings_v5("new pool ids", pool_ids)
    _canonical_pairs_v5("new LP keys", lp_keys)
    _canonical_strings_v5("new nonce keys", nonce_keys)
    if type(reads_fee_accumulator) is not bool:
        raise TypeError("new fee flag must be an exact bool")
    return FCISStateReadTraceV5(
        balance_keys=tuple(sorted(set(trace.balance_keys) | set(balance_keys))),
        pool_ids=tuple(sorted(set(trace.pool_ids) | set(pool_ids))),
        lp_keys=tuple(sorted(set(trace.lp_keys) | set(lp_keys))),
        nonce_keys=tuple(sorted(set(trace.nonce_keys) | set(nonce_keys))),
        reads_fee_accumulator=trace.reads_fee_accumulator or reads_fee_accumulator,
    )


def merge_fcis_state_read_traces_v5(
    left: FCISStateReadTraceV5,
    right: FCISStateReadTraceV5,
) -> FCISStateReadTraceV5:
    """Return the canonical union of two independently produced traces."""

    if type(right) is not FCISStateReadTraceV5:
        raise TypeError("trace merge requires exact traces")
    return extend_fcis_state_read_trace_v5(
        left,
        balance_keys=right.balance_keys,
        pool_ids=right.pool_ids,
        lp_keys=right.lp_keys,
        nonce_keys=right.nonce_keys,
        reads_fee_accumulator=right.reads_fee_accumulator,
    )


@final
@dataclass(frozen=True, slots=True)
class FCISContextReadTraceV5:
    """Canonical context paths explicitly projected before evaluation."""

    paths: tuple[str, ...]

    def __post_init__(self) -> None:
        _canonical_strings_v5("context read paths", self.paths)


EMPTY_FCIS_STATE_READ_TRACE_V5 = FCISStateReadTraceV5()
EMPTY_FCIS_CONTEXT_READ_TRACE_V5 = FCISContextReadTraceV5(())


__all__ = (
    "EMPTY_FCIS_CONTEXT_READ_TRACE_V5",
    "EMPTY_FCIS_STATE_READ_TRACE_V5",
    "FCISContextReadTraceV5",
    "FCISStateReadTraceV5",
    "extend_fcis_state_read_trace_v5",
    "merge_fcis_state_read_traces_v5",
)
