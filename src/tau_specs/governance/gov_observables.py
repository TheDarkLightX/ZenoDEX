"""Deterministic OBSERVABLES for the autonomous-governance lane (reference, advisory).

The sensor side of the loop: frozen policies (Q-tables, layered Q, energy models) key
on BINNED state — and the binning is part of the policy's MEANING, so it must live on
the consensus side, not inside the artifact. This module turns raw committed metrics
into the state-key bins the proposers consume, with two fail-closed disciplines:

  * STALENESS — every observation carries the epoch it was last updated; a signal
    older than `max_stale` (or dated in the future — wrap/clock hostility) yields NO
    key, and the caller must HOLD. A stale sensor never silently feeds a policy.
  * EXACT TYPES — plain dict / plain str / plain int / exact Observation all the way
    down, validated while snapshotting in one traversal (the TOCTOU discipline).

MANIPULATION COST IS A PER-SIGNAL DUTY: every observable inherits the manipulation
surface of its source (the oracle lane is L2 trust-minimized, NOT trustless; pool-
depth — not window length — gates TWAP-class signals, per the zUSD buyback analysis).
The honest claim is layered: the pointwise gate bounds damage per revision, the
trajectory tier bounds it per window, and the signal's own manipulation cost makes
sustained bias expensive. Wiring real committed metrics into these bins (and binding
`now_epoch` to attested state) is the open WS5 integration.

Binning is IMPORT-BOUND to gov_proposers.bin_index so the sensor layer and the
proposers can never disagree about edge semantics.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import TypeGuard

import gov_proposers  # noqa: E402  (flat sibling import, same pattern as gov_loop)

_BIN_INDEX = gov_proposers.bin_index   # import-bound authority (r9 lesson)

_U16_MAX = 0xFFFF


def _is_plain_int(v: object) -> TypeGuard[int]:
    return type(v) is int


def _is_u16(v: object) -> TypeGuard[int]:
    return _is_plain_int(v) and 0 <= v <= _U16_MAX


def _is_plain_str(v: object) -> TypeGuard[str]:
    return type(v) is str


@dataclass(frozen=True)
class Observation:
    """One committed metric reading: the value and the epoch it was last updated."""
    value: int
    updated_epoch: int


def _validate_observation(o: object, *, signal: str) -> Observation:
    if type(o) is not Observation:
        raise TypeError(f"observations[{signal!r}] must be an Observation (exact type)")
    # re-validate fields at use: frozen=True is convenience, not a guarantee
    if not _is_u16(o.value):
        raise TypeError(f"observations[{signal!r}].value must be a plain int in [0, 65535]")
    if not _is_u16(o.updated_epoch):
        raise TypeError(f"observations[{signal!r}].updated_epoch must be a plain int in [0, 65535]")
    return o


def fresh_state_key(
    observations: dict[str, Observation],
    *,
    order: tuple[str, ...],
    edges: dict[str, tuple[int, ...]],
    now_epoch: int,
    max_stale: int,
) -> tuple[int, ...] | None:
    """Bin the named signals into a deterministic state key, or None if ANY is stale.

    `order` fixes the key layout (the same tuple the policy was trained/frozen
    against); every ordered signal must be present in both `observations` and
    `edges` — a MISSING signal is malformed wiring and raises (the signal set is
    static), while a STALE one is a runtime condition and yields None (the caller
    holds; autonomy fails closed, it does not act on dead sensors).

    Freshness is wrap-guarded like every epoch comparison in this suite:
    `now >= updated AND now - updated <= max_stale` — a future-dated observation
    (hostile or clock-skewed) is treated as stale, never as fresh.
    """
    if type(observations) is not dict:
        raise TypeError("observations must be a plain dict (no dict subclass)")
    if type(order) is not tuple or not order:
        raise TypeError("order must be a non-empty tuple of plain str signal names")
    if type(edges) is not dict:
        raise TypeError("edges must be a plain dict (no dict subclass)")
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    if not _is_u16(max_stale):
        raise TypeError("max_stale must be a plain int in [0, 65535]")

    # snapshot-validate everything BEFORE any freshness decision (one traversal each)
    obs: dict[str, Observation] = {}
    for k, v in observations.items():
        if not _is_plain_str(k):
            raise TypeError("observation keys must be plain str")
        obs[k] = _validate_observation(v, signal=k)
    edge_snap: dict[str, tuple[int, ...]] = {}
    for k, e in edges.items():
        if not _is_plain_str(k):
            raise TypeError("edge keys must be plain str")
        if type(e) is not tuple:
            raise TypeError(f"edges[{k!r}] must be a tuple of plain ints")
        edge_snap[k] = e  # bin_index re-validates contents (ascending plain ints)
    for s in order:
        if not _is_plain_str(s):
            raise TypeError("order entries must be plain str")
        if s not in obs:
            raise ValueError(f"missing observation for ordered signal {s!r}")
        if s not in edge_snap:
            raise ValueError(f"missing edges for ordered signal {s!r}")

    bins: list[int] = []
    for s in order:
        o = obs[s]
        fresh = now_epoch >= o.updated_epoch and (now_epoch - o.updated_epoch) <= max_stale
        if not fresh:
            return None   # stale or future-dated: HOLD
        bins.append(_BIN_INDEX(o.value, edge_snap[s]))
    return tuple(bins)
