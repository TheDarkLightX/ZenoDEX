"""Reference autonomous-governance PROPOSERS for ZenoDEX (deterministic, advisory).

These are the "proposer" side of the proposer/gate architecture (see
docs/AUTONOMOUS_GOVERNANCE_ARCHITECTURE.md). A proposer computes a *candidate* next parameter
value; it has NO authority. The verified gate (`gov_gate.py` / the `gov_*_v1.tau` specs) decides
admissibility, and `gov_loop.py` composes the two with `curr` bound to committed state.

SCOPE / NON-CLAIMS: this module is a REFERENCE implementation for simulation + demonstrating the
loop end-to-end. It is NOT wired into any live governance path, NOT consensus-critical, and carries
no authority — a mis-tuned or poisoned proposer here can only ever produce a candidate that the gate
then bounds. Determinism IS load-bearing for the design (a real on-chain proposer must be replayable):
both proposers below are pure integer / fixed-point functions with NO floats and NO randomness, and
their inputs are type-validated (non-`int`/`bool` rejected) so the integer property actually holds.

Two archetypes (the ones discussed for ZenoDEX):
  * PI controller  -- continuous target-tracking (e.g. a peg-class monetary param). PI, not full PID:
    the derivative term amplifies oracle noise (cf. RAI/Reflexer, which is effectively PI). Implemented
    in VELOCITY form (the committed parameter is the accumulator; Δ = Kp·(e−e_prev) + Ki·e), which has
    inherent anti-windup (clamping the output, plus the gate's step-limit, bounds growth) and does NOT
    run away at steady state. Inside the deadband the controller freezes. Fixed-point integer math.
  * Frozen Q-table -- discrete multi-factor rules. Train offline, FREEZE as a hash-pinned artifact;
    the runtime is a pure function: state -> deterministic integer binning -> table lookup -> action.
    A missing bin is fail-closed (returns the current value = no change); a non-int action is rejected.

ROUNDING: all division is Python floor-division (`//`, truncates toward -inf). This is deterministic
in CPython, but a port to another language MUST use the same rounding mode or honest nodes diverge.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass


def _is_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _clamp(v: int, lo: int, hi: int) -> int:
    return lo if v < lo else hi if v > hi else v


# --------------------------------------------------------------------------- #
# PI controller (continuous target-tracking; PI not PID; VELOCITY form; integer)
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class PIConfig:
    """Immutable PI tuning. Gains are rationals kp_num/kp_den, ki_num/ki_den (integer math).

    `deadband` freezes the controller for |error| <= deadband (anti-churn). `out_lo`/`out_hi` clamp
    the proposed value to a sane band BEFORE the gate (the gate's step-limit is the real
    rate-limiter; this is just a coarse guard, and the velocity form's anti-windup). All fields must
    be plain ints; denominators must be > 0; out_lo <= out_hi; deadband >= 0.
    """
    setpoint: int
    kp_num: int
    kp_den: int
    ki_num: int
    ki_den: int
    deadband: int
    out_lo: int
    out_hi: int

    def __post_init__(self) -> None:
        for name in ("setpoint", "kp_num", "kp_den", "ki_num", "ki_den", "deadband", "out_lo", "out_hi"):
            if not _is_int(getattr(self, name)):
                raise TypeError(f"PIConfig.{name} must be a plain int (no float/bool)")
        if self.kp_den <= 0 or self.ki_den <= 0:
            raise ValueError("PIConfig gain denominators must be > 0")
        if self.deadband < 0:
            raise ValueError("PIConfig.deadband must be >= 0")
        if self.out_lo > self.out_hi:
            raise ValueError("PIConfig out_lo must be <= out_hi")


@dataclass(frozen=True)
class PIResult:
    proposed: int
    prev_error: int  # controller state (velocity form) to carry into the next step


def pi_propose(curr: int, measured: int, prev_error: int, cfg: PIConfig) -> PIResult:
    """One VELOCITY-form PI step: Δ = Kp·(error − prev_error) + Ki·error; proposed = clamp(curr + Δ).

    error = measured − setpoint. When `measured` rises above `setpoint` the proposed value rises (the
    caller picks a knob whose increase pushes the target back down). Velocity form: the committed
    parameter IS the accumulator, so there is no separate integral to wind up — at steady state
    (error → 0, prev_error → 0) Δ → 0 and the value holds (no positional-form runaway). Inside the
    deadband the controller FREEZES: no Δ, no state change. Integer floor-division (no floats). The
    proposed value is still subject to the gate (bounds + per-revision step).
    """
    if not (_is_int(curr) and _is_int(measured) and _is_int(prev_error)):
        raise TypeError("pi_propose requires integer (non-bool) curr/measured/prev_error")
    if type(cfg) is not PIConfig:
        # exact type (subclasses rejected): only the PIConfig constructor runs the field
        # validation, so a duck-typed/look-alike cfg could smuggle floats into the math.
        raise TypeError("pi_propose requires a PIConfig (exact type)")
    error = measured - cfg.setpoint
    if -cfg.deadband <= error <= cfg.deadband:
        return PIResult(proposed=curr, prev_error=prev_error)  # freeze inside the deadband
    delta = (cfg.kp_num * (error - prev_error)) // cfg.kp_den + (cfg.ki_num * error) // cfg.ki_den
    proposed = _clamp(curr + delta, cfg.out_lo, cfg.out_hi)
    return PIResult(proposed=proposed, prev_error=error)


# --------------------------------------------------------------------------- #
# Frozen Q-learning lookup table (discrete multi-factor; deterministic; hash-pinned)
# --------------------------------------------------------------------------- #
def bin_index(value: int, edges: tuple[int, ...]) -> int:
    """Deterministic integer binning: number of leading edges with value >= edge.

    edges must be plain ints, strictly ascending (both enforced, fail-closed: a malformed edge
    table is a config error, not a bin). Returns an index in [0, len(edges)]. Pure integer
    comparison.
    """
    if not _is_int(value):
        raise TypeError("bin_index requires an integer (non-bool) value")
    prev: int | None = None
    for e in edges:
        if not _is_int(e):
            raise TypeError("bin_index edges must be plain ints (no float/bool)")
        if prev is not None and e <= prev:
            raise ValueError("bin_index edges must be strictly ascending")
        prev = e
    idx = 0
    for e in edges:
        if value >= e:
            idx += 1
        else:
            break
    return idx


def state_key(bins: tuple[int, ...]) -> str:
    """Canonical key for a binned state (so the table is JSON-serialisable + hashable).

    bins must be plain ints (enforced): a bool bin would stringify as "True" and silently key a
    different table row than the int it equals (True == 1 but str(True) != "1").
    """
    for b in bins:
        if not _is_int(b):
            raise TypeError("state_key bins must be plain ints (no float/bool)")
    return ",".join(str(b) for b in bins)


def table_hash(table: dict[str, int]) -> str:
    """SHA-256 over the canonical (sorted-key) JSON of the frozen table — the pin a client checks."""
    canonical = json.dumps(table, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class QResult:
    proposed: int
    state_key: str
    hit: bool  # False => bin missing => fail-closed default returned


def q_table_propose(bins: tuple[int, ...], table: dict[str, int], curr: int) -> QResult:
    """Look up the action for a binned state in a FROZEN table.

    Pure function: same bins + same table => same result (replay-stable). A missing bin is
    FAIL-CLOSED: returns `curr` (propose no change) rather than guessing. A present-but-non-int action
    is REJECTED (the table must contain plain int actions). The returned value is still subject to the
    gate.
    """
    if not _is_int(curr):
        raise TypeError("q_table_propose requires an integer (non-bool) curr")
    key = state_key(bins)
    if key in table:
        action = table[key]
        if not _is_int(action):
            raise TypeError(f"q-table action for state {key!r} must be a plain int (no float/bool/str)")
        return QResult(proposed=action, state_key=key, hit=True)
    return QResult(proposed=curr, state_key=key, hit=False)
