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

Four archetypes (the ones discussed for ZenoDEX):
  * PI controller  -- continuous target-tracking (e.g. a peg-class monetary param). PI, not full PID:
    the derivative term amplifies oracle noise (cf. RAI/Reflexer, which is effectively PI). Implemented
    in VELOCITY form (the committed parameter is the accumulator; Δ = Kp·(e−e_prev) + Ki·e), which has
    inherent anti-windup (clamping the output, plus the gate's step-limit, bounds growth) and does NOT
    run away at steady state. Inside the deadband the controller freezes. Fixed-point integer math.
  * Frozen Q-table -- discrete multi-factor rules. Train offline, FREEZE as a hash-pinned artifact;
    the runtime is a pure function: state -> deterministic integer binning -> table lookup -> action.
    A missing bin is fail-closed (returns the current value = no change); a non-int action is rejected.
  * Layered (hierarchical) Q-tables -- the factored form of the above for multi-factor state: a
    regime layer selects a sub-policy, the sub-policy's action table yields the action. Avoids the
    joint-table combinatorial blowup; the WHOLE hierarchy is ONE hash-pinned artifact; every layer
    miss is fail-closed.
  * Frozen energy model -- energy-based reasoning in consensus-safe form: a hash-pinned integer
    energy E(c) = w_track*(c-target)^2 + w_move*|c-curr| scored over the EXACTLY-bounded revision
    band, argmin returned (smallest-candidate tie-break). The trade-off the model reasons about
    (tracking error vs. parameter churn) is explicit and replayable.

ROUNDING: all division is Python floor-division (`//`, truncates toward -inf). This is deterministic
in CPython, but a port to another language MUST use the same rounding mode or honest nodes diverge.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import TypeGuard


def _is_int(v: object) -> TypeGuard[int]:
    # EXACT type: a "plain int" only. `isinstance` would admit bool and any `int` subclass; a
    # hostile subclass can override `__sub__` (float into the math) or `__str__` (spoof a table
    # key), so the "pure integer" contract requires the exact built-in type. (TypeGuard so type
    # checkers narrow after the check; the runtime test is unchanged.)
    return type(v) is int


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
        _validate_piconfig(self)


_PICONFIG_FIELDS = ("setpoint", "kp_num", "kp_den", "ki_num", "ki_den", "deadband", "out_lo", "out_hi")


def _validate_piconfig(cfg: PIConfig) -> None:
    """Validate every PIConfig field is a plain int + the bound constraints. Called by the
    constructor AND re-run at use-time in pi_propose, so a config mutated AFTER construction (e.g.
    via `object.__setattr__`, which bypasses frozen-dataclass immutability) cannot smuggle a float
    into the math. (This defends post-construction mutation; a caller with arbitrary code execution
    can defeat any in-language guard and is out of scope by definition.)
    """
    for name in _PICONFIG_FIELDS:
        if not _is_int(getattr(cfg, name)):
            raise TypeError(f"PIConfig.{name} must be a plain int (no float/bool)")
    if cfg.kp_den <= 0 or cfg.ki_den <= 0:
        raise ValueError("PIConfig gain denominators must be > 0")
    if cfg.deadband < 0:
        raise ValueError("PIConfig.deadband must be >= 0")
    if cfg.out_lo > cfg.out_hi:
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
    _validate_piconfig(cfg)  # re-validate: a frozen cfg can be mutated post-construction
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
    # Materialize ONCE: a hostile iterable whose __iter__ yields clean ints on a validation pass
    # then floats on a use pass (TOCTOU) is defeated — we validate and compare the SAME captured
    # tuple, so __iter__ is called a single time.
    edges_t = tuple(edges)
    prev: int | None = None
    for e in edges_t:
        if not _is_int(e):
            raise TypeError("bin_index edges must be plain ints (no float/bool)")
        if prev is not None and e <= prev:
            raise ValueError("bin_index edges must be strictly ascending")
        prev = e
    idx = 0
    for e in edges_t:
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
    # Materialize ONCE (TOCTOU defense): a hostile iterable that yields clean ints during
    # validation then hostile __str__-overriding subclasses during the join is defeated — both
    # the check and the join run over the SAME captured tuple.
    bins_t = tuple(bins)
    for b in bins_t:
        if not _is_int(b):
            raise TypeError("state_key bins must be plain ints (no float/bool)")
    return ",".join(str(b) for b in bins_t)


def _validate_table(table: dict[str, int]) -> None:
    """Validate a frozen Q-table is a PLAIN dict of plain-`str` keys -> plain-`int` values.

    EXACT types, and the dict itself must not be a subclass: a `dict` subclass can override
    `__contains__`/`__getitem__` to lie about its contents, and a `str`-subclass key can serialise
    one way under `table_hash` (json) but compare equal to a DIFFERENT runtime lookup key — either
    makes the client-pinned hash disagree with what the lookup returns, breaking the frozen
    hash-pinned replay guarantee. This is called by BOTH `table_hash` and `q_table_propose`, so the
    pin and the lookup are provably over the same validated structure (or both fail closed).
    """
    if type(table) is not dict:
        raise TypeError("q-table must be a plain dict (no dict subclass)")
    for k, v in table.items():
        if type(k) is not str:
            raise TypeError("q-table keys must be plain str (no str subclass)")
        if not _is_int(v):
            raise TypeError(f"q-table value for {k!r} must be a plain int (no float/bool/str/int-subclass)")


def _table_digest(table: dict[str, int]) -> str:
    """Canonical SHA-256 of an ALREADY-VALIDATED table (no re-validation). Single source of truth
    for the digest, so `table_hash` and the `q_table_propose` use-boundary check agree by construction.
    """
    canonical = json.dumps(table, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def table_hash(table: dict[str, int]) -> str:
    """SHA-256 over the canonical (sorted-key) JSON of the frozen table — the pin a client checks.

    Validates the table first (same guard the lookup uses), so the hash a client pins cannot
    diverge from what `q_table_propose` would return for that table.
    """
    _validate_table(table)
    return _table_digest(table)


@dataclass(frozen=True)
class QResult:
    proposed: int
    state_key: str
    hit: bool  # False => bin missing => fail-closed default returned


def q_table_propose(
    bins: tuple[int, ...], table: dict[str, int], curr: int, *, expected_hash: str | None = None,
) -> QResult:
    """Look up the action for a binned state in a FROZEN table.

    Pure function: same bins + same table => same result (replay-stable). A missing bin is
    FAIL-CLOSED: returns `curr` (propose no change) rather than guessing. The table is validated as a
    plain dict of plain-str keys -> plain-int actions (same guard as `table_hash`, so the pin and the
    lookup agree). The returned value is still subject to the gate.

    `expected_hash` (the pin a client recorded for the frozen artifact) CLOSES the pin↔use gap: the
    table is a two-step, mutable-object protocol (hash at pin time, look up later), so a table mutated
    between the pin and this call would otherwise be silently used with a stale pin. When
    `expected_hash` is supplied, the digest is re-checked HERE, inside the use boundary, and a
    mismatch is a hard fail-closed error — the lookup acts only on the exact pinned artifact.

    The validation, digest check, and lookup all act on one private SNAPSHOT of the table taken
    before any caller-controlled code can run: `state_key(bins)` invokes the caller's `__iter__`,
    which could mutate the caller's (plain) dict after the digest check yet before the lookup —
    without the snapshot that returns a post-hash action under a stale pin.
    """
    if not _is_int(curr):
        raise TypeError("q_table_propose requires an integer (non-bool) curr")
    if type(table) is not dict:
        # rejected BEFORE the copy: dict(subclass) could launder lying keys()/items() into the snapshot
        raise TypeError("q-table must be a plain dict (no dict subclass)")
    snap = dict(table)  # the caller's object is never read again after this line
    _validate_table(snap)
    if expected_hash is not None:
        if type(expected_hash) is not str:
            raise TypeError("expected_hash must be a plain str")
        if _table_digest(snap) != expected_hash:
            raise ValueError("q-table hash mismatch: table is not the pinned artifact")
    key = state_key(bins)
    if key in snap:
        return QResult(proposed=snap[key], state_key=key, hit=True)  # action validated above
    return QResult(proposed=curr, state_key=key, hit=False)


# --------------------------------------------------------------------------- #
# Layered (hierarchical) frozen Q-tables (factored multi-factor; deterministic)
# --------------------------------------------------------------------------- #
# The architecture doc's "layered / factored tables" made concrete: a monolithic joint table over
# the product of every bin dimension blows up combinatorially; a 2-layer hierarchy needs only
# |regime table| + sum(|per-regime action tables|) entries. Layer 1 bins a slow/coarse signal
# (e.g. volatility regime) and selects a SUB-POLICY id; layer 2 bins the fast signals (e.g.
# utilization, peg deviation) inside the selected sub-policy and yields the action. The WHOLE
# layered structure is ONE hash-pinned artifact: swapping any layer is a governed action.

_LAYERED_TOP_KEYS = ("regime", "actions")


def _snapshot_layered_table(artifact: dict[str, object]) -> dict[str, object]:
    """Validate AND privately copy a layered-table artifact in ONE traversal (fail-closed).

    Returns fresh plain dicts built while exact-type-checking every level, so there is no
    validate-then-copy window at all: hostile code that later runs inside `state_key(bins)`
    (caller-controlled `__iter__`) can mutate the caller's object freely — the lookup and the
    digest only ever see this private snapshot. The artifact's exact shape:
    `{"regime": {state_key: regime_id}, "actions": {str(regime_id): {state_key: action}}}` with
    plain dict / plain-str / plain-int at every level (exact types; subclasses rejected — a dict
    subclass can lie via __getitem__/__contains__, a str-subclass key can json-serialise one way
    and compare another, either of which splits the pinned hash from the lookup). Top-level keys
    must be EXACTLY {"regime", "actions"}: an extra key would be unvalidated semantic surface
    that still changes the pinned hash.
    """
    if type(artifact) is not dict:
        raise TypeError("layered q-table artifact must be a plain dict (no dict subclass)")
    if set(artifact.keys()) != set(_LAYERED_TOP_KEYS):
        raise ValueError("layered q-table artifact must have exactly the keys {'regime', 'actions'}")
    regime = artifact["regime"]
    actions = artifact["actions"]
    if type(regime) is not dict:
        raise TypeError("layered q-table 'regime' must be a plain dict")
    if type(actions) is not dict:
        raise TypeError("layered q-table 'actions' must be a plain dict")
    regime_snap: dict[str, int] = {}
    for k, v in regime.items():
        if type(k) is not str:
            raise TypeError("layered q-table regime keys must be plain str (no str subclass)")
        if not _is_int(v):
            raise TypeError(f"layered q-table regime id for {k!r} must be a plain int")
        regime_snap[k] = v
    actions_snap: dict[str, dict[str, int]] = {}
    for rid, row in actions.items():
        if type(rid) is not str:
            raise TypeError("layered q-table action row ids must be plain str (no str subclass)")
        if type(row) is not dict:
            raise TypeError(f"layered q-table action row {rid!r} must be a plain dict")
        row_snap: dict[str, int] = {}
        for k, v in row.items():
            if type(k) is not str:
                raise TypeError(f"layered q-table action keys in row {rid!r} must be plain str")
            if not _is_int(v):
                raise TypeError(f"layered q-table action for {rid!r}[{k!r}] must be a plain int")
            row_snap[k] = v
        actions_snap[rid] = row_snap
    return {"regime": regime_snap, "actions": actions_snap}


def _layered_digest(snap: dict[str, object]) -> str:
    """Canonical SHA-256 of an ALREADY-SNAPSHOTTED layered artifact (sorted-key JSON)."""
    canonical = json.dumps(snap, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def layered_table_hash(artifact: dict[str, object]) -> str:
    """SHA-256 pin over the canonical JSON of the WHOLE layered artifact (both layers).

    Same guard as the lookup (`_snapshot_layered_table`), so the hash a client pins cannot
    diverge from what `layered_q_propose` would act on. One pin covers the regime table AND
    every per-regime action table: swapping any layer changes the pin.
    """
    return _layered_digest(_snapshot_layered_table(artifact))


@dataclass(frozen=True)
class LayeredQResult:
    proposed: int
    regime_key: str        # state_key(regime_bins)
    regime_id: int | None  # selected sub-policy id (None => regime bin missing)
    action_key: str        # state_key(action_bins)
    hit: bool              # False => some layer missed => fail-closed `curr` returned


def layered_q_propose(
    regime_bins: tuple[int, ...],
    action_bins: tuple[int, ...],
    artifact: dict[str, object],
    curr: int,
    *,
    expected_hash: str | None = None,
) -> LayeredQResult:
    """Two-layer frozen lookup: regime_bins -> regime_id -> that regime's action table -> action.

    Pure function (replay-stable): same bins + same artifact => same result. EVERY layer is
    fail-closed — a missing regime bin, a regime_id with no action row, or a missing action bin
    all return `curr` (propose no change) with hit=False; a dangling regime_id in the frozen
    artifact is therefore a runtime no-op, not an escape. The returned action is still subject
    to the gate (bounds + per-revision step + approval + timelock).

    `expected_hash` re-checks the client's pin INSIDE the use boundary (same rationale as
    `q_table_propose`). Validation, digest, and both lookups all act on one private snapshot
    taken before `state_key` runs any caller-controlled iteration, so a hostile `bins.__iter__`
    mutating the caller's artifact mid-call cannot influence the result.
    """
    if not _is_int(curr):
        raise TypeError("layered_q_propose requires an integer (non-bool) curr")
    snap = _snapshot_layered_table(artifact)  # caller's object is never read after this line
    if expected_hash is not None:
        if type(expected_hash) is not str:
            raise TypeError("expected_hash must be a plain str")
        if _layered_digest(snap) != expected_hash:
            raise ValueError("layered q-table hash mismatch: artifact is not the pinned one")
    regime_snap = snap["regime"]
    actions_snap = snap["actions"]
    assert type(regime_snap) is dict and type(actions_snap) is dict  # by construction of the snapshot
    regime_key = state_key(regime_bins)
    action_key = state_key(action_bins)
    if regime_key not in regime_snap:
        return LayeredQResult(curr, regime_key, None, action_key, hit=False)
    regime_id = regime_snap[regime_key]
    row = actions_snap.get(str(regime_id))
    if row is None or action_key not in row:
        return LayeredQResult(curr, regime_key, regime_id, action_key, hit=False)
    return LayeredQResult(row[action_key], regime_key, regime_id, action_key, hit=True)


# --------------------------------------------------------------------------- #
# Energy-based proposer (frozen integer energy model; argmin over the bounded band)
# --------------------------------------------------------------------------- #
# An energy-based reasoning model in its consensus-safe form: a FROZEN, hash-pinned integer
# energy function scores every candidate in the exactly-bounded revision band, and the proposer
# returns the argmin. E(c) = w_track*(c - target)^2 + w_move*|c - curr| makes the trade-off the
# model "reasons" about explicit: tracking error toward a per-state target vs. movement cost
# (parameter churn). The candidate set is the band the gate would admit ([curr-step, curr+step]
# clipped to [lo, hi]), so the proposer is in-envelope BY CONSTRUCTION — and the gate still
# independently verifies bounds, approval, and timelock (defense in depth).

_ENERGY_TOP_KEYS = ("targets", "w_track", "w_move")


def _snapshot_energy_model(artifact: dict[str, object]) -> dict[str, object]:
    """Validate AND privately copy an energy-model artifact in ONE traversal (fail-closed).

    Exact shape: `{"targets": {state_key: target_int}, "w_track": int >= 0, "w_move": int >= 0}`
    with exact plain types at every level (same hash<->lookup consistency rationale as the
    layered table). Both weights zero is a DEGENERATE model (every candidate ties at energy 0,
    so the argmin would silently drift to the band floor) — rejected at validation: fail-closed
    beats silent drift.
    """
    if type(artifact) is not dict:
        raise TypeError("energy model artifact must be a plain dict (no dict subclass)")
    if set(artifact.keys()) != set(_ENERGY_TOP_KEYS):
        raise ValueError("energy model artifact must have exactly the keys {'targets', 'w_track', 'w_move'}")
    targets = artifact["targets"]
    w_track = artifact["w_track"]
    w_move = artifact["w_move"]
    if type(targets) is not dict:
        raise TypeError("energy model 'targets' must be a plain dict")
    if not _is_int(w_track) or not _is_int(w_move):
        raise TypeError("energy model weights must be plain ints (no float/bool)")
    if w_track < 0 or w_move < 0:
        raise ValueError("energy model weights must be >= 0")
    if w_track == 0 and w_move == 0:
        raise ValueError("energy model is degenerate: w_track and w_move are both 0")
    targets_snap: dict[str, int] = {}
    for k, v in targets.items():
        if type(k) is not str:
            raise TypeError("energy model target keys must be plain str (no str subclass)")
        if not _is_int(v):
            raise TypeError(f"energy model target for {k!r} must be a plain int")
        targets_snap[k] = v
    return {"targets": targets_snap, "w_track": w_track, "w_move": w_move}


def _energy_digest(snap: dict[str, object]) -> str:
    """Canonical SHA-256 of an ALREADY-SNAPSHOTTED energy model (sorted-key JSON)."""
    canonical = json.dumps(snap, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def energy_model_hash(artifact: dict[str, object]) -> str:
    """SHA-256 pin over the canonical JSON of the WHOLE energy model (targets + weights)."""
    return _energy_digest(_snapshot_energy_model(artifact))


@dataclass(frozen=True)
class EnergyResult:
    proposed: int
    state_key: str
    target: int | None   # the frozen per-state target (None => state bin missing)
    energy: int | None   # E(proposed) (None => fail-closed no-op, nothing was scored)
    hit: bool            # False => missing target bin or empty band => `curr` returned


def energy_propose(
    bins: tuple[int, ...],
    artifact: dict[str, object],
    curr: int,
    *,
    lo: int,
    hi: int,
    step: int,
    expected_hash: str | None = None,
) -> EnergyResult:
    """Argmin of the frozen energy E(c) = w_track*(c-target)^2 + w_move*|c-curr| over the band.

    The band is [max(lo, curr-step), min(hi, curr+step)] — every candidate the gate's bounds+step
    could admit, and nothing else. Deterministic: pure integer energies, ties broken toward the
    SMALLEST candidate (a total order, so replay-stable). Fail-closed: a missing target bin or an
    empty band (curr stranded outside [lo, hi] beyond step) returns `curr` with hit=False.

    `expected_hash` re-checks the client's pin INSIDE the use boundary; validation, digest, and
    the argmin all act on one private snapshot taken before `state_key` runs caller-controlled
    iteration (same TOCTOU discipline as the table proposers). The proposal is still subject to
    the gate — in-envelope by construction does NOT skip approval/timelock/bounds verification.
    """
    if not (_is_int(curr) and _is_int(lo) and _is_int(hi) and _is_int(step)):
        raise TypeError("energy_propose requires integer (non-bool) curr/lo/hi/step")
    if step < 0:
        raise ValueError("energy_propose step must be >= 0")
    if lo > hi:
        raise ValueError("energy_propose requires lo <= hi")
    snap = _snapshot_energy_model(artifact)  # caller's object is never read after this line
    if expected_hash is not None:
        if type(expected_hash) is not str:
            raise TypeError("expected_hash must be a plain str")
        if _energy_digest(snap) != expected_hash:
            raise ValueError("energy model hash mismatch: artifact is not the pinned one")
    targets_snap = snap["targets"]
    assert type(targets_snap) is dict  # by construction of the snapshot
    w_track = snap["w_track"]
    w_move = snap["w_move"]
    assert type(w_track) is int and type(w_move) is int  # by construction of the snapshot
    key = state_key(bins)
    if key not in targets_snap:
        return EnergyResult(curr, key, None, None, hit=False)
    target = targets_snap[key]
    band_lo = max(lo, curr - step)
    band_hi = min(hi, curr + step)
    if band_lo > band_hi:
        return EnergyResult(curr, key, target, None, hit=False)  # empty band: curr stranded
    best_c: int | None = None
    best_e: int | None = None
    for c in range(band_lo, band_hi + 1):
        d = c - target
        m = c - curr if c >= curr else curr - c
        e = w_track * d * d + w_move * m
        if best_e is None or e < best_e:  # strict <: first (smallest) candidate wins ties
            best_c, best_e = c, e
    assert best_c is not None and best_e is not None  # band non-empty by the check above
    return EnergyResult(best_c, key, target, best_e, hit=True)
