"""Autonomous-governance EPOCH MACHINE for ZenoDEX (reference, advisory).

The missing tier between the pointwise gates and real autonomy. The pointwise suite
(gov_gate.py + gov_loop.py) bounds each revision to one `step` — but its trajectory
brake is per-revision approval. Real autonomy replaces that approval with a STANDING
grant, and the moment approval is standing, per-step safety is no longer trajectory
safety: a poisoned proposer could walk a parameter from min to max at one legal step
per revision. This machine adds the trajectory tier:

  * CHARTER   — the standing approval itself: a governed, revocable, EXPIRING grant
                (dead-man switch: no renewal => the lane halts to HOLD; fails closed).
                For the autonomous lane, `approved` IS charter validity at `now` —
                there is no per-revision human vote to substitute for it.
  * TIMELOCK  — pending revisions mature for MIN_DELAY epochs before they can apply
                (the existing wrap-safe subtraction-guard, re-checked by every gate).
  * VETO      — during that window a guardian can CANCEL the pending revision but can
                never propose or steer one (asymmetric authority: can stop, can't aim).
  * FREEZE    — a committed disaster flag halts the lane entirely (the decision to
                freeze comes from disaster tripwires upstream; this machine obeys it).
  * COOLDOWN  — minimum spacing between APPLIED revisions per surface (anti-thrash).
  * DRIFT BUDGET — per-surface |delta| budget per trajectory window: at most
                `DRIFT_BUDGET_BPS[s]` of movement per `DRIFT_WINDOW_EPOCHS`, however
                many individually-legal steps are proposed.
  * EPOCH BUDGET — aggregate |delta| budget across ALL surfaces per applied revision
                (a coordinated one-legal-step-everywhere regime walk must fit it).

Every transition is a total function `(state, inputs) -> (state', GovReceipt)` in the
CBC shape: validate before mutate, reject leaves params unchanged (receipts carry
canonical params digests so "no-op on reject" is checkable: digest_before ==
digest_after on every reject), stable reject codes with a FIXED precedence.

TRUST POSTURE: every gate this machine consults is IMPORT-BOUND at module load from
the sibling gov_gate / gov_loop modules (no caller-substitutable gate, no forged
wrapper — the r9 lesson: EVERY authority callable on the path, not just the obvious
ones). The proposer is untrusted; nothing it supplies can substitute for committed
state (`curr`, epochs, the drift accumulators) — those live in GovEpochState.

SCOPE / NON-CLAIMS: reference/simulation, NOT wired to live governance, NOT
consensus-critical. Binding `now_epoch`/state to attested committed chain state, and
enforcing that proposed actions are derivable from the chartered `policy_pin`, are the
open WS5 integration (the pin is stored and receipted here; action->pin enforcement
needs the live artifact registry). The constants (cooldown, window, budgets, TTL cap)
are constitution-tier REFERENCE values: changeable only by a version bump and review,
NEVER by the autonomous lane itself (no self-amendment — the lane must not be able to
widen its own cage).
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from typing import TypeGuard

import gov_gate   # noqa: E402  (flat sibling import; suite is used via sys.path, not a package)
import gov_loop   # noqa: E402

# --------------------------------------------------------------------------- #
# Import-bound authorities (r9 lesson: bind EVERY gate at module load).
# --------------------------------------------------------------------------- #
_MULTI_STEP = gov_loop.multi_surface_revision_step
_COOLDOWN_OK = gov_gate.cooldown_ok
_DRIFT_OK = gov_gate.drift_budget_ok
_CHARTER_OK = gov_gate.charter_ok
_EPOCH_BUDGET_OK = gov_gate.epoch_budget_ok

MIN_DELAY = gov_gate.MIN_DELAY
COOLDOWN_EPOCHS = gov_gate.GOV_COOLDOWN_EPOCHS
DRIFT_WINDOW = gov_gate.DRIFT_WINDOW_EPOCHS
EPOCH_BUDGET = gov_gate.EPOCH_MOVEMENT_BUDGET
CHARTER_TTL_MAX = gov_gate.CHARTER_TTL_MAX
DRIFT_BUDGETS = dict(gov_gate.DRIFT_BUDGET_BPS)  # private copy (the source is module state)

_U16_MAX = 0xFFFF

# Surface groups, redeclared locally and CHECKED against gov_loop at import (drift-proof
# without binding gov_loop privates).
_SCALAR_SURFACES = ("fee_bps", "funding_cap_bps", "redeem_staker_bps")
_ROUTER_SURFACES = ("buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps")
_COLLATERAL_SURFACES = ("mcr_bps", "ccr_bps")
ALL_SURFACES: tuple[str, ...] = _SCALAR_SURFACES + _ROUTER_SURFACES + _COLLATERAL_SURFACES
if set(ALL_SURFACES) != set(gov_loop.ALL_SURFACES):  # pragma: no cover - import-time tripwire
    raise RuntimeError("gov_epoch surface groups diverged from gov_loop.ALL_SURFACES")
if set(ALL_SURFACES) != set(DRIFT_BUDGETS):  # pragma: no cover - import-time tripwire
    raise RuntimeError("DRIFT_BUDGET_BPS does not cover exactly the loop surfaces")

# --------------------------------------------------------------------------- #
# Stable receipt codes (CBC discipline). Reject precedence in apply_pending is the
# documented order below; tests pin it.
# --------------------------------------------------------------------------- #
GOV_OK_PROPOSED = "gov_ok_proposed"
GOV_OK_APPLIED = "gov_ok_applied"
GOV_OK_VETOED = "gov_ok_vetoed"
GOV_OK_CHARTER_RENEWED = "gov_ok_charter_renewed"
GOV_OK_CHARTER_REVOKED = "gov_ok_charter_revoked"
GOV_OK_FROZEN_SET = "gov_ok_frozen_set"

GOV_REJ_NO_PENDING = "gov_rej_no_pending"
GOV_REJ_PENDING_EXISTS = "gov_rej_pending_exists"
GOV_REJ_EMPTY_ACTION = "gov_rej_empty_action"
GOV_REJ_FROZEN = "gov_rej_frozen"
GOV_REJ_CHARTER_INVALID = "gov_rej_charter_invalid"
GOV_REJ_TIMELOCK = "gov_rej_timelock"            # pending KEPT (not yet mature — wait)
GOV_REJ_COOLDOWN = "gov_rej_cooldown"            # pending cleared
GOV_REJ_SURFACE_GATE = "gov_rej_surface_gate"    # pending cleared
GOV_REJ_DRIFT_BUDGET = "gov_rej_drift_budget"    # pending cleared
GOV_REJ_EPOCH_BUDGET = "gov_rej_epoch_budget"    # pending cleared
GOV_REJ_NO_CHARTER = "gov_rej_no_charter"

# apply_pending evaluation order (FIRST failure wins; everything after is not consulted):
APPLY_PRECEDENCE: tuple[str, ...] = (
    GOV_REJ_NO_PENDING, GOV_REJ_FROZEN, GOV_REJ_CHARTER_INVALID, GOV_REJ_TIMELOCK,
    GOV_REJ_COOLDOWN, GOV_REJ_SURFACE_GATE, GOV_REJ_DRIFT_BUDGET, GOV_REJ_EPOCH_BUDGET,
)


def _is_plain_int(v: object) -> TypeGuard[int]:
    # EXACT type: bool and int subclasses are rejected everywhere (the round-3 lesson —
    # a hostile subclass overriding dunders must never reach arithmetic or a gate).
    return type(v) is int


def _is_u16(v: object) -> TypeGuard[int]:
    return _is_plain_int(v) and 0 <= v <= _U16_MAX


def _is_plain_str(v: object) -> TypeGuard[str]:
    return type(v) is str


_PIN_HEX = frozenset("0123456789abcdef")


def _is_pin(v: object) -> bool:
    """A policy pin is a lowercase sha256 hexdigest (the gov_proposers *_hash format)."""
    return _is_plain_str(v) and len(v) == 64 and set(v) <= _PIN_HEX


# --------------------------------------------------------------------------- #
# State (frozen dataclasses; canonical sorted-tuple maps so state is a VALUE).
# `frozen=True` is convenience, not a guarantee (object.__setattr__ bypasses it) —
# _validate_state re-validates EVERYTHING at every transition entry (use-time
# revalidation, the round-4 lesson).
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class Charter:
    """The autonomous lane's standing approval (revocable, expiring, policy-pinned)."""
    granted_epoch: int
    ttl: int
    revoked: bool
    policy_pin: str   # sha256 hex of the chartered policy artifact (audit/WS5 binding)


@dataclass(frozen=True)
class PendingRevision:
    """A proposed multi-surface action maturing in the timelock/veto window."""
    deltas: tuple[tuple[str, int], ...]   # canonical: sorted by surface, signed deltas
    proposed_epoch: int


@dataclass(frozen=True)
class SurfaceTraj:
    """Per-surface trajectory bookkeeping (committed alongside the params)."""
    last_revision_epoch: int
    window_start_epoch: int
    drift_used: int


@dataclass(frozen=True)
class GovEpochState:
    """The governed envelope's committed state: params + trajectory + authority flags."""
    params: tuple[tuple[str, int], ...]          # canonical sorted (surface, value)
    traj: tuple[tuple[str, SurfaceTraj], ...]    # canonical sorted (surface, traj)
    charter: Charter | None                      # None => autonomy disabled (fail-closed)
    frozen: bool
    pending: PendingRevision | None


@dataclass(frozen=True)
class GovReceipt:
    """Canonical outcome of one transition (stable code + params-digest no-op proof)."""
    code: str
    epoch: int
    surface: str | None        # first failing surface/group where applicable
    digest_before: str
    digest_after: str
    policy_pin: str | None     # the chartered pin in force (audit trail), if any


def params_digest(params: dict[str, int]) -> str:
    """Canonical SHA-256 of a validated params map: sha256(json(sorted pairs)).

    The receipt binds pre/post param state with this digest; it is also the
    cross-language golden-vector surface for the Rust port (byte-identical JSON:
    sorted keys, no whitespace).
    """
    snap = _snapshot_params(params, name="params")
    canonical = json.dumps(sorted(snap.items()), separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------- #
# Validation (raise on malformed/hostile; receipts are only for well-formed-but-
# inadmissible — the same boundary gov_loop draws).
# --------------------------------------------------------------------------- #
def _snapshot_params(m: object, *, name: str) -> dict[str, int]:
    """Validate AND privately copy a {surface: u16} map in one traversal (TOCTOU discipline)."""
    if type(m) is not dict:
        raise TypeError(f"{name} must be a plain dict (no dict subclass)")
    out: dict[str, int] = {}
    for k, v in m.items():
        if not _is_plain_str(k):
            raise TypeError(f"{name} keys must be plain str")
        if k not in ALL_SURFACES:
            raise ValueError(f"{name} contains an unknown surface: {k!r}")
        if not _is_u16(v):
            raise TypeError(f"{name}[{k!r}] must be a plain int in [0, 65535]")
        out[k] = v
    if set(out) != set(ALL_SURFACES):
        missing = sorted(set(ALL_SURFACES) - set(out))
        raise ValueError(f"{name} is missing surfaces: {missing}")
    return out


def _snapshot_deltas(m: object, *, name: str) -> dict[str, int]:
    """Validate AND privately copy a {surface: signed delta} map (may be any subset)."""
    if type(m) is not dict:
        raise TypeError(f"{name} must be a plain dict (no dict subclass)")
    out: dict[str, int] = {}
    for k, v in m.items():
        if not _is_plain_str(k):
            raise TypeError(f"{name} keys must be plain str")
        if k not in ALL_SURFACES:
            raise ValueError(f"{name} contains an unknown surface: {k!r}")
        if not _is_plain_int(v):
            raise TypeError(f"{name}[{k!r}] must be a plain int")
        if not -_U16_MAX <= v <= _U16_MAX:
            raise ValueError(f"{name}[{k!r}] magnitude exceeds the bv[16] domain")
        out[k] = v
    return out


def _validate_charter(c: object) -> None:
    if type(c) is not Charter:
        raise TypeError("charter must be a Charter (exact type)")
    if type(c.revoked) is not bool:
        raise TypeError("charter.revoked must be a real bool")
    if not (_is_u16(c.granted_epoch) and _is_u16(c.ttl)):
        raise TypeError("charter epochs/ttl must be plain ints in [0, 65535]")
    if not _is_pin(c.policy_pin):
        raise TypeError("charter.policy_pin must be a 64-char lowercase hex str")


def _validate_pending(p: object) -> None:
    if type(p) is not PendingRevision:
        raise TypeError("pending must be a PendingRevision (exact type)")
    if type(p.deltas) is not tuple or not p.deltas:
        raise TypeError("pending.deltas must be a non-empty tuple")
    seen: list[str] = []
    for item in p.deltas:
        if type(item) is not tuple or len(item) != 2:
            raise TypeError("pending.deltas items must be (surface, delta) tuples")
        k, v = item
        if not _is_plain_str(k) or k not in ALL_SURFACES:
            raise ValueError(f"pending.deltas has an unknown surface: {k!r}")
        if not _is_plain_int(v) or not -_U16_MAX <= v <= _U16_MAX:
            raise TypeError(f"pending.deltas[{k!r}] must be a plain int in the bv[16] band")
        seen.append(k)
    if seen != sorted(seen) or len(set(seen)) != len(seen):
        raise ValueError("pending.deltas must be sorted by surface with unique keys")
    if not _is_u16(p.proposed_epoch):
        raise TypeError("pending.proposed_epoch must be a plain int in [0, 65535]")


def _validate_state(s: object) -> None:
    """Re-validate the ENTIRE state object at use time (frozen != immutable)."""
    if type(s) is not GovEpochState:
        raise TypeError("state must be a GovEpochState (exact type)")
    for field_name, pairs in (("params", s.params), ("traj", s.traj)):
        if type(pairs) is not tuple:
            raise TypeError(f"state.{field_name} must be a tuple")
        keys = []
        for item in pairs:
            if type(item) is not tuple or len(item) != 2:
                raise TypeError(f"state.{field_name} items must be pairs")
            keys.append(item[0])
        if keys != sorted(keys) or set(keys) != set(ALL_SURFACES):
            raise ValueError(f"state.{field_name} must cover exactly the known surfaces, sorted")
    for k, v in s.params:
        if not _is_plain_str(k) or not _is_u16(v):
            raise TypeError("state.params entries must be (plain str, plain u16 int)")
    for k, t in s.traj:
        if not _is_plain_str(k) or type(t) is not SurfaceTraj:
            raise TypeError("state.traj entries must be (plain str, SurfaceTraj)")
        if not (_is_u16(t.last_revision_epoch) and _is_u16(t.window_start_epoch)
                and _is_u16(t.drift_used)):
            raise TypeError("SurfaceTraj fields must be plain ints in [0, 65535]")
    if s.charter is not None:
        _validate_charter(s.charter)
    if type(s.frozen) is not bool:
        raise TypeError("state.frozen must be a real bool")
    if s.pending is not None:
        _validate_pending(s.pending)


def _params_dict(s: GovEpochState) -> dict[str, int]:
    return {k: v for k, v in s.params}


def _traj_dict(s: GovEpochState) -> dict[str, SurfaceTraj]:
    return {k: t for k, t in s.traj}


def _canon_params(d: dict[str, int]) -> tuple[tuple[str, int], ...]:
    return tuple(sorted(d.items()))


def _canon_traj(d: dict[str, SurfaceTraj]) -> tuple[tuple[str, SurfaceTraj], ...]:
    return tuple(sorted(d.items()))


def genesis_state(params: dict[str, int], *, epoch: int = 0) -> GovEpochState:
    """Build the canonical genesis state. Autonomy starts DISABLED (charter=None):
    the lane cannot act until a charter is granted — fail-closed by default. Trajectory
    windows and cooldowns start at `epoch` (the first revision must clear a full
    cooldown from genesis — a deliberate warm-up, not a bug)."""
    if not _is_u16(epoch):
        raise TypeError("epoch must be a plain int in [0, 65535]")
    snap = _snapshot_params(params, name="params")
    traj = {s: SurfaceTraj(epoch, epoch, 0) for s in ALL_SURFACES}
    return GovEpochState(
        params=_canon_params(snap), traj=_canon_traj(traj),
        charter=None, frozen=False, pending=None,
    )


# --------------------------------------------------------------------------- #
# Receipt helper
# --------------------------------------------------------------------------- #
def _receipt(code: str, epoch: int, before: str, after: str,
             *, surface: str | None = None, pin: str | None = None) -> GovReceipt:
    return GovReceipt(code, epoch, surface, before, after, pin)


def _charter_valid(s: GovEpochState, now_epoch: int) -> bool:
    c = s.charter
    if c is None:
        return False
    verdict = _CHARTER_OK(c.revoked, c.granted_epoch, now_epoch, c.ttl)
    if type(verdict) is not bool:  # fail-closed: malformed gate verdicts are never "admit"
        raise TypeError("charter gate must return a real bool")
    return verdict


# --------------------------------------------------------------------------- #
# Transitions (each: validate -> decide -> build candidate -> commit/no-op).
# --------------------------------------------------------------------------- #
def propose_revision(
    state: GovEpochState, deltas: dict[str, int], *, now_epoch: int,
) -> tuple[GovEpochState, GovReceipt]:
    """Queue a multi-surface action (factory shape {surface: signed delta}) for the
    timelock/veto window. Requires: not frozen, no pending already, a valid charter at
    `now_epoch`, and a non-empty well-formed action. The action is validated EAGERLY so
    nothing malformed can ever sit in `pending`."""
    _validate_state(state)
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    dl = _snapshot_deltas(deltas, name="deltas")
    dg = params_digest(_params_dict(state))
    pin = state.charter.policy_pin if state.charter is not None else None
    if state.frozen:
        return state, _receipt(GOV_REJ_FROZEN, now_epoch, dg, dg, pin=pin)
    if state.pending is not None:
        return state, _receipt(GOV_REJ_PENDING_EXISTS, now_epoch, dg, dg, pin=pin)
    if not _charter_valid(state, now_epoch):
        return state, _receipt(GOV_REJ_CHARTER_INVALID, now_epoch, dg, dg, pin=pin)
    if not dl:
        return state, _receipt(GOV_REJ_EMPTY_ACTION, now_epoch, dg, dg, pin=pin)
    pending = PendingRevision(deltas=tuple(sorted(dl.items())), proposed_epoch=now_epoch)
    new = replace(state, pending=pending)
    return new, _receipt(GOV_OK_PROPOSED, now_epoch, dg, dg, pin=pin)


def veto_pending(
    state: GovEpochState, *, now_epoch: int,
) -> tuple[GovEpochState, GovReceipt]:
    """Guardian cancel: removes the pending revision. Deliberately works REGARDLESS of
    frozen/charter state — stopping is always safe, so the stop authority is never
    gated. The guardian cannot propose or modify, only cancel (asymmetric authority)."""
    _validate_state(state)
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    dg = params_digest(_params_dict(state))
    pin = state.charter.policy_pin if state.charter is not None else None
    if state.pending is None:
        return state, _receipt(GOV_REJ_NO_PENDING, now_epoch, dg, dg, pin=pin)
    new = replace(state, pending=None)
    return new, _receipt(GOV_OK_VETOED, now_epoch, dg, dg, pin=pin)


def apply_pending(
    state: GovEpochState, *, now_epoch: int,
) -> tuple[GovEpochState, GovReceipt]:
    """Apply the matured pending revision through EVERY gate tier, all-or-nothing.

    Evaluation order (FIRST failure wins — see APPLY_PRECEDENCE):
      1. no pending          -> gov_rej_no_pending   (nothing to apply)
      2. frozen              -> gov_rej_frozen        (pending CLEARED)
      3. charter invalid     -> gov_rej_charter_invalid (pending CLEARED; dead-man)
      4. timelock immature   -> gov_rej_timelock      (pending KEPT — wait, retry later)
      5. cooldown (per touched surface, ALL_SURFACES order) -> gov_rej_cooldown (CLEARED)
      6. pointwise gates     -> gov_rej_surface_gate  (CLEARED; first failing surface)
      7. drift budget (per touched surface, window-rolled) -> gov_rej_drift_budget (CLEARED)
      8. epoch budget (aggregate) -> gov_rej_epoch_budget (CLEARED)
      9. all pass -> params applied, trajectories updated, pending cleared.

    The autonomous lane's `approved` flag IS charter validity (checked at step 3): once
    the charter holds, the pointwise gates are consulted with approved=True — there is
    no per-revision human vote in this lane, which is exactly why steps 5-8 exist.
    Params NEVER change on any reject (digest_before == digest_after on the receipt)."""
    _validate_state(state)
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    params = _params_dict(state)
    dg = params_digest(params)
    pin = state.charter.policy_pin if state.charter is not None else None

    def _rej_keep(code: str, surface: str | None = None) -> tuple[GovEpochState, GovReceipt]:
        return state, _receipt(code, now_epoch, dg, dg, surface=surface, pin=pin)

    def _rej_clear(code: str, surface: str | None = None) -> tuple[GovEpochState, GovReceipt]:
        new = state if state.pending is None else replace(state, pending=None)
        return new, _receipt(code, now_epoch, dg, dg, surface=surface, pin=pin)

    if state.pending is None:
        return _rej_keep(GOV_REJ_NO_PENDING)
    if state.frozen:
        return _rej_clear(GOV_REJ_FROZEN)
    if not _charter_valid(state, now_epoch):
        return _rej_clear(GOV_REJ_CHARTER_INVALID)
    pending = state.pending
    if not _COOLDOWN_OK(pending.proposed_epoch, now_epoch, MIN_DELAY):
        return _rej_keep(GOV_REJ_TIMELOCK)

    deltas = {k: v for k, v in pending.deltas}
    traj = _traj_dict(state)
    touched = tuple(s for s in ALL_SURFACES if s in deltas)
    for s in touched:
        if not _COOLDOWN_OK(traj[s].last_revision_epoch, now_epoch, COOLDOWN_EPOCHS):
            return _rej_clear(GOV_REJ_COOLDOWN, s)

    decision = _MULTI_STEP(
        params, deltas,
        approved=True,  # charter validity established above IS the lane's approval
        proposal_ts=pending.proposed_epoch, current_ts=now_epoch,
    )
    if type(decision.admitted) is not bool:
        raise TypeError("multi-surface step must return a real-bool verdict")
    if not decision.admitted:
        return _rej_clear(GOV_REJ_SURFACE_GATE, decision.rejected_surface)

    # Window-rolled drift budgets per touched surface (deterministic roll at use; the
    # roll itself commits only on apply). A window_start "in the future" (hostile or
    # inconsistent state) never rolls — drift_used keeps counting: fail-closed.
    rolled: dict[str, SurfaceTraj] = {}
    for s in touched:
        t = traj[s]
        fresh_window = (now_epoch >= t.window_start_epoch
                        and now_epoch - t.window_start_epoch >= DRIFT_WINDOW)
        used = 0 if fresh_window else t.drift_used
        start = now_epoch if fresh_window else t.window_start_epoch
        nxt = params[s] + deltas[s]
        verdict = _DRIFT_OK(params[s], nxt, used, DRIFT_BUDGETS[s])
        if type(verdict) is not bool:
            raise TypeError("drift gate must return a real bool")
        if not verdict:
            return _rej_clear(GOV_REJ_DRIFT_BUDGET, s)
        rolled[s] = SurfaceTraj(now_epoch, start, used + abs(deltas[s]))

    scalar_sum = sum(abs(deltas[s]) for s in _SCALAR_SURFACES if s in deltas)
    router_sum = sum(abs(deltas[s]) for s in _ROUTER_SURFACES if s in deltas)
    collateral_sum = sum(abs(deltas[s]) for s in _COLLATERAL_SURFACES if s in deltas)
    budget_verdict = _EPOCH_BUDGET_OK(scalar_sum, router_sum, collateral_sum, EPOCH_BUDGET)
    if type(budget_verdict) is not bool:
        raise TypeError("epoch-budget gate must return a real bool")
    if not budget_verdict:
        return _rej_clear(GOV_REJ_EPOCH_BUDGET)

    new_params = dict(decision.applied)
    for s in touched:
        traj[s] = rolled[s]
    new = GovEpochState(
        params=_canon_params(new_params), traj=_canon_traj(traj),
        charter=state.charter, frozen=state.frozen, pending=None,
    )
    return new, _receipt(GOV_OK_APPLIED, now_epoch, dg, params_digest(new_params), pin=pin)


def renew_charter(
    state: GovEpochState, *, now_epoch: int, ttl: int, policy_pin: str,
) -> tuple[GovEpochState, GovReceipt]:
    """HUMAN/governed action (not reachable by the autonomous lane): grant or renew the
    standing approval. ttl must be in [1, CHARTER_TTL_MAX] — no perpetual charter; a
    malformed grant raises (fail loud, it is an admin action). Renewal while frozen is
    allowed (it moves no parameter)."""
    _validate_state(state)
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    if not _is_plain_int(ttl):
        raise TypeError("ttl must be a plain int")
    if not 1 <= ttl <= CHARTER_TTL_MAX:
        raise ValueError(f"ttl must be in [1, {CHARTER_TTL_MAX}] (no perpetual charter)")
    if not _is_pin(policy_pin):
        raise TypeError("policy_pin must be a 64-char lowercase hex str")
    dg = params_digest(_params_dict(state))
    charter = Charter(granted_epoch=now_epoch, ttl=ttl, revoked=False, policy_pin=policy_pin)
    new = replace(state, charter=charter)
    return new, _receipt(GOV_OK_CHARTER_RENEWED, now_epoch, dg, dg, pin=policy_pin)


def revoke_charter(
    state: GovEpochState, *, now_epoch: int,
) -> tuple[GovEpochState, GovReceipt]:
    """Guardian/governed action: kill the standing approval immediately (idempotent).
    Like veto, revocation is never gated — stopping is always safe."""
    _validate_state(state)
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    dg = params_digest(_params_dict(state))
    if state.charter is None:
        return state, _receipt(GOV_REJ_NO_CHARTER, now_epoch, dg, dg)
    if state.charter.revoked:
        return state, _receipt(GOV_OK_CHARTER_REVOKED, now_epoch, dg, dg,
                               pin=state.charter.policy_pin)
    new = replace(state, charter=replace(state.charter, revoked=True))
    return new, _receipt(GOV_OK_CHARTER_REVOKED, now_epoch, dg, dg,
                         pin=state.charter.policy_pin)


def set_frozen(
    state: GovEpochState, flag: bool, *, now_epoch: int,
) -> tuple[GovEpochState, GovReceipt]:
    """Disaster interlock input: a committed tripwire (oracle divergence, depeg, vault
    floor, ...) freezes the lane; this machine OBEYS the flag, it does not decide it.
    Freezing does not drop a pending revision by itself — but a frozen apply rejects
    AND clears it (see apply_pending), and veto remains available while frozen."""
    _validate_state(state)
    if type(flag) is not bool:
        raise TypeError("flag must be a real bool")
    if not _is_u16(now_epoch):
        raise TypeError("now_epoch must be a plain int in [0, 65535]")
    dg = params_digest(_params_dict(state))
    pin = state.charter.policy_pin if state.charter is not None else None
    new = state if state.frozen == flag else replace(state, frozen=flag)
    return new, _receipt(GOV_OK_FROZEN_SET, now_epoch, dg, dg, pin=pin)
