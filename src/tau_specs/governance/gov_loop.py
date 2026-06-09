"""Autonomous-governance revision LOOP for ZenoDEX (reference, advisory).

Composes a PROPOSER's candidate (gov_proposers.py) with the verified GATE (gov_gate.py): the gate
decides admissibility, and on rejection the loop is a NO-OP (the committed value is unchanged).

TWO ENFORCED PRECONDITIONS for the safety property to hold:

1. EXECUTION MODE. The loop binds `exec_req=True` ITSELF when calling the gate. The gov_gate gates
   short-circuit to "admit" on `exec_req=False` (that branch means "no execution requested, nothing
   to check"); a caller who passed a gate pre-bound with `exec_req=False` would bypass the bounds.
   By owning the flag, the loop makes that bypass unreachable — the gate's bounds always apply.

2. THE BINDING (WS2 non-trust clause). The gate's `curr` is `committed_curr` — supplied by THIS loop
   from authenticated committed state — NOT any value the proposer claims. The proposer is untrusted;
   it cannot spoof `curr` to dress an arbitrary jump up as a one-step move. The spec bounds the delta;
   the loop owns the anchor. (Sourcing `committed_curr`, the epochs, and the `approved` flag from real
   on-chain governance state is the open WS5 integration; this module models that contract.)

`autonomous_revision_step` is the single-scalar loop (fee / whale-defense / funding-cap — the
gov_gate gates with the `(approved, exec_req, proposal_ts, current_ts, curr, next)` shape).
`multi_surface_revision_step` (below) is the all-or-nothing MULTI-surface loop: it gates an
action shaped like the policy-factory artifact's (`{surface_name: signed_delta}` over fee /
funding / whale / the 4 router shares / the MCR-CCR pair), admitting only if EVERY touched
surface's gate accepts — the router shares and the collateral pair are each gated as a unit.

SCOPE / NON-CLAIMS: reference/simulation, NOT wired to live governance, NOT consensus-critical. The
gate is the only authority; this loop just sequences proposer -> gate -> (apply | no-op) + receipt.

TRUST BOUNDARY (gate selection): `gate` must be a raw, trusted gov_gate gate. The loop binds
`exec_req=True` and `curr=committed_curr` on the callable it is GIVEN and requires a real-bool
verdict; it cannot defend against a forged wrapper that ignores those arguments and answers
admit. Owning the gate choice (e.g. a whitelist of gov_gate functions) belongs to the WS5
integration layer, exactly like sourcing `committed_curr` and `approved` from committed state.
"""
from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

# A gov_gate single-scalar gate: (approved, exec_req, proposal_ts, current_ts, curr, next) -> ok?
# e.g. gov_gate.fee_revision_ok / whale_defense_revision_ok / funding_rate_revision_ok.
SurfaceGate = Callable[[bool, bool, int, int, int, int], bool]


def _is_int(v: object) -> bool:
    # EXACT type (not isinstance): a hostile `int` subclass reaching committed_curr/proposed_next
    # could otherwise pass both this check and the gate's domain check and be admitted out-of-cap.
    return type(v) is int


@dataclass(frozen=True)
class RevisionDecision:
    """Deterministic outcome of one autonomous revision step."""
    admitted: bool
    committed_curr: int   # the authenticated anchor the gate was evaluated against
    proposed: int         # what the (untrusted) proposer asked for
    applied: int          # committed_curr if rejected (no-op), else proposed
    reason: str           # "admitted" | "rejected_by_gate"


def autonomous_revision_step(
    committed_curr: int, proposed_next: int, gate: SurfaceGate,
    *, approved: bool, proposal_ts: int, current_ts: int,
) -> RevisionDecision:
    """Run one revision through `gate`, with `exec_req=True` and `curr=committed_curr` bound here.

    `gate` is a raw gov_gate single-scalar gate; this function calls it as
    `gate(approved, True, proposal_ts, current_ts, committed_curr, proposed_next)` — the caller can
    NOT set `exec_req` (it is always True) and can NOT substitute the proposer's `curr` for the
    committed one. `approved` is the real governance-approval flag (must be a bool). Fail-closed:
    anything the gate does not admit leaves the parameter unchanged.
    """
    if not (_is_int(committed_curr) and _is_int(proposed_next)
            and _is_int(proposal_ts) and _is_int(current_ts)):
        raise TypeError("committed_curr/proposed_next/proposal_ts/current_ts must be ints (non-bool)")
    if type(approved) is not bool:
        raise TypeError("approved must be a real bool")
    verdict = gate(approved, True, proposal_ts, current_ts, committed_curr, proposed_next)
    if type(verdict) is not bool:
        # fail-closed: a gate that does not return a real bool is malformed — refuse to interpret
        # a truthy object (e.g. a mock, an int) as "admitted".
        raise TypeError("gate must return a real bool")
    admitted = verdict
    if admitted:
        return RevisionDecision(True, committed_curr, proposed_next, proposed_next, "admitted")
    return RevisionDecision(False, committed_curr, proposed_next, committed_curr, "rejected_by_gate")


# --------------------------------------------------------------------------- #
# Multi-surface revision step (all-or-nothing across every touched surface)
# --------------------------------------------------------------------------- #
# Autonomous policies act on SEVERAL parameters at once (e.g. the policy-factory artifact's
# actions: {"fee_bps": +10, "funding_cap_bps": -5} or a buyburn<->reserve router shift). The
# single-scalar step above cannot gate those. This step takes a committed anchor for EVERY
# surface plus a DELTA map (the factory action shape, keyed by surface name) and admits the
# revision only if EVERY touched surface's verified gate accepts — any rejection leaves ALL
# parameters unchanged (no partial application).
#
# TRUST POSTURE (stronger than the single-scalar step): the gates are imported directly from
# the sibling gov_gate module rather than accepted as caller arguments, so there is no forged-
# wrapper surface at all; exec_req=True and curr=committed are bound here, exactly as above.

import gov_gate  # noqa: E402  (flat sibling import; this suite is used via sys.path, not as a package)

_SCALAR_SURFACES: dict[str, "SurfaceGate"] = {
    "fee_bps": gov_gate.fee_revision_ok,
    "funding_cap_bps": gov_gate.funding_rate_revision_ok,
    "redeem_staker_bps": gov_gate.whale_defense_revision_ok,
}
_ROUTER_SURFACES = ("buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps")
_COLLATERAL_SURFACES = ("mcr_bps", "ccr_bps")
ALL_SURFACES: tuple[str, ...] = (
    tuple(_SCALAR_SURFACES) + _ROUTER_SURFACES + _COLLATERAL_SURFACES
)


def _snapshot_surface_ints(
    m: object, *, name: str, require_all: bool,
) -> dict[str, int]:
    """Validate AND privately copy a {surface_name: int} mapping in one traversal (fail-closed).

    Exact plain dict / plain-str keys / plain-int values; every key must be a KNOWN surface (an
    action touching a surface this loop cannot gate must hard-reject, never silently pass). With
    require_all, every surface must be present (the committed anchor covers the whole envelope).
    The caller's object is never read after this returns (TOCTOU discipline).
    """
    if type(m) is not dict:
        raise TypeError(f"{name} must be a plain dict (no dict subclass)")
    out: dict[str, int] = {}
    for k, v in m.items():
        if type(k) is not str:
            raise TypeError(f"{name} keys must be plain str (no str subclass)")
        if k not in ALL_SURFACES:
            raise ValueError(f"{name} contains an unknown surface: {k!r}")
        if not _is_int(v):
            raise TypeError(f"{name}[{k!r}] must be a plain int (no float/bool)")
        out[k] = v
    if require_all and set(out) != set(ALL_SURFACES):
        missing = sorted(set(ALL_SURFACES) - set(out))
        raise ValueError(f"{name} is missing surfaces: {missing}")
    return out


def _require_bool_verdict(verdict: object) -> bool:
    # Same fail-closed rule as the single-scalar step. The gates here are our own module's, but
    # this also locks future gov_gate edits to the real-bool contract.
    if type(verdict) is not bool:
        raise TypeError("gate must return a real bool")
    return verdict


@dataclass(frozen=True)
class MultiSurfaceDecision:
    """Deterministic outcome of one all-or-nothing multi-surface revision."""
    admitted: bool
    committed: dict[str, int]        # the authenticated anchors (every surface)
    deltas: dict[str, int]           # the validated proposal (touched surfaces only)
    applied: dict[str, int]          # committed if rejected; committed+deltas where touched if admitted
    rejected_surface: str | None     # first failing surface/group in evaluation order, else None
    reason: str                      # "admitted" | "admitted_hold" | "rejected_by_gate:<surface>"


def multi_surface_revision_step(
    committed: dict[str, int], deltas: dict[str, int],
    *, approved: bool, proposal_ts: int, current_ts: int,
) -> MultiSurfaceDecision:
    """Gate a multi-surface action (factory shape: {surface: signed delta}) all-or-nothing.

    Evaluation order is fixed and deterministic: fee_bps -> funding_cap_bps -> redeem_staker_bps
    -> router group -> collateral group; the FIRST failing surface rejects the WHOLE revision and
    every parameter stays at its committed value. The router shares are gated as a UNIT (sum
    budget + per-share step) whenever any share is touched, with untouched shares anchored at
    their committed values; the MCR/CCR pair likewise. An empty delta map is a hold: admitted as
    a no-op without consulting any gate (there is nothing to authorize — nothing changes).

    `exec_req=True` and `curr=committed` are bound HERE (the proposer cannot supply either), and
    the gates are the sibling gov_gate module's directly — not caller-substitutable.
    """
    if not (_is_int(proposal_ts) and _is_int(current_ts)):
        raise TypeError("proposal_ts/current_ts must be ints (non-bool)")
    if type(approved) is not bool:
        raise TypeError("approved must be a real bool")
    comm = _snapshot_surface_ints(committed, name="committed", require_all=True)
    dl = _snapshot_surface_ints(deltas, name="deltas", require_all=False)
    if not dl:
        return MultiSurfaceDecision(True, comm, dl, dict(comm), None, "admitted_hold")

    def _reject(surface: str) -> MultiSurfaceDecision:
        return MultiSurfaceDecision(
            False, comm, dl, dict(comm), surface, f"rejected_by_gate:{surface}",
        )

    for surface, gate in _SCALAR_SURFACES.items():
        if surface in dl:
            ok = _require_bool_verdict(gate(
                approved, True, proposal_ts, current_ts, comm[surface], comm[surface] + dl[surface],
            ))
            if not ok:
                return _reject(surface)
    if any(s in dl for s in _ROUTER_SURFACES):
        nexts = tuple(comm[s] + dl.get(s, 0) for s in _ROUTER_SURFACES)
        currs = tuple(comm[s] for s in _ROUTER_SURFACES)
        ok = _require_bool_verdict(gov_gate.router_revision_ok(
            approved, True, proposal_ts, current_ts, *nexts, *currs,
        ))
        if not ok:
            return _reject("router")
    if any(s in dl for s in _COLLATERAL_SURFACES):
        mcr_next = comm["mcr_bps"] + dl.get("mcr_bps", 0)
        ccr_next = comm["ccr_bps"] + dl.get("ccr_bps", 0)
        ok = _require_bool_verdict(gov_gate.collateral_ratio_revision_ok(
            approved, True, proposal_ts, current_ts,
            comm["mcr_bps"], mcr_next, comm["ccr_bps"], ccr_next,
        ))
        if not ok:
            return _reject("collateral")
    applied = {s: comm[s] + dl.get(s, 0) for s in ALL_SURFACES}
    return MultiSurfaceDecision(True, comm, dl, applied, None, "admitted")
