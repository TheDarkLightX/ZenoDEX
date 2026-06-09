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

This loop is for single-scalar surfaces (fee / whale-defense / funding-cap — the gov_gate gates with
the `(approved, exec_req, proposal_ts, current_ts, curr, next)` shape). Multi-value surfaces (router
split, MCR/CCR) compose differently and are out of scope here.

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
    return isinstance(v, int) and not isinstance(v, bool)


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
