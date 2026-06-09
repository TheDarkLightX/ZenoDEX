"""Reference evaluator for the ZenoDEX governance pointwise-revision gates.

This is the Python ("computes") side of the repo's hybrid model; the `gov_*_v1.tau`
specs are the Tau ("validates") side. Both encode the SAME Boolean gate. The Tau spec
is verified by `validate_governance_specs.py` (compile + non-vacuity + per-guardrail
teeth); this module is the runtime a proposer-agnostic governance shell would call to
decide whether a *proposed* revision is admissible.

PROPOSER-AGNOSTIC: the proposer (a staker vote, a PID controller, or a frozen
Q-learning lookup table) computes `next`; these gates decide admissibility. A
mis-trained / poisoned / oracle-manipulated proposer can never escape the bounded
envelope — the worst it does is move a parameter by `step` per revision inside
[min, max]. The bound is the safety, not trust in the proposer.

Domain discipline (fail-closed): the Tau core operates on bv[16] (modular, unsigned).
This shell HARD-REJECTS any input outside [0, 0xFFFF] rather than silently wrapping it
— stricter than the core, never weaker, so the composed (shell + core) decision is
fail-closed. Guardrail constants are IMMUTABLE here: they are part of the gate, not a
revisable parameter, and can change only by a spec-version bump.
"""
from __future__ import annotations

from dataclasses import dataclass

U16_MAX = 0xFFFF


def _in_domain(*vals: int) -> bool:
    """Fail-closed domain guard: every value must be a bv[16]-representable PLAIN int.

    EXACT type (`type(v) is int`), not `isinstance`: the latter admits bool and any `int`
    subclass. A hostile subclass overriding `__le__`/`__sub__` could otherwise pass this guard
    and the bound/step comparisons, admitting an out-of-cap revision. Exact-type matches the
    `type(f) is bool` discipline used for flags below.
    """
    return all(type(v) is int and 0 <= v <= U16_MAX for v in vals)


def _flags_ok(*flags: bool) -> bool:
    """Fail-closed flag guard: every control flag must be a REAL bool (not 2, None, "yes", ...).

    The gate semantics use boolean truthiness (`if not exec_req`, `approved and ...`); a non-bool
    flag from decoded input would otherwise leak through truthiness (e.g. `approved=2` is truthy,
    `exec_req=None` takes the escape path). Rejecting non-bools keeps the shell strictly fail-closed.
    """
    return all(type(f) is bool for f in flags)


def _timelock_ok(proposal_ts: int, current_ts: int, min_delay: int) -> bool:
    """Wrap-safe timelock: current >= proposal AND current - proposal >= min_delay.

    Mirrors the spec's subtraction-guard form (NOT `current >= proposal + min_delay`,
    which is bypassable when proposal_ts + min_delay wraps past 2^16).
    """
    return current_ts >= proposal_ts and (current_ts - proposal_ts) >= min_delay


def _step_ok(curr: int, nxt: int, step: int) -> bool:
    """Bounded drift: |next - curr| <= step (wrap-safe; both sides nonneg in-domain)."""
    return abs(curr - nxt) <= step


# --------------------------------------------------------------------------- #
# Universal gate (mirrors gov_action_bound_v1.tau). Bounds are arguments.
# --------------------------------------------------------------------------- #
def action_bound_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int, min_delay: int,
    curr: int, nxt: int, lo: int, hi: int, step: int,
) -> bool:
    """Admissible iff: execution not requested, OR (approved AND past timelock AND
    next in [lo, hi] AND |next - curr| <= step). Proposer-agnostic."""
    if not _flags_ok(approved, exec_req):
        return False
    if not _in_domain(proposal_ts, current_ts, min_delay, curr, nxt, lo, hi, step):
        return False
    if not exec_req:
        return True
    return (
        approved
        and _timelock_ok(proposal_ts, current_ts, min_delay)
        and lo <= nxt <= hi
        and _step_ok(curr, nxt, step)
    )


# --------------------------------------------------------------------------- #
# IMMUTABLE per-surface guardrails (match the concrete .tau specs exactly).
# --------------------------------------------------------------------------- #
MIN_DELAY = 24  # { #x0018 } timelock units, shared

FEE_MAX_BPS = 1000   # { #x03E8 } 10% hard cap
FEE_STEP_BPS = 50    # { #x0032 } 0.5% max drift / revision

SPLIT_SHARE_MAX = 10000  # { #x2710 } each share <= 100%
SPLIT_SUM = 10000        # { #x2710 } shares must total exactly 100%
SPLIT_STEP_BPS = 500     # { #x01F4 } 5pp max per-share drift / revision

RATIO_MIN_BPS = 10000  # { #x2710 } 100% collateral floor
RATIO_MAX_BPS = 30000  # { #x7530 } 300% ceiling
RATIO_STEP_BPS = 1000  # { #x03E8 } 10pp max drift / revision

FUNDING_CAP_MAX_BPS = 200  # { #x00C8 } 2%/epoch hard cap on the funding clamp
FUNDING_STEP_BPS = 25      # { #x0019 } 0.25%/epoch max drift / revision

WHALE_STAKER_BPS_MAX = 7000  # { #x1B58 } whale-defense ceiling
WHALE_STEP_BPS = 500         # { #x01F4 } 5pp max drift / revision


def fee_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    fee_curr_bps: int, fee_next_bps: int,
) -> bool:
    """Swap-fee revision (factored bounds + step)."""
    return action_bound_ok(
        approved, exec_req, proposal_ts, current_ts, MIN_DELAY,
        fee_curr_bps, fee_next_bps, 0, FEE_MAX_BPS, FEE_STEP_BPS,
    )


def router_split_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    buyburn_next: int, stakers_next: int, reserve_next: int, hosts_next: int,
) -> bool:
    """Fee-router split SUM-BUDGET gate (mirrors gov_router_split: shares total exactly 100%).

    The per-share anti-whiplash drift is the separate `router_step_revision_ok` gate; a router
    revision is admissible iff BOTH accept (see `router_revision_ok`)."""
    nexts = (buyburn_next, stakers_next, reserve_next, hosts_next)
    if not _flags_ok(approved, exec_req):
        return False
    if not _in_domain(proposal_ts, current_ts, *nexts):
        return False
    if not exec_req:
        return True
    return (
        approved
        and _timelock_ok(proposal_ts, current_ts, MIN_DELAY)
        and all(s <= SPLIT_SHARE_MAX for s in nexts)
        and sum(nexts) == SPLIT_SUM
    )


def router_step_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    buyburn_next: int, stakers_next: int, reserve_next: int, hosts_next: int,
    buyburn_curr: int, stakers_curr: int, reserve_curr: int, hosts_curr: int,
) -> bool:
    """Fee-router per-share DRIFT gate. Each share's step IS the universal `action_bound` gate
    (lo=0, hi=SPLIT_SHARE_MAX, step=SPLIT_STEP_BPS) applied to that share — so a router revision
    is admissible iff `router_split` (sum-budget) AND `action_bound` per share both accept.
    Verified two tractable ways: each share via `gov_action_bound` (the universal gate), and the
    combined 4-step as the master `o6` bit. (A standalone 4-step Tau spec normalizes in ~180s on
    the current build, so it is not kept — the step is the universal gate applied per-share.)"""
    pairs = ((buyburn_curr, buyburn_next), (stakers_curr, stakers_next),
             (reserve_curr, reserve_next), (hosts_curr, hosts_next))
    return all(
        action_bound_ok(approved, exec_req, proposal_ts, current_ts, MIN_DELAY,
                        c, n, 0, SPLIT_SHARE_MAX, SPLIT_STEP_BPS)
        for c, n in pairs
    )


def router_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    buyburn_next: int, stakers_next: int, reserve_next: int, hosts_next: int,
    buyburn_curr: int, stakers_curr: int, reserve_curr: int, hosts_curr: int,
) -> bool:
    """Composed router gate: admissible iff the sum-budget AND the per-share step both accept."""
    return router_split_revision_ok(
        approved, exec_req, proposal_ts, current_ts,
        buyburn_next, stakers_next, reserve_next, hosts_next,
    ) and router_step_revision_ok(
        approved, exec_req, proposal_ts, current_ts,
        buyburn_next, stakers_next, reserve_next, hosts_next,
        buyburn_curr, stakers_curr, reserve_curr, hosts_curr,
    )


def collateral_ratio_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    mcr_curr_bps: int, mcr_next_bps: int, ccr_curr_bps: int, ccr_next_bps: int,
) -> bool:
    """zUSD MCR/CCR revision (ordered: mcr_next <= ccr_next; bounds; step)."""
    if not _flags_ok(approved, exec_req):
        return False
    if not _in_domain(proposal_ts, current_ts, mcr_curr_bps, mcr_next_bps, ccr_curr_bps, ccr_next_bps):
        return False
    if not exec_req:
        return True
    return (
        approved
        and _timelock_ok(proposal_ts, current_ts, MIN_DELAY)
        and mcr_next_bps >= RATIO_MIN_BPS
        and ccr_next_bps <= RATIO_MAX_BPS
        and mcr_next_bps <= ccr_next_bps
        and _step_ok(mcr_curr_bps, mcr_next_bps, RATIO_STEP_BPS)
        and _step_ok(ccr_curr_bps, ccr_next_bps, RATIO_STEP_BPS)
    )


def whale_defense_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    staker_bps_curr: int, staker_bps_next: int,
) -> bool:
    """redeem.staker_bps whale-defense revision (factored ceiling + step)."""
    return action_bound_ok(
        approved, exec_req, proposal_ts, current_ts, MIN_DELAY,
        staker_bps_curr, staker_bps_next, 0, WHALE_STAKER_BPS_MAX, WHALE_STEP_BPS,
    )


def funding_rate_revision_ok(
    approved: bool, exec_req: bool, proposal_ts: int, current_ts: int,
    funding_cap_curr_bps: int, funding_cap_next_bps: int,
) -> bool:
    """Perps funding-rate-cap revision (factored bounds + step)."""
    return action_bound_ok(
        approved, exec_req, proposal_ts, current_ts, MIN_DELAY,
        funding_cap_curr_bps, funding_cap_next_bps, 0, FUNDING_CAP_MAX_BPS, FUNDING_STEP_BPS,
    )


@dataclass(frozen=True)
class MasterRevision:
    """A composite revision across the four economic-core surfaces."""
    approved: bool
    exec_req: bool
    proposal_ts: int
    current_ts: int
    fee_curr_bps: int
    fee_next_bps: int
    buyburn_next_bps: int
    stakers_next_bps: int
    reserve_next_bps: int
    hosts_next_bps: int
    buyburn_curr_bps: int
    stakers_curr_bps: int
    reserve_curr_bps: int
    hosts_curr_bps: int
    mcr_curr_bps: int
    mcr_next_bps: int
    ccr_curr_bps: int
    ccr_next_bps: int
    staker_bps_curr: int
    staker_bps_next: int


def master_revision_ok(r: MasterRevision) -> bool:
    """Composite gate (mirrors gov_revision_master_v1.tau): factored AND of every
    per-surface guardrail under the shared approval + timelock gate.

    Fail-closed: every numeric field is domain-validated FIRST (before the exec_req
    escape and the timelock), so an out-of-domain timestamp/value can never slip through
    on Python's non-wrapping ints. Each surface guardrail is then evaluated with exec_req
    forced True so the composite reflects the surface's bound regardless of the top-level
    exec flag; the shared gate (approval + timelock + exec_req escape) is applied once.

    Requires the EXACT `MasterRevision` type: a duck-typed object with property-backed fields could
    return `exec_req=True` during the flag check and `False` at the escape branch (a TOCTOU on
    attribute reads). A real frozen dataclass returns the same stored value on every access, so
    requiring the exact type makes the multiple reads of each field consistent.
    """
    if type(r) is not MasterRevision:
        raise TypeError("master_revision_ok requires a MasterRevision (exact type)")
    if not _flags_ok(r.approved, r.exec_req):
        return False
    if not _in_domain(
        r.proposal_ts, r.current_ts, r.fee_curr_bps, r.fee_next_bps,
        r.buyburn_next_bps, r.stakers_next_bps, r.reserve_next_bps, r.hosts_next_bps,
        r.buyburn_curr_bps, r.stakers_curr_bps, r.reserve_curr_bps, r.hosts_curr_bps,
        r.mcr_curr_bps, r.mcr_next_bps, r.ccr_curr_bps, r.ccr_next_bps,
        r.staker_bps_curr, r.staker_bps_next,
    ):
        return False
    if not r.exec_req:
        return True
    if not (r.approved and _timelock_ok(r.proposal_ts, r.current_ts, MIN_DELAY)):
        return False
    fee_ok = fee_revision_ok(True, True, 0, MIN_DELAY, r.fee_curr_bps, r.fee_next_bps)
    router_ok = router_revision_ok(
        True, True, 0, MIN_DELAY,
        r.buyburn_next_bps, r.stakers_next_bps, r.reserve_next_bps, r.hosts_next_bps,
        r.buyburn_curr_bps, r.stakers_curr_bps, r.reserve_curr_bps, r.hosts_curr_bps)
    collateral_ok = collateral_ratio_revision_ok(
        True, True, 0, MIN_DELAY, r.mcr_curr_bps, r.mcr_next_bps, r.ccr_curr_bps, r.ccr_next_bps)
    whale_ok = whale_defense_revision_ok(
        True, True, 0, MIN_DELAY, r.staker_bps_curr, r.staker_bps_next)
    return fee_ok and router_ok and collateral_ok and whale_ok
