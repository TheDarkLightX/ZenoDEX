"""Shared boundary scenarios binding the Tau specs and gov_gate.py (differential parity).

Single source of truth for `tests/tau_specs/governance/test_gov_parity.py`: each scenario is
evaluated BOTH against the Tau spec (ground `sat`) and against gov_gate.py, and both must equal
`expect`. This is the repo's dual-checker discipline applied to the two gate implementations —
neither is trusted over the other; they must agree on every shared case.

CASES: (surface, kwargs-for-the-python-gate, expected-admissibility).
SURFACE_TAU: per surface, the spec file, output bit, and how each kwarg maps onto a Tau input
             variable (kind, var). kind "sbf" => boolean (0/1), "bv" => bv[16] value.
"""
from __future__ import annotations

SURFACE_TAU = {
    "fee": ("gov_fee_revision_v1.tau", "o1", {
        "approved": ("sbf", "i1"), "exec_req": ("sbf", "i2"),
        "proposal_ts": ("bv", "i3"), "current_ts": ("bv", "i4"),
        "fee_curr_bps": ("bv", "i5"), "fee_next_bps": ("bv", "i6")}),
    "router_split": ("gov_router_split_revision_v1.tau", "o1", {
        "approved": ("sbf", "i1"), "exec_req": ("sbf", "i2"),
        "proposal_ts": ("bv", "i3"), "current_ts": ("bv", "i4"),
        "buyburn_next": ("bv", "i5"), "stakers_next": ("bv", "i6"),
        "reserve_next": ("bv", "i7"), "hosts_next": ("bv", "i8")}),
    # The router PER-SHARE step is the universal action_bound gate (see "action" below);
    # router_step_revision_ok is 4x action_bound, and the combined step is the master o6 bit.
    "funding": ("gov_funding_rate_revision_v1.tau", "o1", {
        "approved": ("sbf", "i1"), "exec_req": ("sbf", "i2"),
        "proposal_ts": ("bv", "i3"), "current_ts": ("bv", "i4"),
        "funding_cap_curr_bps": ("bv", "i5"), "funding_cap_next_bps": ("bv", "i6")}),
    "collateral": ("gov_collateral_ratio_revision_v1.tau", "o1", {
        "approved": ("sbf", "i1"), "exec_req": ("sbf", "i2"),
        "proposal_ts": ("bv", "i3"), "current_ts": ("bv", "i4"),
        "mcr_curr_bps": ("bv", "i5"), "mcr_next_bps": ("bv", "i6"),
        "ccr_curr_bps": ("bv", "i7"), "ccr_next_bps": ("bv", "i8")}),
    "whale": ("gov_whale_defense_revision_v1.tau", "o1", {
        "approved": ("sbf", "i1"), "exec_req": ("sbf", "i2"),
        "proposal_ts": ("bv", "i3"), "current_ts": ("bv", "i4"),
        "staker_bps_curr": ("bv", "i5"), "staker_bps_next": ("bv", "i6")}),
    "action": ("gov_action_bound_v1.tau", "o1", {
        "approved": ("sbf", "i1"), "exec_req": ("sbf", "i2"),
        "proposal_ts": ("bv", "i3"), "current_ts": ("bv", "i4"), "min_delay": ("bv", "i5"),
        "curr": ("bv", "i6"), "nxt": ("bv", "i7"),
        "lo": ("bv", "i8"), "hi": ("bv", "i9"), "step": ("bv", "i10")}),
}

# Python gate kwargs must match gov_gate.py signatures exactly.
CASES = [
    # --- fee ---
    ("fee", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=500, fee_next_bps=550), True),                       # valid (drift 50)
    ("fee", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=980, fee_next_bps=1000), True),                      # at cap, drift 20
    ("fee", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=500, fee_next_bps=1001), False),                     # above cap
    ("fee", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=0, fee_next_bps=200), False),                        # step over
    ("fee", dict(approved=False, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=500, fee_next_bps=550), False),                      # not approved
    ("fee", dict(approved=True, exec_req=True, proposal_ts=100, current_ts=110,
                 fee_curr_bps=500, fee_next_bps=500), False),                      # timelock (gap 10)
    ("fee", dict(approved=False, exec_req=False, proposal_ts=0, current_ts=0,
                 fee_curr_bps=500, fee_next_bps=9999), True),                      # exec_req escape
    # --- router SUM-BUDGET gate (4 next shares) ---
    ("router_split", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                          buyburn_next=6000, stakers_next=0, reserve_next=2000, hosts_next=2000), True),
    ("router_split", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                          buyburn_next=6000, stakers_next=1, reserve_next=2000, hosts_next=2000), False),  # sum 10001
    ("router_split", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                          buyburn_next=10001, stakers_next=0, reserve_next=0, hosts_next=0), False),  # share > 100%
    # router PER-SHARE step is action_bound (lo=0, hi=10000, step=500) — exercised in "action" below
    # --- funding rate cap ---
    ("funding", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                     funding_cap_curr_bps=100, funding_cap_next_bps=120), True),                 # drift 20
    ("funding", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                     funding_cap_curr_bps=100, funding_cap_next_bps=201), False),                # above cap 200
    ("funding", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                     funding_cap_curr_bps=0, funding_cap_next_bps=100), False),                  # drift 100 > 25
    # --- whale ---
    ("whale", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                   staker_bps_curr=6600, staker_bps_next=7000), True),             # at ceiling
    ("whale", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                   staker_bps_curr=5000, staker_bps_next=7001), False),            # over ceiling
    # --- action_bound (universal) ---
    ("action", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24, min_delay=24,
                    curr=500, nxt=550, lo=0, hi=1000, step=50), True),
    ("action", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24, min_delay=24,
                    curr=500, nxt=2000, lo=0, hi=1000, step=50), False),           # above max
    # action_bound used AS the router per-share step gate (lo=0, hi=10000, step=500):
    ("action", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24, min_delay=24,
                    curr=6000, nxt=6400, lo=0, hi=10000, step=500), True),         # share +400, ok
    ("action", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24, min_delay=24,
                    curr=6000, nxt=6600, lo=0, hi=10000, step=500), False),        # share drift 600 > 500
    # --- collateral (ordered; heavier ground tau) ---
    ("collateral", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                        mcr_curr_bps=11000, mcr_next_bps=11000, ccr_curr_bps=15000, ccr_next_bps=15000), True),
    ("collateral", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                        mcr_curr_bps=15000, mcr_next_bps=15000, ccr_curr_bps=11000, ccr_next_bps=11000), False),  # order
]
