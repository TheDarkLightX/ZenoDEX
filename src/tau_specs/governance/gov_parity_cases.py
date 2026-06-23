"""Shared boundary scenarios binding the Tau specs and gov_gate.py (differential parity).

Single source of truth for `tests/tau_specs/governance/test_gov_parity.py`: each scenario is
evaluated BOTH against the Tau spec (ground `sat`) and against gov_gate.py, and both must equal
`expect`. This is the repo's dual-checker discipline applied to the two gate implementations —
neither is trusted over the other; they must agree on every shared case.

CASES: (surface, kwargs-for-the-python-gate, expected-admissibility).
SURFACE_TAU: per surface, the spec file, output bit, and how each kwarg maps onto a Tau input
             variable (kind, var). kind "sbf" => boolean (0/1), "bv" => bv[16] value.
SIGNATURE_ORDER: positional argument order of each gate function — the contract the Rust
             kernel mirrors. The committed JSON fixture for the Rust side
             (tests/tau_specs/governance/fixtures/gov_gate_parity_cases.json) is generated
             from CASES via this table (gen_rust_parity_fixture.py) and byte-pinned by
             test_gov_parity.py, making this module the single source of truth for all
             THREE implementations (Tau / Python / Rust).
"""
from __future__ import annotations

SIGNATURE_ORDER = {
    "fee": ("approved", "exec_req", "proposal_ts", "current_ts",
            "fee_curr_bps", "fee_next_bps"),
    "router_split": ("approved", "exec_req", "proposal_ts", "current_ts",
                     "buyburn_next", "stakers_next", "reserve_next", "hosts_next"),
    "funding": ("approved", "exec_req", "proposal_ts", "current_ts",
                "funding_cap_curr_bps", "funding_cap_next_bps"),
    "collateral": ("approved", "exec_req", "proposal_ts", "current_ts",
                   "mcr_curr_bps", "mcr_next_bps", "ccr_curr_bps", "ccr_next_bps"),
    "whale": ("approved", "exec_req", "proposal_ts", "current_ts",
              "staker_bps_curr", "staker_bps_next"),
    "action": ("approved", "exec_req", "proposal_ts", "current_ts", "min_delay",
               "curr", "nxt", "lo", "hi", "step"),
    "drift": ("curr", "nxt", "used", "budget"),
    "cooldown": ("last_revision_epoch", "now_epoch", "cooldown"),
    "charter": ("revoked", "granted_epoch", "now_epoch", "ttl"),
    "epoch_budget": ("scalar_sum", "router_sum", "collateral_sum", "budget"),
}

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
    # --- trajectory tier (pure bits: no approval/exec/timelock inputs) ---
    "drift": ("gov_drift_budget_v1.tau", "o1", {
        "curr": ("bv", "i1"), "nxt": ("bv", "i2"),
        "used": ("bv", "i3"), "budget": ("bv", "i4")}),
    "cooldown": ("gov_cooldown_v1.tau", "o1", {
        "last_revision_epoch": ("bv", "i1"), "now_epoch": ("bv", "i2"),
        "cooldown": ("bv", "i3")}),
    "charter": ("gov_charter_v1.tau", "o1", {
        "revoked": ("sbf", "i1"), "granted_epoch": ("bv", "i2"),
        "now_epoch": ("bv", "i3"), "ttl": ("bv", "i4")}),
    "epoch_budget": ("gov_epoch_budget_v1.tau", "o1", {
        "scalar_sum": ("bv", "i1"), "router_sum": ("bv", "i2"),
        "collateral_sum": ("bv", "i3"), "budget": ("bv", "i4")}),
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
    # --- drift budget (trajectory window) ---
    ("drift", dict(curr=500, nxt=520, used=20, budget=150), True),          # delta 20 <= remaining 130
    ("drift", dict(curr=500, nxt=470, used=120, budget=150), True),         # delta 30 == remaining 30 (boundary)
    ("drift", dict(curr=500, nxt=520, used=140, budget=150), False),        # delta 20 > remaining 10
    ("drift", dict(curr=0, nxt=0, used=200, budget=150), False),            # used over budget (even for a no-move)
    ("drift", dict(curr=500, nxt=501, used=150, budget=150), False),        # exhausted budget blocks minimal move
    ("drift", dict(curr=65520, nxt=16, used=0, budget=50), False),          # large-magnitude move, wrap-safe
    # --- cooldown (spacing between applied revisions) ---
    ("cooldown", dict(last_revision_epoch=0, now_epoch=48, cooldown=48), True),    # boundary admit
    ("cooldown", dict(last_revision_epoch=100, now_epoch=110, cooldown=24), False),  # gap 10 < 24
    ("cooldown", dict(last_revision_epoch=65520, now_epoch=8, cooldown=24), False),  # wrap probe: now < last
    # --- charter (standing approval, dead-man) ---
    ("charter", dict(revoked=False, granted_epoch=0, now_epoch=10, ttl=24), True),     # inside ttl
    ("charter", dict(revoked=True, granted_epoch=0, now_epoch=10, ttl=24), False),     # revoked
    ("charter", dict(revoked=False, granted_epoch=0, now_epoch=24, ttl=24), False),    # expired at granted+ttl
    ("charter", dict(revoked=False, granted_epoch=0, now_epoch=10, ttl=4097), False),  # ttl over constitutional max
    ("charter", dict(revoked=False, granted_epoch=65520, now_epoch=8, ttl=4095), False),  # wrap probe: future grant
    ("charter", dict(revoked=False, granted_epoch=0, now_epoch=0, ttl=0), False),      # zero ttl dead at birth
    # --- epoch budget (aggregate movement per revision) ---
    ("epoch_budget", dict(scalar_sum=60, router_sum=400, collateral_sum=0, budget=600), True),
    ("epoch_budget", dict(scalar_sum=300, router_sum=300, collateral_sum=100, budget=600), False),  # 700 > 600
    ("epoch_budget", dict(scalar_sum=65535, router_sum=1, collateral_sum=0, budget=256), False),    # wrap probe
    # --- curr/next TRANSPOSITION KILLERS (T2 LOW): the step bound is symmetric, so a
    # swapped curr/next in any implementation passes symmetric cases; these pairs flip
    # their verdict under the swap because bounds/caps apply to NEXT only. One
    # True-case + its swapped False-case per curr/next surface family.
    ("fee", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=1005, fee_next_bps=1000), True),     # stepping back under the cap
    ("fee", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                 fee_curr_bps=1000, fee_next_bps=1005), False),    # swapped: next over cap
    ("funding", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                     funding_cap_curr_bps=210, funding_cap_next_bps=200), True),
    ("funding", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                     funding_cap_curr_bps=200, funding_cap_next_bps=210), False),
    ("whale", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                   staker_bps_curr=7100, staker_bps_next=7000), True),
    ("whale", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                   staker_bps_curr=7000, staker_bps_next=7100), False),
    ("collateral", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                        mcr_curr_bps=9500, mcr_next_bps=10400,
                        ccr_curr_bps=15000, ccr_next_bps=15000), True),   # mcr climbs over the floor
    ("collateral", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                        mcr_curr_bps=10400, mcr_next_bps=9500,
                        ccr_curr_bps=15000, ccr_next_bps=15000), False),  # swapped: next below floor
    ("collateral", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                        mcr_curr_bps=11000, mcr_next_bps=11000,
                        ccr_curr_bps=30500, ccr_next_bps=29800), True),   # ccr steps back under ceiling
    ("collateral", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24,
                        mcr_curr_bps=11000, mcr_next_bps=11000,
                        ccr_curr_bps=29800, ccr_next_bps=30500), False),  # swapped: next over ceiling
    ("action", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24, min_delay=24,
                    curr=10500, nxt=10000, lo=0, hi=10000, step=500), True),   # share steps back into band
    ("action", dict(approved=True, exec_req=True, proposal_ts=0, current_ts=24, min_delay=24,
                    curr=10000, nxt=10500, lo=0, hi=10000, step=500), False),  # swapped: next over hi
]
