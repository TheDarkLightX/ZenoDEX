"""Teeth tests for the governance pointwise-revision reference gates (gov_gate.py).

Mirrors the Tau teeth proven by validate_governance_specs.py: every gate ADMITS a
concrete valid revision and REJECTS each immutable-guardrail violation, the exec_req=0
escape is honored, out-of-domain inputs are hard-rejected, and the timelock is wrap-safe.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

_SPEC = Path(__file__).resolve().parents[3] / "src" / "tau_specs" / "governance" / "gov_gate.py"
_spec = importlib.util.spec_from_file_location("gov_gate", _SPEC)
assert _spec and _spec.loader
gov_gate = importlib.util.module_from_spec(_spec)
sys.modules["gov_gate"] = gov_gate  # register so @dataclass can introspect __module__
_spec.loader.exec_module(gov_gate)

MD = gov_gate.MIN_DELAY  # 24


# --------------------------------------------------------------------------- #
# action_bound (universal gate)
# --------------------------------------------------------------------------- #
def test_action_bound_admits_valid():
    # min_delay=24, curr=500, next=550, [0,1000], step=50, gap 24
    assert gov_gate.action_bound_ok(True, True, 0, MD, MD, 500, 550, 0, 1000, 50)


def test_action_bound_rejects_above_max():
    assert not gov_gate.action_bound_ok(True, True, 0, MD, MD, 500, 2000, 0, 1000, 50)


def test_action_bound_rejects_below_min():
    assert not gov_gate.action_bound_ok(True, True, 0, MD, MD, 100, 10, 100, 1000, 50)


def test_action_bound_rejects_step_exceeded():
    assert not gov_gate.action_bound_ok(True, True, 0, MD, MD, 0, 200, 0, 1000, 50)


def test_action_bound_rejects_not_approved():
    assert not gov_gate.action_bound_ok(False, True, 0, MD, MD, 500, 550, 0, 1000, 50)


def test_action_bound_exec_req_false_is_escape():
    # exec not requested -> admissible regardless of an otherwise-bad value
    assert gov_gate.action_bound_ok(False, False, 0, 0, MD, 500, 9999, 0, 1000, 50)


def test_action_bound_rejects_out_of_domain():
    assert not gov_gate.action_bound_ok(True, True, 0, MD, MD, 500, 70000, 0, 1000, 50)
    assert not gov_gate.action_bound_ok(True, True, 0, MD, MD, 500, -1, 0, 1000, 50)


def test_action_bound_rejects_bool_as_int_domain():
    # bool is a subclass of int; must be rejected as a non-domain value
    assert not gov_gate.action_bound_ok(True, True, 0, MD, MD, True, 550, 0, 1000, 50)  # type: ignore[arg-type]


# --- strict flag domain (Codex re-review MED: fail-closed on non-bool approved/exec_req) ---
def test_action_bound_rejects_non_bool_approved():
    # approved=2 is truthy but not a real bool -> must be rejected (fail-closed)
    assert not gov_gate.action_bound_ok(2, True, 0, MD, MD, 500, 550, 0, 1000, 50)  # type: ignore[arg-type]


def test_action_bound_rejects_non_bool_exec_req():
    # exec_req=None must NOT take the escape path; must reject
    assert not gov_gate.action_bound_ok(True, None, 0, MD, MD, 500, 9999, 0, 1000, 50)  # type: ignore[arg-type]


def test_router_split_rejects_non_bool_flag():
    assert not gov_gate.router_split_revision_ok(2, True, 0, MD, 6000, 0, 2000, 2000)  # type: ignore[arg-type]


def test_collateral_rejects_non_bool_flag():
    assert not gov_gate.collateral_ratio_revision_ok(True, None, 0, MD, 11000, 11000, 15000, 15000)  # type: ignore[arg-type]


# --------------------------------------------------------------------------- #
# timelock wrap-safety (the bug the harness probe found)
# --------------------------------------------------------------------------- #
def test_timelock_honest_gap_admits():
    assert gov_gate.fee_revision_ok(True, True, 100, 140, 500, 500)  # gap 40 >= 24


def test_timelock_too_soon_rejects():
    assert not gov_gate.fee_revision_ok(True, True, 100, 110, 500, 500)  # gap 10 < 24


def test_timelock_wrap_bypass_rejected():
    # proposal near 2^16: naive `current >= proposal + delay` would wrap and admit;
    # the subtraction-guard form rejects (current < proposal).
    assert not gov_gate.fee_revision_ok(True, True, 0xFFF8, 0x0010, 500, 500)


# --------------------------------------------------------------------------- #
# fee revision
# --------------------------------------------------------------------------- #
def test_fee_admits_valid():
    assert gov_gate.fee_revision_ok(True, True, 0, MD, 500, 550)  # drift 50 == step


def test_fee_rejects_above_cap():
    assert not gov_gate.fee_revision_ok(True, True, 0, MD, 500, 1001)


def test_fee_rejects_step_over():
    assert not gov_gate.fee_revision_ok(True, True, 0, MD, 0, 200)  # drift 200 > 50


def test_fee_at_cap_with_small_step_admits():
    assert gov_gate.fee_revision_ok(True, True, 0, MD, 980, 1000)  # at cap, drift 20


# --------------------------------------------------------------------------- #
# router SUM-BUDGET gate (4 next shares)
# --------------------------------------------------------------------------- #
def test_router_split_admits_mvp_default():
    # 6000/0/2000/2000 = 10000 (MVP default per memory)
    assert gov_gate.router_split_revision_ok(True, True, 0, MD, 6000, 0, 2000, 2000)


def test_router_split_rejects_sum_below():
    assert not gov_gate.router_split_revision_ok(True, True, 0, MD, 0, 0, 0, 0)


def test_router_split_rejects_sum_above():
    assert not gov_gate.router_split_revision_ok(True, True, 0, MD, 10000, 10000, 0, 0)


def test_router_split_rejects_share_over_100pct():
    assert not gov_gate.router_split_revision_ok(True, True, 0, MD, 10001, 0, 0, 0)


def test_router_split_rejects_sum_off_by_one():
    assert not gov_gate.router_split_revision_ok(True, True, 0, MD, 6000, 1, 2000, 2000)  # = 10001


# --------------------------------------------------------------------------- #
# router PER-SHARE STEP gate (4 next + 4 curr)
# --------------------------------------------------------------------------- #
def test_router_step_admits_no_change():
    assert gov_gate.router_step_revision_ok(True, True, 0, MD, 6000, 0, 2000, 2000, 6000, 0, 2000, 2000)


def test_router_step_admits_bounded_reallocation():
    # buyburn +400, hosts -400: each per-share drift <= 500
    assert gov_gate.router_step_revision_ok(True, True, 0, MD, 6400, 0, 2000, 1600, 6000, 0, 2000, 2000)


def test_router_step_rejects_step_over():
    # buyburn 6000 -> 6600 (drift 600 > 500)
    assert not gov_gate.router_step_revision_ok(True, True, 0, MD, 6600, 0, 2000, 1400, 6000, 0, 2000, 2000)


# --------------------------------------------------------------------------- #
# composed router gate (sum-budget AND per-share step both required)
# --------------------------------------------------------------------------- #
def test_router_composed_admits_valid():
    assert gov_gate.router_revision_ok(True, True, 0, MD, 6400, 0, 2000, 1600, 6000, 0, 2000, 2000)


def test_router_composed_rejects_bad_sum():
    # drift ok but sum 10001
    assert not gov_gate.router_revision_ok(True, True, 0, MD, 6001, 0, 2000, 2000, 6000, 0, 2000, 2000)


def test_router_composed_rejects_bad_step():
    # sum ok (10000) but buyburn drift 600 > 500
    assert not gov_gate.router_revision_ok(True, True, 0, MD, 6600, 0, 2000, 1400, 6000, 0, 2000, 2000)


# --------------------------------------------------------------------------- #
# collateral ratio (ordered)
# --------------------------------------------------------------------------- #
def test_collateral_admits_valid():
    assert gov_gate.collateral_ratio_revision_ok(True, True, 0, MD, 11000, 11000, 15000, 15000)


def test_collateral_rejects_mcr_below_floor():
    assert not gov_gate.collateral_ratio_revision_ok(True, True, 0, MD, 11000, 9999, 15000, 15000)


def test_collateral_rejects_ccr_above_ceiling():
    assert not gov_gate.collateral_ratio_revision_ok(True, True, 0, MD, 11000, 11000, 30001, 30001)


def test_collateral_rejects_mcr_exceeds_ccr():
    # both in-bounds but order violated (mcr_next 15000 > ccr_next 11000)
    assert not gov_gate.collateral_ratio_revision_ok(True, True, 0, MD, 15000, 15000, 11000, 11000)


def test_collateral_rejects_mcr_step_over():
    # mcr 11000 -> 20000 drift 9000 > 1000 (ccr held at 20000 so order ok)
    assert not gov_gate.collateral_ratio_revision_ok(True, True, 0, MD, 11000, 20000, 20000, 20000)


# --------------------------------------------------------------------------- #
# whale defense
# --------------------------------------------------------------------------- #
def test_whale_admits_valid():
    assert gov_gate.whale_defense_revision_ok(True, True, 0, MD, 5000, 5000)


def test_whale_rejects_above_ceiling():
    assert not gov_gate.whale_defense_revision_ok(True, True, 0, MD, 5000, 7001)


def test_whale_at_ceiling_admits():
    assert gov_gate.whale_defense_revision_ok(True, True, 0, MD, 6600, 7000)  # at ceiling, drift 400


def test_whale_rejects_step_over():
    assert not gov_gate.whale_defense_revision_ok(True, True, 0, MD, 0, 2000)  # drift 2000 > 500


# --------------------------------------------------------------------------- #
# funding rate cap
# --------------------------------------------------------------------------- #
def test_funding_admits_valid():
    assert gov_gate.funding_rate_revision_ok(True, True, 0, MD, 100, 120)  # drift 20 <= 25


def test_funding_rejects_above_cap():
    assert not gov_gate.funding_rate_revision_ok(True, True, 0, MD, 100, 201)


def test_funding_at_cap_admits():
    assert gov_gate.funding_rate_revision_ok(True, True, 0, MD, 180, 200)  # at cap, drift 20


def test_funding_rejects_step_over():
    assert not gov_gate.funding_rate_revision_ok(True, True, 0, MD, 0, 100)  # drift 100 > 25


# --------------------------------------------------------------------------- #
# master composite
# --------------------------------------------------------------------------- #
def _valid_master(**overrides) -> "gov_gate.MasterRevision":
    base = dict(
        approved=True, exec_req=True, proposal_ts=0, current_ts=MD,
        fee_curr_bps=500, fee_next_bps=500,
        buyburn_next_bps=6000, stakers_next_bps=0, reserve_next_bps=2000, hosts_next_bps=2000,
        buyburn_curr_bps=6000, stakers_curr_bps=0, reserve_curr_bps=2000, hosts_curr_bps=2000,
        mcr_curr_bps=11000, mcr_next_bps=11000, ccr_curr_bps=15000, ccr_next_bps=15000,
        staker_bps_curr=5000, staker_bps_next=5000,
    )
    base.update(overrides)
    return gov_gate.MasterRevision(**base)


def test_master_admits_all_valid():
    assert gov_gate.master_revision_ok(_valid_master())


@pytest.mark.parametrize("override", [
    {"fee_next_bps": 1001},                                                  # fee cap
    {"buyburn_next_bps": 0, "stakers_next_bps": 0, "reserve_next_bps": 0, "hosts_next_bps": 0},  # router sum
    {"buyburn_next_bps": 6600, "hosts_next_bps": 1400},                      # router per-share step (drift 600)
    {"mcr_next_bps": 15000, "ccr_next_bps": 11000},                          # collateral order violated
    {"ccr_curr_bps": 29900, "ccr_next_bps": 30001},                          # ccr ceiling (drift 101 ok, ceiling not)
    {"staker_bps_next": 7001},                                               # whale ceiling
    {"approved": False},                                                     # not approved
    {"proposal_ts": 100, "current_ts": 110},                                 # timelock gap 10 < 24
])
def test_master_rejects_any_bad_surface(override):
    assert not gov_gate.master_revision_ok(_valid_master(**override))


def test_master_exec_req_false_is_escape():
    assert gov_gate.master_revision_ok(_valid_master(exec_req=False, fee_next_bps=9999))


# --- master fail-closed domain (Codex HIGH: validate every field before exec/timelock) ---
def test_master_rejects_out_of_domain_timestamp():
    # current_ts 0x10012 = 65554 > 0xFFFF: must hard-reject (the reproduced Codex finding)
    assert not gov_gate.master_revision_ok(_valid_master(proposal_ts=0xFFFA, current_ts=0x10012))


def test_master_rejects_out_of_domain_value():
    assert not gov_gate.master_revision_ok(_valid_master(fee_next_bps=70000))


def test_master_out_of_domain_rejected_even_on_exec_escape():
    # stricter-than-Tau shell: out-of-domain is rejected even when execution is not requested
    assert not gov_gate.master_revision_ok(_valid_master(exec_req=False, current_ts=70000))


def test_master_rejects_non_bool_flags():
    assert not gov_gate.master_revision_ok(_valid_master(approved=2))      # type: ignore[arg-type]
    assert not gov_gate.master_revision_ok(_valid_master(exec_req=None))   # type: ignore[arg-type]


def test_master_rejects_duck_typed_revision():
    # (Codex round-5) a duck-typed object with a property-backed exec_req that returns True during
    # the flag check then False at the escape branch (TOCTOU on attribute reads) used to be admitted
    # for otherwise-bad in-domain fields. master_revision_ok now requires the exact MasterRevision
    # type, so attribute reads come from consistent stored fields, not a lying property.
    class FlipExec:
        def __init__(self):
            self._n = 0

        def __getattr__(self, name):
            if name == "exec_req":
                self._n += 1
                return True if self._n == 1 else False  # flips between the two reads
            if name == "approved":
                return True
            return 0  # all numeric fields in-domain

    with pytest.raises(TypeError):
        gov_gate.master_revision_ok(FlipExec())
