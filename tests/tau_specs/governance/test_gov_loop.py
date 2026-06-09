"""Tests for the autonomous-governance loop (gov_loop.py) composed with the VERIFIED gate.

The headline results are empirical, not asserted:
  * a poisoned / saturated proposer is BOUNDED by the gate (the loop is a no-op on rejection);
  * the loop FORCES execution mode (exec_req=True), so the gate's bounds always apply — a value that
    the gate would "admit" under exec_req=False is still rejected by the loop;
  * the proposer cannot spoof `curr` — the loop evaluates the gate against committed state;
  * a well-tuned velocity-form PI converges toward its setpoint while every step stays inside the gate.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

_GOV = Path(__file__).resolve().parents[3] / "src" / "tau_specs" / "governance"
sys.path.insert(0, str(_GOV))

import gov_gate  # noqa: E402
import gov_loop  # noqa: E402
import gov_proposers as gp  # noqa: E402

FEE = gov_gate.fee_revision_ok          # raw gov_gate single-scalar gate
MD = gov_gate.MIN_DELAY


def _step(curr, nxt, **over):
    kw = dict(approved=True, proposal_ts=0, current_ts=MD)
    kw.update(over)
    return gov_loop.autonomous_revision_step(curr, nxt, FEE, **kw)


# --------------------------------------------------------------------------- #
# basic composition
# --------------------------------------------------------------------------- #
def test_loop_admits_in_bound():
    d = _step(500, 520)  # drift 20 <= step 50, <= cap 1000
    assert d.admitted and d.applied == 520


def test_loop_rejects_out_of_step_is_noop():
    d = _step(500, 600)  # drift 100 > step 50
    assert not d.admitted and d.applied == 500 and d.reason == "rejected_by_gate"


def test_loop_rejects_above_cap_is_noop():
    d = _step(980, 1100)  # > 1000 cap
    assert not d.admitted and d.applied == 980


def test_loop_rejects_unapproved():
    d = _step(500, 520, approved=False)  # governance did not approve
    assert not d.admitted and d.applied == 500


# --------------------------------------------------------------------------- #
# the loop FORCES execution mode (Codex HIGH: a raw gate is unsafe if bound exec_req=False)
# --------------------------------------------------------------------------- #
def test_loop_forces_execution_mode():
    # Under exec_req=False the gate short-circuits to admit (nothing to execute):
    assert gov_gate.fee_revision_ok(True, False, 0, MD, 500, 9000) is True
    # ...but the loop binds exec_req=True itself, so the same out-of-bound jump is REJECTED:
    d = _step(500, 9000)
    assert not d.admitted and d.applied == 500


# --------------------------------------------------------------------------- #
# THE safety property: a bad proposer is bounded by the gate
# --------------------------------------------------------------------------- #
def test_gate_bounds_poisoned_pi_proposer():
    # a poisoned/saturated PI proposes a huge jump; the gate refuses; the param is unchanged.
    cfg = gp.PIConfig(setpoint=1000, kp_num=1000, kp_den=1, ki_num=0, ki_den=1,
                      deadband=0, out_lo=0, out_hi=60000)
    poison = gp.pi_propose(500, 60000, 0, cfg)  # enormous error * huge gain -> clamps to out_hi
    assert poison.proposed >= 9000
    d = _step(500, poison.proposed)
    assert not d.admitted and d.applied == 500  # bounded: no-op, fee stays at 500


def test_gate_bounds_poisoned_qtable_entry():
    q = gp.q_table_propose((2, 2), {"2,2": 9000}, curr=500)  # poisoned table entry
    assert q.proposed == 9000
    d = _step(500, q.proposed)
    assert not d.admitted and d.applied == 500


def test_binding_proposer_cannot_spoof_curr():
    # The proposer may *believe* curr is 9000 and propose 9020 (a 20-drift in ITS frame), but the
    # loop evaluates the gate against the COMMITTED curr (500) -> a huge jump -> rejected.
    d = _step(500, 9020)
    assert not d.admitted and d.committed_curr == 500 and d.applied == 500


# --------------------------------------------------------------------------- #
# a well-tuned velocity-form PI converges while every step stays inside the gate
# --------------------------------------------------------------------------- #
def test_pi_converges_under_gate():
    # Memoryless plant: measured M = 1700 - K (raising the fee K pushes the measured signal down).
    # Setpoint 1000 -> equilibrium K = 700, M = 1000. The velocity-form PI drives K there; the gate
    # caps each step at 50 bps. We assert: (a) every applied step was admitted by the gate, and
    # (b) the signal converges from |error| = 200 to within the integer DEADZONE.
    #
    # NOTE (honest property of fixed-point control): with integer gain Ki = ki_num/ki_den, an error
    # smaller than ki_den floor-divides to 0, so steady-state error is bounded by ~ki_den (16 here),
    # not zero. A larger Ki would shrink it but make the first big-error step exceed the gate's
    # 50-bps cap. We set deadband = ki_den so the controller cleanly freezes at the deadzone edge.
    DEADZONE = 16
    cfg = gp.PIConfig(setpoint=1000, kp_num=1, kp_den=8, ki_num=1, ki_den=DEADZONE,
                      deadband=DEADZONE, out_lo=0, out_hi=1000)
    K, prev_error = 500, 0
    all_admitted = True
    for _ in range(150):
        M = 1700 - K
        r = gp.pi_propose(K, M, prev_error, cfg)
        prev_error = r.prev_error
        d = _step(K, r.proposed)
        all_admitted = all_admitted and (d.admitted or r.proposed == K)
        K = d.applied
    final_M = 1700 - K
    assert all_admitted, "a well-tuned PI must stay within the gate's per-step bound"
    assert abs(final_M - 1000) <= DEADZONE, f"did not converge into the deadzone: M={final_M}"
    assert abs(final_M - 1000) < 200, "must improve substantially from the initial |error|=200"
    assert 700 - DEADZONE <= K <= 700 + DEADZONE, f"knob did not settle near equilibrium 700: K={K}"


# --------------------------------------------------------------------------- #
# type discipline
# --------------------------------------------------------------------------- #
def test_loop_rejects_non_int_values():
    with pytest.raises(TypeError):
        gov_loop.autonomous_revision_step(True, 520, FEE, approved=True, proposal_ts=0, current_ts=MD)


def test_loop_rejects_non_bool_approved():
    with pytest.raises(TypeError):
        gov_loop.autonomous_revision_step(500, 520, FEE, approved=1, proposal_ts=0, current_ts=MD)


def test_loop_rejects_non_bool_gate_verdict():
    # (Codex round-2 hardening) a truthy non-bool verdict (int, mock-like object) must hard-fail,
    # not be coerced into "admitted".
    for verdict in (1, "yes", object()):
        def fake_gate(approved, exec_req, p_ts, c_ts, curr, nxt, _v=verdict):
            return _v
        with pytest.raises(TypeError):
            gov_loop.autonomous_revision_step(500, 520, fake_gate,
                                              approved=True, proposal_ts=0, current_ts=MD)


def test_loop_rejects_hostile_int_subclass_committed_curr():
    # (Codex round-3, the serious one) a hostile int subclass reaching committed_curr/proposed_next
    # used to pass BOTH the loop's check and the gate's isinstance domain guard, admitting an
    # out-of-cap jump (RevisionDecision(admitted=True, applied=9000)). Both now exact-type.
    class EvilInt(int):
        def __sub__(self, other):
            return 0  # spoof |next - curr| == 0 to slip past the step check, if it were reached
    with pytest.raises(TypeError):
        gov_loop.autonomous_revision_step(EvilInt(500), 9000, FEE,
                                          approved=True, proposal_ts=0, current_ts=MD)
    with pytest.raises(TypeError):
        gov_loop.autonomous_revision_step(500, EvilInt(9000), FEE,
                                          approved=True, proposal_ts=0, current_ts=MD)


def test_gate_domain_rejects_hostile_int_subclass():
    # The gate (authority) itself must reject the subclass at its domain guard, independent of the
    # loop — defense in depth: a direct caller can't admit an out-of-cap jump via an evil int.
    class EvilInt(int):
        def __sub__(self, other):
            return 0
    assert gov_gate.fee_revision_ok(True, True, 0, MD, EvilInt(500), 9000) is False
    assert gov_gate.fee_revision_ok(True, True, 0, MD, 500, EvilInt(9000)) is False


# --------------------------------------------------------------------------- #
# Multi-surface revision step (all-or-nothing; factory action shape)
# --------------------------------------------------------------------------- #
import json as _json  # noqa: E402

_FIXTURES = Path(__file__).resolve().parent / "fixtures"

# A sane committed envelope anchor: every surface mid-range; router shares sum to 10000;
# mcr close to ccr so an order-break is reachable within one collateral step.
COMMITTED = {
    "fee_bps": 300, "funding_cap_bps": 100, "redeem_staker_bps": 6000,
    "buyburn_bps": 2000, "stakers_bps": 6000, "reserve_bps": 1000, "hosts_bps": 1000,
    "mcr_bps": 14500, "ccr_bps": 15000,
}


def _multi(deltas, *, committed=None, approved=True, pts=0, cts=MD, **kw):
    return gov_loop.multi_surface_revision_step(
        dict(committed or COMMITTED), deltas,
        approved=approved, proposal_ts=pts, current_ts=cts, **kw)


def test_multi_hold_is_admitted_noop_without_gates():
    d = _multi({})
    assert d.admitted is True and d.reason == "admitted_hold"
    assert d.applied == COMMITTED and d.rejected_surface is None


def test_multi_single_surface_fee_admit_and_apply():
    d = _multi({"fee_bps": 10})
    assert d.admitted is True and d.reason == "admitted"
    assert d.applied["fee_bps"] == 310
    # untouched surfaces carried through unchanged
    assert d.applied["funding_cap_bps"] == 100 and d.applied["stakers_bps"] == 6000


def test_multi_coordinated_two_surface_action_admits():
    # the factory's raise_fee_10_tighten_funding_5 shape
    d = _multi({"fee_bps": 10, "funding_cap_bps": -5})
    assert d.admitted and d.applied["fee_bps"] == 310 and d.applied["funding_cap_bps"] == 95


def test_multi_router_shift_admits_when_sum_preserved():
    # the factory's shift_router_to_reserve_100 shape: sum stays 10000, steps <= 500
    d = _multi({"buyburn_bps": -100, "reserve_bps": 100})
    assert d.admitted and d.applied["buyburn_bps"] == 1900 and d.applied["reserve_bps"] == 1100
    assert d.applied["stakers_bps"] == 6000 and d.applied["hosts_bps"] == 1000


def test_multi_all_or_nothing_legal_plus_illegal_rejects_everything():
    # THE load-bearing test: fee +10 is legal alone, but the router sum-break poisons the
    # WHOLE action — nothing applies, including the legal fee move.
    d = _multi({"fee_bps": 10, "buyburn_bps": 100})  # sum 10100: router sum gate must fire
    assert d.admitted is False and d.rejected_surface == "router"
    assert d.reason == "rejected_by_gate:router"
    assert d.applied == COMMITTED  # fee NOT applied


def test_multi_negative_controls_mirror_factory_corpus():
    # the factory corpus negative-control ids, reproduced through MY gates:
    cases = {
        "fee_step_over_50": ({"fee_bps": 60}, "fee_bps"),
        "fee_cap_over_1000": ({"fee_bps": 20}, "fee_bps"),  # from committed fee 990 below
        "funding_underflow": ({"funding_cap_bps": -150}, "funding_cap_bps"),
        "router_sum_break": ({"buyburn_bps": 100}, "router"),
        "whale_step_over_500": ({"redeem_staker_bps": 600}, "redeem_staker_bps"),
        "collateral_order_break": ({"mcr_bps": 1000}, "collateral"),  # 15500 > ccr 15000
    }
    for name, (deltas, expect_surface) in cases.items():
        committed = dict(COMMITTED)
        if name == "fee_cap_over_1000":
            committed["fee_bps"] = 990  # step 20 legal, cap 1010 > 1000 illegal
        d = _multi(deltas, committed=committed)
        assert d.admitted is False, name
        assert d.rejected_surface == expect_surface, name
        assert d.applied == committed, name  # reject-is-no-op on every control


def test_multi_requires_approval_and_timelock():
    ok = {"fee_bps": 10}
    assert _multi(ok, approved=False).admitted is False
    assert _multi(ok, cts=MD - 1).admitted is False  # timelock not elapsed
    # wrap-safe direction: proposal in the future must not admit
    assert _multi(ok, pts=MD + 100, cts=MD).admitted is False


def test_multi_exact_types_fail_closed():
    class LyingDict(dict):
        pass

    class EvilKey(str):
        pass

    with pytest.raises(TypeError):
        _multi(LyingDict({"fee_bps": 10}))
    with pytest.raises(TypeError):
        gov_loop.multi_surface_revision_step(
            LyingDict(COMMITTED), {"fee_bps": 10}, approved=True, proposal_ts=0, current_ts=MD)
    with pytest.raises(TypeError):
        _multi({EvilKey("fee_bps"): 10})
    with pytest.raises(TypeError):
        _multi({"fee_bps": True})  # bool delta
    with pytest.raises(ValueError):
        _multi({"evil_bps": 10})  # unknown surface must hard-reject, never silently pass
    with pytest.raises(ValueError):
        gov_loop.multi_surface_revision_step(
            {"fee_bps": 300}, {"fee_bps": 10}, approved=True, proposal_ts=0, current_ts=MD,
        )  # committed missing surfaces
    with pytest.raises(TypeError):
        _multi({"fee_bps": 10}, approved=1)  # non-bool approved


def test_multi_gate_verdict_must_be_real_bool_and_gates_are_import_bound(monkeypatch):
    # the real-bool contract is enforced by _require_bool_verdict (an int 1 must raise, not admit):
    with pytest.raises(TypeError):
        gov_loop._require_bool_verdict(1)
    with pytest.raises(TypeError):
        gov_loop._require_bool_verdict("yes")
    assert gov_loop._require_bool_verdict(True) is True
    assert gov_loop._require_bool_verdict(False) is False
    # AND the gates are bound at import time (early binding) — a runtime monkeypatch of the
    # gov_gate module CANNOT swap a forged always-admit gate under the loop; the step still
    # consults the original verified gate (this is the no-forged-wrapper property, empirically):
    monkeypatch.setattr(gov_gate, "fee_revision_ok", lambda *a: True)
    d = _multi({"fee_bps": 9000})  # far out of envelope; the forged gate would admit it
    assert d.admitted is False and d.rejected_surface == "fee_bps"  # original gate in force


def test_multi_snapshot_defeats_midcall_mutation_of_caller_dicts():
    # the loop must never read the caller's dicts after its snapshot: mutating them after the
    # call started (here: between construction and use via a hostile later read there is no
    # window — so we assert the DECISION's recorded committed/deltas are private copies)
    committed = dict(COMMITTED)
    deltas = {"fee_bps": 10}
    d = _multi(deltas, committed=committed)
    committed["fee_bps"] = 0
    deltas["fee_bps"] = 9999
    assert d.committed["fee_bps"] == 300 and d.deltas["fee_bps"] == 10  # private copies


def test_factory_policy_fixture_actions_all_gate_admissible():
    # DIFFERENTIAL BINDING to the concurrent policy-factory lane: every action in the frozen
    # zenodex.autonomous_governance.q_policy.v1 artifact (built by the factory with my gate's
    # guardrails as negative controls) must be admissible through the real gates from a sane
    # mid-range committed state — proving the two lanes meet: factory actions are in-envelope,
    # and this loop can gate them directly with no adapter.
    art = _json.loads((_FIXTURES / "factory_q_policy_sample.json").read_text())
    assert art["schema"] == "zenodex.autonomous_governance.q_policy.v1"
    assert len(art["actions"]) == 7
    seen_multi_surface = 0
    for action in art["actions"]:
        deltas = action["deltas"]
        assert type(deltas) is dict
        d = _multi(dict(deltas))
        assert d.admitted is True, action["id"]
        if len(deltas) >= 2:
            seen_multi_surface += 1
            for k, dv in deltas.items():
                assert d.applied[k] == COMMITTED[k] + dv, action["id"]
    assert seen_multi_surface >= 4  # the coordinated fee+funding and router-shift actions
