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
