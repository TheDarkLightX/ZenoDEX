"""Tests for the reference autonomous-governance proposers (gov_proposers.py).

Covers determinism (no floats/randomness), the velocity-form PI (deadband freeze, no steady-state
runaway, output clamp), config/type validation, and the frozen Q-table's deterministic lookup +
hash-pin + fail-closed default + non-int rejection. (The proposer+gate composition / safety property
is in test_gov_loop.py.)
"""
from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

_GOV = Path(__file__).resolve().parents[3] / "src" / "tau_specs" / "governance"
sys.path.insert(0, str(_GOV))

import gov_proposers as gp  # noqa: E402


def _cfg(**over):
    base = dict(setpoint=1000, kp_num=1, kp_den=8, ki_num=1, ki_den=16,
                deadband=5, out_lo=0, out_hi=10000)
    base.update(over)
    return gp.PIConfig(**base)


# --------------------------------------------------------------------------- #
# PI controller (velocity form)
# --------------------------------------------------------------------------- #
def test_pi_deterministic():
    assert gp.pi_propose(500, 1200, 0, _cfg()) == gp.pi_propose(500, 1200, 0, _cfg())


def test_pi_raises_knob_when_measured_above_setpoint():
    r = gp.pi_propose(500, 1200, 0, _cfg())  # error +200
    assert r.proposed > 500 and r.prev_error == 200


def test_pi_lowers_knob_when_measured_below_setpoint():
    r = gp.pi_propose(500, 800, 0, _cfg())  # error -200
    assert r.proposed < 500 and r.prev_error == -200


def test_pi_deadband_freezes_and_keeps_state():
    # |error| = 3 <= deadband 5 => freeze: no move AND no state change, even with a nonzero prev_error
    r = gp.pi_propose(500, 1003, 1000, _cfg(deadband=5))
    assert r.proposed == 500 and r.prev_error == 1000


def test_pi_no_runaway_at_steady_state():
    # at the setpoint (error 0, inside deadband) the value must HOLD across repeated steps
    # (the old positional-form bug added the integral every step -> runaway).
    cfg = _cfg(deadband=2)
    val, pe = 700, 0
    for _ in range(50):
        r = gp.pi_propose(val, 1000, pe, cfg)  # measured == setpoint
        val, pe = r.proposed, r.prev_error
    assert val == 700  # held, no drift toward out_hi


def test_pi_output_clamped_to_band():
    r = gp.pi_propose(900, 60000, 0, _cfg(out_hi=1000))
    assert r.proposed == 1000  # clamped before the gate ever sees it


def test_pi_rejects_non_int_args():
    with pytest.raises(TypeError):
        gp.pi_propose(True, 1200, 0, _cfg())


def test_piconfig_rejects_non_int_field():
    with pytest.raises(TypeError):
        gp.PIConfig(setpoint=1000, kp_num=1, kp_den=8.0, ki_num=1, ki_den=16,
                    deadband=5, out_lo=0, out_hi=10000)


def test_piconfig_rejects_zero_denominator():
    with pytest.raises(ValueError):
        _cfg(kp_den=0)


def test_pi_rejects_forged_cfg():
    # (Codex round-2 MED) a duck-typed cfg never ran PIConfig's field validation and could smuggle
    # floats into the math; pi_propose must accept the exact PIConfig type only.
    forged = SimpleNamespace(setpoint=1000, kp_num=0.5, kp_den=1, ki_num=0.5, ki_den=1,
                             deadband=0, out_lo=0, out_hi=10000)
    with pytest.raises(TypeError):
        gp.pi_propose(500, 1200, 0, forged)

    class SubCfg(gp.PIConfig):  # subclass could override validation -> also rejected
        pass

    sub = SubCfg(setpoint=1000, kp_num=1, kp_den=8, ki_num=1, ki_den=16,
                 deadband=5, out_lo=0, out_hi=10000)
    with pytest.raises(TypeError):
        gp.pi_propose(500, 1200, 0, sub)


def test_pi_rejects_hostile_int_subclass():
    # (Codex round-3) an int subclass overriding __sub__ used to put a FLOAT into the math
    # (PIResult(proposed=537.0, prev_error=200.5)); "plain int" must be exact-type, not isinstance.
    class FloatyInt(int):
        def __sub__(self, other):
            return 200.5
    with pytest.raises(TypeError):
        gp.pi_propose(500, FloatyInt(1200), 0, _cfg())


# --------------------------------------------------------------------------- #
# Frozen Q-table
# --------------------------------------------------------------------------- #
def test_bin_index_monotone():
    edges = (100, 500, 2000)
    assert [gp.bin_index(v, edges) for v in (50, 100, 499, 500, 5000)] == [0, 1, 1, 2, 3]


def test_bin_index_rejects_non_int_edges():
    # (Codex round-2 MED) bin_index(1, (0.5,)) used to return 1 — float edges must be rejected.
    for bad_edges in ((0.5,), (100, 500.0), (True, 500)):
        with pytest.raises(TypeError):
            gp.bin_index(1, bad_edges)


def test_bin_index_rejects_unsorted_edges():
    # the "sorted ascending" precondition is enforced, not assumed (duplicates included)
    for bad_edges in ((500, 100), (100, 100, 500)):
        with pytest.raises(ValueError):
            gp.bin_index(1, bad_edges)


def test_q_table_deterministic_and_hit():
    table = {"0,1": 480, "1,1": 520, "2,2": 600}
    r1 = gp.q_table_propose((1, 1), table, curr=500)
    assert r1 == gp.q_table_propose((1, 1), table, curr=500)
    assert r1.hit and r1.proposed == 520


def test_q_table_missing_bin_is_fail_closed():
    r = gp.q_table_propose((9, 9), {"0,0": 480}, curr=500)
    assert not r.hit and r.proposed == 500


def test_q_table_rejects_non_int_action():
    for bad in ("520", 520.0, True):
        with pytest.raises(TypeError):
            gp.q_table_propose((0, 0), {"0,0": bad}, curr=500)


def test_q_table_rejects_non_int_bins():
    # (Codex round-2 MED) q_table_propose((True,), {"True": 520}, 500) used to hit — a bool bin
    # stringifies as "True" and keys a different row than the int it equals. Rejected in state_key.
    for bad_bins in ((True,), (0.5, 1), (1, "2")):
        with pytest.raises(TypeError):
            gp.q_table_propose(bad_bins, {"True": 520, "0.5,1": 520, "1,2": 520}, curr=500)
        with pytest.raises(TypeError):
            gp.state_key(bad_bins)


def test_state_key_rejects_hostile_int_subclass():
    # (Codex round-3) an int subclass overriding __str__ used to stringify a bin to "True" and hit
    # a different table row than the int value; exact-type rejection closes that lookup spoof.
    class KeyInt(int):
        def __str__(self):
            return "True"
    with pytest.raises(TypeError):
        gp.state_key((KeyInt(1),))
    with pytest.raises(TypeError):
        gp.q_table_propose((KeyInt(1),), {"True": 520}, curr=500)


def test_table_hash_stable_and_order_independent():
    assert gp.table_hash({"0,1": 480, "1,1": 520}) == gp.table_hash({"1,1": 520, "0,1": 480})


def test_table_hash_changes_on_content_change():
    assert gp.table_hash({"0,0": 480}) != gp.table_hash({"0,0": 481})
