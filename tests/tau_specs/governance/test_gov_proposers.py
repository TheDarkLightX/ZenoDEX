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


class _LyingBins:
    """(Codex round-4) an iterable whose __iter__ yields clean ints on the FIRST pass (validation)
    and a hostile __str__-overriding int subclass on the SECOND pass (use) — a TOCTOU attack."""
    def __init__(self):
        self._calls = 0

    class _KeyInt(int):
        def __str__(self):
            return "True"

    def __iter__(self):
        self._calls += 1
        if self._calls == 1:
            return iter((1,))                       # validation pass sees a clean int
        return iter((self._KeyInt(1),))             # use pass tries to inject "True"


def test_state_key_defeats_two_pass_toctou():
    # materialize-once: __iter__ is called a single time, so the lying second pass never happens.
    b = _LyingBins()
    # either it rejects the hostile subclass, or (because it materialized the clean first pass) it
    # returns the honest "1" — never the spoofed "True".
    try:
        assert gp.state_key(b) == "1"
    except TypeError:
        pass  # also acceptable: caught the subclass
    b2 = _LyingBins()
    try:
        r = gp.q_table_propose(b2, {"True": 520, "1": 480}, curr=500)
        assert r.proposed != 520, "TOCTOU spoof reached the poisoned 'True' row"
    except TypeError:
        pass


class _LyingEdges:
    """(Codex round-4) edges that validate as (0,) on the first pass then SWAP to (100,) on the
    second. The swapped values are chosen so the result distinguishes the fix: with materialize-once
    the comparison uses the validated (0,) -> bin_index(5)=1; the old two-pass code would have
    validated (0,) but COMPARED against (100,) -> bin_index(5)=0."""
    def __init__(self):
        self._calls = 0

    def __iter__(self):
        self._calls += 1
        return iter((0,)) if self._calls == 1 else iter((100,))


def test_bin_index_defeats_two_pass_toctou():
    e = _LyingEdges()
    # materialize-once: the use pass reads the SAME captured (0,) the validation pass approved.
    assert gp.bin_index(5, e) == 1  # 5 >= 0 -> 1 (NOT 0, which the swapped (100,) would give)


def test_pi_revalidates_mutated_frozen_cfg():
    # (Codex round-4) a frozen PIConfig mutated post-construction via object.__setattr__ (which
    # bypasses immutability) must be re-rejected at use-time, not trusted from construction.
    cfg = _cfg()
    object.__setattr__(cfg, "kp_num", 0.5)  # smuggle a float past the frozen guard
    with pytest.raises(TypeError):
        gp.pi_propose(500, 1200, 0, cfg)


def test_table_hash_stable_and_order_independent():
    assert gp.table_hash({"0,1": 480, "1,1": 520}) == gp.table_hash({"1,1": 520, "0,1": 480})


def test_q_table_rejects_dict_subclass():
    # (Codex round-5) a dict subclass can override __contains__/__getitem__ to lie about its
    # contents, making the pinned hash disagree with the lookup. Reject non-plain-dict tables.
    class LyingDict(dict):
        def __contains__(self, k):
            return True

        def __getitem__(self, k):
            return 520

    bad = LyingDict({"1": 500})
    with pytest.raises(TypeError):
        gp.q_table_propose((1,), bad, curr=500)
    with pytest.raises(TypeError):
        gp.table_hash(bad)


def test_q_table_rejects_str_subclass_key():
    # (Codex round-5) a str-subclass key can json-serialise as one string but compare equal to a
    # different runtime key, so table_hash and the lookup diverge. Reject non-plain-str keys.
    class EvilKey(str):
        def __eq__(self, other):
            return other == "1"

        def __hash__(self):
            return hash("1")

    table = {EvilKey("not-the-key"): 520}
    with pytest.raises(TypeError):
        gp.q_table_propose((1,), table, curr=500)
    with pytest.raises(TypeError):
        gp.table_hash(table)


def test_q_table_and_hash_share_validation():
    # the pin and the lookup are over the SAME validated structure: a table table_hash accepts is
    # exactly one q_table_propose will look up in (both reject the same hostile tables).
    good = {"0,0": 480, "1,1": 520}
    assert isinstance(gp.table_hash(good), str)            # accepted by the pin
    assert gp.q_table_propose((1, 1), good, curr=500).proposed == 520  # and by the lookup


def test_q_table_expected_hash_match_is_admitted():
    table = {"1,1": 520}
    pin = gp.table_hash(table)
    r = gp.q_table_propose((1, 1), table, curr=500, expected_hash=pin)
    assert r.hit and r.proposed == 520  # correct pin -> normal lookup


def test_q_table_rejects_stale_pin_after_mutation():
    # (Codex round-6) the EXACT pin↔use gap: hash a table, MUTATE it, then look up with the stale
    # pin. The mutation changes the action (520 -> 9000), so this is non-vacuous: without the
    # use-boundary check the lookup would return the mutated 9000 under a pin that no longer matches.
    table = {"1,1": 520}
    pin = gp.table_hash(table)        # client pins the frozen artifact
    table["1,1"] = 9000               # table mutated AFTER the pin
    with pytest.raises(ValueError):
        gp.q_table_propose((1, 1), table, curr=500, expected_hash=pin)
    # and without the pin, the stale/mutated table is silently used (documents the two-step risk):
    assert gp.q_table_propose((1, 1), table, curr=500).proposed == 9000


def test_q_table_rejects_non_str_expected_hash():
    table = {"1,1": 520}
    with pytest.raises(TypeError):
        gp.q_table_propose((1, 1), table, curr=500, expected_hash=12345)


def test_q_table_snapshot_defeats_bins_iter_mutation_toctou():
    # (Codex round-6 MED) mutation DURING the call: `state_key(bins)` runs the caller's
    # `__iter__` AFTER the digest check but BEFORE the lookup. A hostile bins that mutates the
    # (plain) table there used to return the post-hash action (9000) under the STALE pin —
    # bypassing both the pin and value validation. The snapshot makes the lookup read the
    # pinned artifact. Non-vacuous: the post-call assert proves the hostile mutation DID fire
    # on the caller's dict, and the result still came from the snapshot (520, not 9000).
    table = {"1": 520}
    pin = gp.table_hash(table)

    class MutatingBins:
        def __iter__(self):
            table["1"] = 9000  # fires inside state_key(), after the digest check
            return iter((1,))

    r = gp.q_table_propose(MutatingBins(), table, curr=500, expected_hash=pin)
    assert table["1"] == 9000  # the hostile __iter__ really ran and mutated the caller's dict
    assert r.hit is True and r.state_key == "1"
    assert r.proposed == 520  # the PINNED value — not the post-hash 9000


def test_q_table_snapshot_defeats_bins_iter_type_corruption():
    # same window, nastier payload: the mid-call mutation installs a NON-INT action. Without the
    # snapshot the lookup would return a float that never passed `_validate_table` (validation ran
    # before the mutation). With the snapshot the corrupted entry is never read.
    table = {"1": 520}
    pin = gp.table_hash(table)

    class CorruptingBins:
        def __iter__(self):
            table["1"] = 9000.5  # not a plain int; installed after validation
            return iter((1,))

    r = gp.q_table_propose(CorruptingBins(), table, curr=500, expected_hash=pin)
    assert table["1"] == 9000.5  # corruption really happened on the caller's dict
    assert r.proposed == 520 and type(r.proposed) is int  # snapshot value, type intact


def test_table_hash_changes_on_content_change():
    assert gp.table_hash({"0,0": 480}) != gp.table_hash({"0,0": 481})


# --------------------------------------------------------------------------- #
# Layered (hierarchical) frozen Q-tables
# --------------------------------------------------------------------------- #
def _layered():
    # regime layer: volatility bin -> sub-policy id; action layer per sub-policy:
    # (utilization, peg-dev) bins -> action. Two regimes, different actions for the same state.
    return {
        "regime": {"0": 0, "1": 1, "2": 1},
        "actions": {
            "0": {"0,0": 300, "1,1": 320},   # calm regime: small fees
            "1": {"0,0": 360, "1,1": 400},   # volatile regime: larger fees
        },
    }


def test_layered_q_happy_two_layer_lookup():
    r = gp.layered_q_propose((1,), (1, 1), _layered(), 300)
    assert r.hit is True and r.proposed == 400 and r.regime_id == 1
    assert r.regime_key == "1" and r.action_key == "1,1"


def test_layered_q_regimes_change_the_action_for_the_same_state():
    # the layering is real: identical action_bins, different regime -> different action.
    calm = gp.layered_q_propose((0,), (1, 1), _layered(), 300)
    vol = gp.layered_q_propose((1,), (1, 1), _layered(), 300)
    assert (calm.proposed, vol.proposed) == (320, 400)


def test_layered_q_deterministic_replay():
    assert gp.layered_q_propose((1,), (0, 0), _layered(), 300) == gp.layered_q_propose(
        (1,), (0, 0), _layered(), 300
    )


def test_layered_q_fail_closed_on_every_layer_miss():
    # regime bin missing
    r1 = gp.layered_q_propose((9,), (1, 1), _layered(), 555)
    assert r1.hit is False and r1.proposed == 555 and r1.regime_id is None
    # regime id with no action row (dangling sub-policy id = runtime no-op, not an escape)
    art = _layered()
    art["regime"]["7"] = 7  # no "7" row in actions
    r2 = gp.layered_q_propose((7,), (1, 1), art, 555)
    assert r2.hit is False and r2.proposed == 555 and r2.regime_id == 7
    # action bin missing inside a present row
    r3 = gp.layered_q_propose((1,), (9, 9), _layered(), 555)
    assert r3.hit is False and r3.proposed == 555 and r3.regime_id == 1


def test_layered_q_exact_shape_and_types_fail_closed():
    class LyingDict(dict):
        pass

    class EvilKey(str):
        pass

    class KeyInt(int):
        pass

    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), LyingDict(_layered()), 300)  # dict subclass artifact
    bad = _layered()
    bad["extra"] = {}
    with pytest.raises(ValueError):
        gp.layered_q_propose((0,), (0, 0), bad, 300)  # extra top-level key
    with pytest.raises(ValueError):
        gp.layered_q_propose((0,), (0, 0), {"regime": {}}, 300)  # missing top-level key
    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), {"regime": {EvilKey("0"): 0}, "actions": {}}, 300)
    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), {"regime": {"0": True}, "actions": {}}, 300)  # bool id
    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), {"regime": {"0": 0}, "actions": {"0": {"0,0": KeyInt(5)}}}, 300)
    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), {"regime": {"0": 0}, "actions": {"0": [300]}}, 300)  # row not dict
    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), _layered(), True)  # bool curr


def test_layered_q_hash_pin_match_and_mismatch():
    art = _layered()
    pin = gp.layered_table_hash(art)
    r = gp.layered_q_propose((1,), (1, 1), art, 300, expected_hash=pin)
    assert r.hit and r.proposed == 400
    art["actions"]["1"]["1,1"] = 9000  # mutate AFTER the pin
    with pytest.raises(ValueError):
        gp.layered_q_propose((1,), (1, 1), art, 300, expected_hash=pin)
    # and the pin itself covers BOTH layers: changing only the regime layer changes the hash
    a2 = _layered()
    a2["regime"]["0"] = 1
    assert gp.layered_table_hash(a2) != pin


def test_layered_q_snapshot_defeats_bins_iter_mutation_toctou():
    # same pin/use window as the flat table (Codex r6): regime_bins.__iter__ runs after the
    # digest check; a hostile bins that mutates the artifact there must NOT influence the result.
    art = _layered()
    pin = gp.layered_table_hash(art)

    class MutatingBins:
        def __iter__(self):
            art["actions"]["1"]["1,1"] = 9000  # fires inside state_key(), post-digest
            return iter((1,))

    r = gp.layered_q_propose(MutatingBins(), (1, 1), art, 300, expected_hash=pin)
    assert art["actions"]["1"]["1,1"] == 9000  # the hostile mutation really fired
    assert r.hit is True and r.proposed == 400  # the PINNED action — not the post-hash 9000


def test_layered_q_poisoned_artifact_is_bounded_by_the_gate():
    import gov_gate
    import gov_loop

    # a poisoned layered table proposes 9000; the fee gate (cap 1000, step 50) must reject it
    # and the loop must no-op. A sane action from the same machinery is admitted (non-vacuous).
    poisoned = {"regime": {"1": 1}, "actions": {"1": {"1,1": 9000}}}
    bad = gp.layered_q_propose((1,), (1, 1), poisoned, 300)
    d_bad = gov_loop.autonomous_revision_step(
        300, bad.proposed, gov_gate.fee_revision_ok, approved=True, proposal_ts=0, current_ts=100
    )
    assert d_bad.admitted is False and d_bad.applied == 300
    sane = {"regime": {"1": 1}, "actions": {"1": {"1,1": 320}}}
    good = gp.layered_q_propose((1,), (1, 1), sane, 300)
    d_good = gov_loop.autonomous_revision_step(
        300, good.proposed, gov_gate.fee_revision_ok, approved=True, proposal_ts=0, current_ts=100
    )
    assert d_good.admitted is True and d_good.applied == 320


# --------------------------------------------------------------------------- #
# Energy-based proposer (frozen integer energy model)
# --------------------------------------------------------------------------- #
def _energy(targets=None, w_track=1, w_move=0):
    return {"targets": dict(targets or {"1,1": 340}), "w_track": w_track, "w_move": w_move}


def test_energy_argmin_tracks_target_within_band():
    # curr=300, step=50, target=340 inside the band -> argmin at the target itself
    r = gp.energy_propose((1, 1), _energy(), 300, lo=0, hi=1000, step=50)
    assert r.hit is True and r.proposed == 340 and r.target == 340 and r.energy == 0


def test_energy_argmin_clips_to_band_edge_when_target_is_far():
    # target=900 far above: best reachable candidate is the band edge curr+step
    r = gp.energy_propose((1, 1), _energy({"1,1": 900}), 300, lo=0, hi=1000, step=50)
    assert r.hit is True and r.proposed == 350  # 300+50, nearest the target within the band
    r2 = gp.energy_propose((1, 1), _energy({"1,1": 0}), 300, lo=280, hi=1000, step=50)
    assert r2.proposed == 280  # clipped by lo, not by step


def test_energy_movement_cost_really_reasons():
    # THE non-vacuity test for "reasoning": same state, same target, different weights ->
    # different proposals. Heavy movement cost holds curr; pure tracking chases the target.
    chase = gp.energy_propose((1, 1), _energy({"1,1": 340}, w_track=1, w_move=0), 300, lo=0, hi=1000, step=50)
    hold = gp.energy_propose((1, 1), _energy({"1,1": 340}, w_track=1, w_move=10000), 300, lo=0, hi=1000, step=50)
    assert chase.proposed == 340 and hold.proposed == 300
    assert chase.proposed != hold.proposed


def test_energy_tie_breaks_toward_smallest_candidate():
    # curr=12, target=10, step=2, w_track=1, w_move=1:
    # E(10)=0+2=2, E(11)=1+1=2 (tie), E(12)=4+0=4 -> smallest candidate of the tie wins: 10
    r = gp.energy_propose((0,), _energy({"0": 10}, w_track=1, w_move=1), 12, lo=0, hi=100, step=2)
    assert r.proposed == 10 and r.energy == 2


def test_energy_step_zero_band_is_curr_only():
    r = gp.energy_propose((0,), _energy({"0": 999}), 300, lo=0, hi=1000, step=0)
    assert r.hit is True and r.proposed == 300  # band == {curr}


def test_energy_fail_closed_on_missing_bin_and_empty_band():
    r1 = gp.energy_propose((9, 9), _energy(), 300, lo=0, hi=1000, step=50)
    assert r1.hit is False and r1.proposed == 300 and r1.target is None and r1.energy is None
    # curr stranded below lo beyond step: band empty -> no-op (the gate would reject any move anyway)
    r2 = gp.energy_propose((1, 1), _energy(), 100, lo=200, hi=1000, step=50)
    assert r2.hit is False and r2.proposed == 100 and r2.energy is None


def test_energy_model_validation_fail_closed():
    class LyingDict(dict):
        pass

    with pytest.raises(TypeError):
        gp.energy_propose((0,), LyingDict(_energy()), 300, lo=0, hi=1000, step=50)
    with pytest.raises(ValueError):
        gp.energy_propose((0,), {"targets": {}, "w_track": 0, "w_move": 0}, 300, lo=0, hi=1000, step=50)
    with pytest.raises(ValueError):
        gp.energy_propose((0,), {"targets": {}, "w_track": -1, "w_move": 1}, 300, lo=0, hi=1000, step=50)
    with pytest.raises(TypeError):
        gp.energy_propose((0,), {"targets": {}, "w_track": True, "w_move": 1}, 300, lo=0, hi=1000, step=50)
    bad = _energy()
    bad["extra"] = 1
    with pytest.raises(ValueError):
        gp.energy_propose((0,), bad, 300, lo=0, hi=1000, step=50)
    with pytest.raises(TypeError):
        gp.energy_propose((0,), _energy({"0": 1.5}), 300, lo=0, hi=1000, step=50)  # float target
    with pytest.raises(ValueError):
        gp.energy_propose((0,), _energy(), 300, lo=1000, hi=0, step=50)  # lo > hi
    with pytest.raises(ValueError):
        gp.energy_propose((0,), _energy(), 300, lo=0, hi=1000, step=-1)  # negative step
    with pytest.raises(TypeError):
        gp.energy_propose((0,), _energy(), 300, lo=0, hi=1000, step=True)  # bool step


def test_energy_hash_pin_and_toctou_snapshot():
    art = _energy({"1": 340})
    pin = gp.energy_model_hash(art)
    r = gp.energy_propose((1,), art, 300, lo=0, hi=1000, step=50, expected_hash=pin)
    assert r.proposed == 340
    # stale pin after mutation
    art["targets"]["1"] = 900
    with pytest.raises(ValueError):
        gp.energy_propose((1,), art, 300, lo=0, hi=1000, step=50, expected_hash=pin)
    # mid-call mutation via hostile bins: result must come from the snapshot
    art2 = _energy({"1": 340})
    pin2 = gp.energy_model_hash(art2)

    class MutatingBins:
        def __iter__(self):
            art2["targets"]["1"] = 900  # fires inside state_key(), post-digest
            return iter((1,))

    r2 = gp.energy_propose(MutatingBins(), art2, 300, lo=0, hi=1000, step=50, expected_hash=pin2)
    assert art2["targets"]["1"] == 900  # the hostile mutation really fired
    assert r2.proposed == 340  # the PINNED target's argmin — not the post-hash 900's


def test_energy_poisoned_targets_are_bounded_by_the_gate():
    import gov_gate
    import gov_loop

    # poisoned target 9000: the energy proposer itself only reaches the band edge (350), and the
    # gate then independently verifies. With a poisoned WIDE band (caller lies about lo/hi/step)
    # the gate still rejects the out-of-envelope proposal — the gate, not the band, is the defense.
    r = gp.energy_propose((1,), _energy({"1": 9000}), 300, lo=0, hi=20000, step=20000)
    assert r.proposed == 9000  # the proposer chased the poisoned target through the lying band
    d = gov_loop.autonomous_revision_step(
        300, r.proposed, gov_gate.fee_revision_ok, approved=True, proposal_ts=0, current_ts=100
    )
    assert d.admitted is False and d.applied == 300  # gate bounds it: no-op


def test_layered_q_rejects_str_subclass_top_level_key():
    # (Codex r8 LOW) the shape check ran set-equality BEFORE key-type validation, so a
    # str-subclass top-level key was accepted (its __eq__/__hash__ ran inside the comparison).
    # Non-vacuous: on the pre-fix code this artifact was admitted and looked up normally.
    class EvilKey(str):
        pass

    art = {EvilKey("regime"): {"0": 0}, "actions": {"0": {"0,0": 300}}}
    with pytest.raises(TypeError):
        gp.layered_q_propose((0,), (0, 0), art, 300)


def test_energy_rejects_str_subclass_top_level_key():
    class EvilKey(str):
        pass

    art = {EvilKey("targets"): {"0": 1}, "w_track": 1, "w_move": 0}
    with pytest.raises(TypeError):
        gp.energy_propose((0,), art, 300, lo=0, hi=1000, step=50)
