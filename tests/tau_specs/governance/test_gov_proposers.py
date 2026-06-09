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
