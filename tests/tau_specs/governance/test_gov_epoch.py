"""Tests for the autonomous-governance EPOCH MACHINE (gov_epoch.py).

The headline results are empirical, not asserted:
  * a poisoned policy proposing one LEGAL max step every cycle is halted by the DRIFT
    BUDGET at 3 steps per window — per-step-admissible is not trajectory-admissible;
  * an expired/revoked charter halts the lane to HOLD (dead-man: autonomy fails closed);
  * the guardian veto kills a pending revision and works even while frozen;
  * a coordinated every-surface-one-legal-step action is rejected by the AGGREGATE
    budget while every per-surface gate would individually admit it;
  * params NEVER change on any reject (receipt digests prove the no-op);
  * the import-bound gates cannot be forged by monkeypatching gov_gate/gov_loop.
"""
from __future__ import annotations

import sys
from dataclasses import replace
from pathlib import Path

import pytest

_GOV = Path(__file__).resolve().parents[3] / "src" / "tau_specs" / "governance"
sys.path.insert(0, str(_GOV))

import gov_epoch as ge  # noqa: E402
import gov_gate  # noqa: E402
import gov_loop  # noqa: E402

PIN = "ab" * 32  # 64-char lowercase hex policy pin
GENESIS_PARAMS = {
    "fee_bps": 500, "funding_cap_bps": 100, "redeem_staker_bps": 6000,
    "buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": 2000,
    "mcr_bps": 11000, "ccr_bps": 15000,
}
MD = ge.MIN_DELAY            # 24
CD = ge.COOLDOWN_EPOCHS      # 48
WIN = ge.DRIFT_WINDOW        # 720


def chartered(epoch: int = 0, ttl: int = 4096) -> ge.GovEpochState:
    s = ge.genesis_state(GENESIS_PARAMS, epoch=epoch)
    s, r = ge.renew_charter(s, now_epoch=epoch, ttl=ttl, policy_pin=PIN)
    assert r.code == ge.GOV_OK_CHARTER_RENEWED
    return s


def params(s: ge.GovEpochState) -> dict[str, int]:
    return {k: v for k, v in s.params}


def propose_apply(s, deltas, at, apply_at):
    s, rp = ge.propose_revision(s, deltas, now_epoch=at)
    assert rp.code == ge.GOV_OK_PROPOSED, rp.code
    s, ra = ge.apply_pending(s, now_epoch=apply_at)
    return s, ra


# --------------------------------------------------------------------------- #
# lifecycle basics
# --------------------------------------------------------------------------- #
def test_genesis_is_fail_closed_no_charter():
    s = ge.genesis_state(GENESIS_PARAMS)
    s2, r = ge.propose_revision(s, {"fee_bps": 10}, now_epoch=0)
    assert r.code == ge.GOV_REJ_CHARTER_INVALID and s2 is s


def test_happy_path_propose_mature_apply():
    s = chartered()
    s, r = propose_apply(s, {"fee_bps": 50}, at=0, apply_at=CD)
    assert r.code == ge.GOV_OK_APPLIED
    assert params(s)["fee_bps"] == 550
    assert s.pending is None
    assert r.digest_before != r.digest_after
    assert r.policy_pin == PIN


def test_timelock_immature_keeps_pending():
    s = chartered()
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s2, r = ge.apply_pending(s, now_epoch=MD - 1)
    assert r.code == ge.GOV_REJ_TIMELOCK
    assert s2 is s and s2.pending is not None       # kept: not yet mature, wait
    s3, r2 = ge.apply_pending(s2, now_epoch=CD)     # matured (and past genesis cooldown)
    assert r2.code == ge.GOV_OK_APPLIED and params(s3)["fee_bps"] == 550


def test_pending_exists_blocks_second_proposal():
    s = chartered()
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s2, r = ge.propose_revision(s, {"fee_bps": 10}, now_epoch=1)
    assert r.code == ge.GOV_REJ_PENDING_EXISTS and s2 is s


def test_empty_action_rejected():
    s = chartered()
    s2, r = ge.propose_revision(s, {}, now_epoch=0)
    assert r.code == ge.GOV_REJ_EMPTY_ACTION and s2 is s


# --------------------------------------------------------------------------- #
# THE TRAJECTORY HEADLINE: a per-step-legal walk is halted by the drift budget
# --------------------------------------------------------------------------- #
def test_poisoned_policy_max_step_walk_halts_at_drift_budget():
    # fee: step 50, window budget 150 (3 steps per 720 epochs). A poisoned policy
    # proposes +50 every cycle; the pointwise gate admits EVERY one of them, the
    # trajectory tier halts the walk at 3.
    s = chartered()
    t = 0
    fees = [500]
    codes = []
    for _ in range(4):
        s, rp = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=t)
        assert rp.code == ge.GOV_OK_PROPOSED
        s, ra = ge.apply_pending(s, now_epoch=t + CD)
        codes.append(ra.code)
        fees.append(params(s)["fee_bps"])
        t += CD
    assert codes == [ge.GOV_OK_APPLIED] * 3 + [ge.GOV_REJ_DRIFT_BUDGET]
    assert fees == [500, 550, 600, 650, 650]   # 4th step did NOT move the param
    # each rejected step was individually legal for the pointwise gate:
    assert gov_gate.fee_revision_ok(True, True, 0, MD, 650, 700)
    # window roll re-opens the budget — but only after a FULL window from genesis
    s, ra = propose_apply(s, {"fee_bps": 50}, at=WIN, apply_at=WIN + CD)
    assert ra.code == ge.GOV_OK_APPLIED and params(s)["fee_bps"] == 700


def test_drift_budget_counts_magnitude_not_direction():
    # +50 then -50 nets to zero displacement but consumes 100 of the 150 budget:
    # oscillation is movement (anti-thrash is the point).
    s = chartered()
    s, r1 = propose_apply(s, {"fee_bps": 50}, at=0, apply_at=CD)
    s, r2 = propose_apply(s, {"fee_bps": -50}, at=CD, apply_at=2 * CD)
    s, r3 = propose_apply(s, {"fee_bps": 50}, at=2 * CD, apply_at=3 * CD)
    assert [r1.code, r2.code, r3.code] == [ge.GOV_OK_APPLIED] * 3
    s, r4 = propose_apply(s, {"fee_bps": -50}, at=3 * CD, apply_at=4 * CD)
    assert r4.code == ge.GOV_REJ_DRIFT_BUDGET   # 150 consumed by |+50|+|-50|+|+50|


def test_cooldown_blocks_rapid_consecutive_applies():
    s = chartered()
    s, r1 = propose_apply(s, {"fee_bps": 50}, at=0, apply_at=CD)
    assert r1.code == ge.GOV_OK_APPLIED
    # re-propose immediately; timelock matures at CD+MD but cooldown needs CD+CD
    s, _ = ge.propose_revision(s, {"fee_bps": 10}, now_epoch=CD)
    s2, r2 = ge.apply_pending(s, now_epoch=CD + MD)
    assert r2.code == ge.GOV_REJ_COOLDOWN and r2.surface == "fee_bps"
    assert s2.pending is None                   # cleared: re-propose required
    assert params(s2)["fee_bps"] == 550         # no-op on params


# --------------------------------------------------------------------------- #
# charter: dead-man expiry + revocation
# --------------------------------------------------------------------------- #
def test_charter_expiry_halts_lane_dead_man():
    s = chartered(ttl=100)
    # inside ttl: works
    s, r = propose_apply(s, {"fee_bps": 50}, at=0, apply_at=CD)
    assert r.code == ge.GOV_OK_APPLIED
    # propose inside ttl, mature AFTER expiry: apply must reject (validity AT now)
    s, _ = ge.propose_revision(s, {"fee_bps": 10}, now_epoch=70)
    s2, r2 = ge.apply_pending(s, now_epoch=100)         # 100 - 0 >= ttl 100 => expired
    assert r2.code == ge.GOV_REJ_CHARTER_INVALID
    assert s2.pending is None and params(s2)["fee_bps"] == 550
    # and proposing after expiry rejects too
    s3, r3 = ge.propose_revision(s2, {"fee_bps": 10}, now_epoch=101)
    assert r3.code == ge.GOV_REJ_CHARTER_INVALID and s3 is s2
    # renewal restores the lane
    s4, _ = ge.renew_charter(s3, now_epoch=101, ttl=100, policy_pin=PIN)
    s5, r5 = ge.propose_revision(s4, {"fee_bps": 10}, now_epoch=101)
    assert r5.code == ge.GOV_OK_PROPOSED


def test_revocation_is_immediate_and_idempotent():
    s = chartered()
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s, r = ge.revoke_charter(s, now_epoch=1)
    assert r.code == ge.GOV_OK_CHARTER_REVOKED
    s2, r2 = ge.apply_pending(s, now_epoch=CD)
    assert r2.code == ge.GOV_REJ_CHARTER_INVALID and s2.pending is None
    s3, r3 = ge.revoke_charter(s2, now_epoch=2)          # idempotent
    assert r3.code == ge.GOV_OK_CHARTER_REVOKED and s3.charter.revoked
    s4, r4 = ge.revoke_charter(ge.genesis_state(GENESIS_PARAMS), now_epoch=0)
    assert r4.code == ge.GOV_REJ_NO_CHARTER


def test_charter_ttl_constitutional_cap_enforced():
    s = ge.genesis_state(GENESIS_PARAMS)
    with pytest.raises(ValueError):
        ge.renew_charter(s, now_epoch=0, ttl=ge.CHARTER_TTL_MAX + 1, policy_pin=PIN)
    with pytest.raises(ValueError):
        ge.renew_charter(s, now_epoch=0, ttl=0, policy_pin=PIN)


# --------------------------------------------------------------------------- #
# veto + freeze
# --------------------------------------------------------------------------- #
def test_veto_kills_pending():
    s = chartered()
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s, r = ge.veto_pending(s, now_epoch=5)
    assert r.code == ge.GOV_OK_VETOED and s.pending is None
    s2, r2 = ge.apply_pending(s, now_epoch=CD)
    assert r2.code == ge.GOV_REJ_NO_PENDING
    s3, r3 = ge.veto_pending(s, now_epoch=6)
    assert r3.code == ge.GOV_REJ_NO_PENDING and s3 is s


def test_veto_works_while_frozen():
    s = chartered()
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s, _ = ge.set_frozen(s, True, now_epoch=1)
    s, r = ge.veto_pending(s, now_epoch=2)
    assert r.code == ge.GOV_OK_VETOED and s.pending is None


def test_freeze_halts_propose_and_apply():
    s = chartered()
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s, _ = ge.set_frozen(s, True, now_epoch=1)
    s2, r = ge.apply_pending(s, now_epoch=CD)
    assert r.code == ge.GOV_REJ_FROZEN and s2.pending is None
    assert params(s2)["fee_bps"] == 500
    s3, r3 = ge.propose_revision(s2, {"fee_bps": 10}, now_epoch=CD)
    assert r3.code == ge.GOV_REJ_FROZEN and s3 is s2
    # unfreeze restores the lane
    s4, _ = ge.set_frozen(s3, False, now_epoch=CD)
    s5, r5 = ge.propose_revision(s4, {"fee_bps": 10}, now_epoch=CD)
    assert r5.code == ge.GOV_OK_PROPOSED


def test_set_frozen_is_idempotent_and_exact_bool():
    s = chartered()
    s1, _ = ge.set_frozen(s, False, now_epoch=0)
    assert s1 is s
    with pytest.raises(TypeError):
        ge.set_frozen(s, 1, now_epoch=0)


# --------------------------------------------------------------------------- #
# aggregate epoch budget: coordinated regime walk
# --------------------------------------------------------------------------- #
def test_single_group_max_actions_fit_epoch_budget():
    # full sum-preserving router rebalance: aggregate 2000 == budget (boundary admit)
    s = chartered()
    deltas = {"buyburn_bps": -500, "stakers_bps": 500, "reserve_bps": -500, "hosts_bps": 500}
    s, r = propose_apply(s, deltas, at=0, apply_at=CD)
    assert r.code == ge.GOV_OK_APPLIED
    assert params(s)["buyburn_bps"] == 5500 and params(s)["hosts_bps"] == 2500
    # collateral pair at full step: aggregate 2000 == budget
    s2 = chartered()
    s2, r2 = propose_apply(s2, {"mcr_bps": 1000, "ccr_bps": 1000}, at=0, apply_at=CD)
    assert r2.code == ge.GOV_OK_APPLIED


def test_coordinated_every_surface_walk_rejected_by_aggregate_budget():
    # every surface one LEGAL step at once: per-surface gates would admit each group,
    # drift budgets all pass (fresh windows) — the AGGREGATE budget rejects (4575 > 2000).
    s = chartered()
    deltas = {
        "fee_bps": 50, "funding_cap_bps": 25, "redeem_staker_bps": 500,
        "buyburn_bps": -500, "stakers_bps": 500, "reserve_bps": -500, "hosts_bps": 500,
        "mcr_bps": 1000, "ccr_bps": 1000,
    }
    s, rp = ge.propose_revision(s, deltas, now_epoch=0)
    assert rp.code == ge.GOV_OK_PROPOSED
    s2, r = ge.apply_pending(s, now_epoch=CD)
    assert r.code == ge.GOV_REJ_EPOCH_BUDGET
    assert params(s2) == GENESIS_PARAMS            # all-or-nothing: nothing moved
    # cross-group: one full group + one scalar overflows the budget by 50
    s3 = chartered()
    s3, r3 = propose_apply(
        s3, {"mcr_bps": 1000, "ccr_bps": 1000, "fee_bps": 50}, at=0, apply_at=CD)
    assert r3.code == ge.GOV_REJ_EPOCH_BUDGET


def test_surface_gate_rejection_names_surface_all_or_nothing():
    s = chartered()
    s, rp = ge.propose_revision(s, {"fee_bps": 60, "funding_cap_bps": 5}, now_epoch=0)
    assert rp.code == ge.GOV_OK_PROPOSED          # well-formed, queued
    s2, r = ge.apply_pending(s, now_epoch=CD)     # fee step 60 > 50 rejects the WHOLE action
    assert r.code == ge.GOV_REJ_SURFACE_GATE and r.surface == "fee_bps"
    assert params(s2) == GENESIS_PARAMS and s2.pending is None


# --------------------------------------------------------------------------- #
# precedence + no-op discipline
# --------------------------------------------------------------------------- #
def test_apply_precedence_no_pending_before_frozen():
    s = chartered()
    s, _ = ge.set_frozen(s, True, now_epoch=0)
    _, r = ge.apply_pending(s, now_epoch=CD)
    assert r.code == ge.GOV_REJ_NO_PENDING        # "apply what?" precedes "may I?"


def test_apply_precedence_frozen_before_charter_and_timelock():
    s = chartered(ttl=10)
    s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=0)
    s, _ = ge.set_frozen(s, True, now_epoch=1)
    # at now=5: frozen=yes, charter still valid, timelock immature -> frozen wins
    _, r = ge.apply_pending(s, now_epoch=5)
    assert r.code == ge.GOV_REJ_FROZEN
    # unfreeze, jump past expiry AND timelock: charter precedes timelock/cooldown
    s2, _ = ge.set_frozen(s, False, now_epoch=5)
    _, r2 = ge.apply_pending(s2, now_epoch=50)    # ttl 10 expired at 10
    assert r2.code == ge.GOV_REJ_CHARTER_INVALID


def test_every_reject_leaves_params_unchanged_with_digest_proof():
    s0 = chartered()
    base_digest = ge.params_digest(GENESIS_PARAMS)
    seen: dict[str, ge.GovReceipt] = {}

    def collect(state, receipt):
        seen[receipt.code] = receipt
        return state

    # timelock (kept), cooldown, drift, epoch budget, surface gate, frozen, charter, veto-empty
    s, _ = ge.propose_revision(s0, {"fee_bps": 50}, now_epoch=0)
    collect(*ge.apply_pending(s, now_epoch=1))                       # timelock
    s1, r1 = propose_apply(s0, {"fee_bps": 50}, at=0, apply_at=CD)   # an APPLIED one (digest moves)
    assert r1.digest_before == base_digest != r1.digest_after
    s2, _ = ge.propose_revision(s1, {"fee_bps": 10}, now_epoch=CD)
    collect(*ge.apply_pending(s2, now_epoch=CD + MD))                # cooldown
    sb, _ = ge.set_frozen(s0, True, now_epoch=0)
    sb, _ = ge.set_frozen(sb, False, now_epoch=0)
    collect(*ge.propose_revision(replace(s0, frozen=True), {"fee_bps": 1}, now_epoch=0))  # frozen
    collect(*ge.apply_pending(replace(s, frozen=True), now_epoch=CD))                     # frozen apply
    collect(*ge.propose_revision(ge.genesis_state(GENESIS_PARAMS), {"fee_bps": 1}, now_epoch=0))
    for code, receipt in seen.items():
        assert receipt.digest_before == receipt.digest_after, code
    assert ge.GOV_REJ_TIMELOCK in seen and ge.GOV_REJ_COOLDOWN in seen
    assert ge.GOV_REJ_FROZEN in seen and ge.GOV_REJ_CHARTER_INVALID in seen


def test_determinism_same_inputs_same_receipts():
    s = chartered()
    s1, r1 = propose_apply(s, {"fee_bps": 50}, at=0, apply_at=CD)
    s2, r2 = propose_apply(s, {"fee_bps": 50}, at=0, apply_at=CD)
    assert r1 == r2 and s1 == s2


# --------------------------------------------------------------------------- #
# hostile-object regressions (the 8-round arc patterns, applied from day one)
# --------------------------------------------------------------------------- #
def test_hostile_int_subclass_delta_rejected():
    class EvilInt(int):
        def __abs__(self):
            return 0
    s = chartered()
    with pytest.raises(TypeError):
        ge.propose_revision(s, {"fee_bps": EvilInt(50)}, now_epoch=0)


def test_hostile_dict_subclass_deltas_rejected():
    class LyingDict(dict):
        def items(self):  # pragma: no cover - must never be consulted
            return iter([("fee_bps", 1)])
    s = chartered()
    with pytest.raises(TypeError):
        ge.propose_revision(s, LyingDict({"fee_bps": 9000}), now_epoch=0)


def test_unknown_surface_hard_rejects():
    s = chartered()
    with pytest.raises(ValueError):
        ge.propose_revision(s, {"charter_ttl": 9999}, now_epoch=0)   # no self-amendment


def test_forged_state_via_object_setattr_rejected_at_use():
    s = chartered()
    object.__setattr__(s, "frozen", 2)                 # bypass frozen=True dataclass
    with pytest.raises(TypeError):
        ge.apply_pending(s, now_epoch=CD)


def test_forged_charter_ttl_rejected_at_use():
    s = chartered()
    object.__setattr__(s.charter, "ttl", 70000)        # out of u16 / over cap
    with pytest.raises(TypeError):
        ge.propose_revision(s, {"fee_bps": 10}, now_epoch=0)


def test_duck_typed_state_rejected():
    class FakeState:
        params = tuple(sorted(GENESIS_PARAMS.items()))
        traj = ()
        charter = None
        frozen = False
        pending = None
    with pytest.raises(TypeError):
        ge.apply_pending(FakeState(), now_epoch=CD)


def test_bool_epoch_rejected_everywhere():
    s = chartered()
    with pytest.raises(TypeError):
        ge.propose_revision(s, {"fee_bps": 10}, now_epoch=True)
    with pytest.raises(TypeError):
        ge.apply_pending(s, now_epoch=True)


def test_hostile_policy_pin_rejected():
    class EvilStr(str):
        pass
    s = ge.genesis_state(GENESIS_PARAMS)
    with pytest.raises(TypeError):
        ge.renew_charter(s, now_epoch=0, ttl=10, policy_pin=EvilStr("ab" * 32))
    with pytest.raises(TypeError):
        ge.renew_charter(s, now_epoch=0, ttl=10, policy_pin="AB" * 32)  # uppercase


# --------------------------------------------------------------------------- #
# forged-gate empiricism: monkeypatching gov_gate/gov_loop cannot reach the
# import-bound authorities (r9 lesson — EVERY authority, not just the obvious one)
# --------------------------------------------------------------------------- #
def test_forged_gates_do_not_bite(monkeypatch):
    calls = {"n": 0}

    def always_admit(*a, **k):
        calls["n"] += 1
        return True

    monkeypatch.setattr(gov_gate, "drift_budget_ok", always_admit)
    monkeypatch.setattr(gov_gate, "cooldown_ok", always_admit)
    monkeypatch.setattr(gov_gate, "charter_ok", always_admit)
    monkeypatch.setattr(gov_gate, "epoch_budget_ok", always_admit)
    monkeypatch.setattr(gov_loop, "multi_surface_revision_step", always_admit)

    # un-chartered lane still rejects (charter authority not swappable)
    s = ge.genesis_state(GENESIS_PARAMS)
    _, r = ge.propose_revision(s, {"fee_bps": 10}, now_epoch=0)
    assert r.code == ge.GOV_REJ_CHARTER_INVALID
    # drift walk still halts at the budget (drift authority not swappable)
    s = chartered()
    t, codes = 0, []
    for _ in range(4):
        s, _ = ge.propose_revision(s, {"fee_bps": 50}, now_epoch=t)
        s, ra = ge.apply_pending(s, now_epoch=t + CD)
        codes.append(ra.code)
        t += CD
    assert codes[-1] == ge.GOV_REJ_DRIFT_BUDGET
    # the fakes were never consulted — the patch cannot reach the bound locals
    assert calls["n"] == 0
    # non-vacuity: the fake WOULD admit anything if it were reachable
    assert always_admit(0, 0, 0, 0) is True and calls["n"] == 1


# --------------------------------------------------------------------------- #
# T1 MED regressions: _validate_state must be canonical for forged states
# --------------------------------------------------------------------------- #
def test_forged_duplicate_params_entry_rejected():
    # 10 sorted entries, every surface present, fee_bps duplicated with a hostile
    # value: pre-fix this PASSED validation and _params_dict collapsed the dup
    # (last won) — gates/receipts then operated on a map differing from the
    # accepted state object. Must now hard-reject.
    s = chartered()
    dup = tuple(sorted(list(s.params) + [("fee_bps", 9000)]))
    object.__setattr__(s, "params", dup)
    with pytest.raises(ValueError):
        ge.propose_revision(s, {"fee_bps": 10}, now_epoch=0)
    with pytest.raises(ValueError):
        ge.apply_pending(s, now_epoch=CD)
    s2 = chartered()
    dup_traj = tuple(sorted(list(s2.traj) + [("fee_bps", dict(s2.traj)["fee_bps"])]))
    object.__setattr__(s2, "traj", dup_traj)
    with pytest.raises(ValueError):
        ge.apply_pending(s2, now_epoch=CD)


def test_forged_hostile_params_key_rejected_before_any_comparison():
    # a str-subclass key planted via object.__setattr__ must be type-rejected
    # BEFORE sorted()/set() can consult its __lt__/__eq__/__hash__ — the call
    # counter proves the hostile dunders never run. (Pre-fix: sorted()/set()
    # consulted them — hostile code EXECUTED inside the validator — before the
    # per-entry type loop eventually rejected; the fix removes the execution
    # window, not just the final verdict.)
    calls = {"n": 0}

    class EvilKey(str):
        def __lt__(self, other):  # pragma: no cover - must never be consulted
            calls["n"] += 1
            return str.__lt__(self, other)

        def __gt__(self, other):  # pragma: no cover - must never be consulted
            calls["n"] += 1
            return str.__gt__(self, other)

        def __eq__(self, other):
            calls["n"] += 1
            return str.__eq__(self, other)

        __hash__ = str.__hash__

    s = chartered()
    forged = tuple((EvilKey(k) if k == "fee_bps" else k, v) for k, v in s.params)
    object.__setattr__(s, "params", forged)
    with pytest.raises(TypeError):
        ge.propose_revision(s, {"fee_bps": 10}, now_epoch=0)
    assert calls["n"] == 0
