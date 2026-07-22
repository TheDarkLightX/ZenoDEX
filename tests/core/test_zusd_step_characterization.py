"""Characterization + structural guard for the zUSD step machine after the
dispatch-table refactor of ``_step_python``.

The refactor replaced a monolithic if/elif chain with a total ``tag -> handler``
dispatch table; each handler returns ``(new_state, effects)`` on success or a reject
``ZUSDStepResult``, and the shared tail (post-state invariant check + accept) and the
fail-closed ``except`` wrapper run once in ``_step_python``. Equivalence to the prior
implementation was verified bit-identically against a 2058-case golden corpus during
development; this module is the committed permanent guard. It locks:

* dispatch TOTALITY (the table covers exactly the known command set);
* fail-closed shape (every input yields a ``ZUSDStepResult``; rejects carry no state;
  accepts carry an invariant-clean state);
* determinism (a step is a pure function of (state, cmd));
* non-vacuous coverage (every command tag is exercised on both accept and reject).
"""

from __future__ import annotations

import random
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import src.core.zusd as Z  # noqa: E402

E8 = Z.E8

_KNOWN_TAGS = {
    "advance_epoch", "bootstrap_oracle", "oracle_report", "oracle_commit",
    "deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd",
    "deposit_sp", "withdraw_sp", "redeem_zusd", "liquidate",
}


def _ready_state() -> Z.ZUSDState:
    return Z.ZUSDState(
        now_epoch=5, oracle_seen=True, oracle_last_update_epoch=5,
        price_e8=100 * E8, price_pending_e8=100 * E8, collateral_e8=10000 * E8,
        debt_e8=1000 * E8, free_debt_e8=1000 * E8, base_rate_bps=200,
        base_rate_borrow_bump_bps=50, base_rate_redeem_bump_bps=50,
        borrow_fee_max_bps=500, redemption_fee_max_bps=500, liquidation_gas_comp_bps=100,
    )


def _liquidatable_state() -> Z.ZUSDState:
    # Valid (debt == free + sp) and under MCR at the finalized price.
    return Z.ZUSDState(
        now_epoch=5, oracle_seen=True, oracle_last_update_epoch=5,
        price_e8=10 * E8, price_pending_e8=10 * E8, collateral_e8=100 * E8,
        debt_e8=1000 * E8, free_debt_e8=0, sp_debt_e8=1000 * E8,
        max_sp_coll_e8=10 ** 30, liquidation_gas_comp_bps=100,
        liquidation_gas_comp_fixed_collateral_e8=E8,
    )


def _rand_args(rng: random.Random, tag: str) -> dict:
    if tag == "advance_epoch":
        return {"delta": rng.choice([0, 1, 5, -1, 200])}
    if tag in ("bootstrap_oracle", "oracle_report"):
        return {"auth_ok": rng.choice([True, False]),
                "price_e8": rng.choice([0, -1, 100 * E8, 90 * E8, 50 * E8])}
    if tag in ("oracle_commit", "liquidate"):
        return {"auth_ok": rng.choice([True, False])}
    return {"amount_e8": rng.choice([0, -1, 1, 100 * E8, 1000 * E8, 5000 * E8, 10 ** 9])}


def _corpus():
    """Deterministic (seeded) corpus of (state, cmd) covering every tag on both
    accept and reject, including the liquidation accept path."""
    rng = random.Random(20260614)
    bases = [Z.ZUSDState(), _ready_state(), _liquidatable_state()]
    items = []
    for base in bases:
        for tag in sorted(_KNOWN_TAGS):
            for _ in range(6):
                items.append((base, Z.ZUSDCommand(tag=tag, args=_rand_args(rng, tag))))
    for _ in range(400):
        s = rng.choice([Z.ZUSDState(), _ready_state()])
        for _ in range(rng.randint(1, 8)):
            tag = rng.choice(sorted(_KNOWN_TAGS))
            cmd = Z.ZUSDCommand(tag=tag, args=_rand_args(rng, tag))
            items.append((s, cmd))
            r = Z._step_python(s, cmd)
            if r.ok and r.state is not None:
                s = r.state
    return items


def test_dispatch_table_is_total_and_matches_known_commands():
    """The dispatch table covers EXACTLY the known command set -- no missing handler
    (would silently become 'unknown action') and no stray extra handler."""
    assert set(Z._ZUSD_STEP_HANDLERS.keys()) == _KNOWN_TAGS


def test_unknown_tag_is_rejected_fail_closed():
    r = Z._step_python(Z.ZUSDState(), Z.ZUSDCommand(tag="does_not_exist", args={}))
    assert r.ok is False and r.state is None
    assert "unknown action" in (r.error or "")


def test_step_is_total_deterministic_and_fail_closed_over_corpus():
    """Every (state, cmd) yields a ZUSDStepResult; accepts carry an invariant-clean
    state; rejects carry no state; the step is deterministic. Also asserts the corpus
    is NON-VACUOUS: every tag is exercised on both accept and reject."""
    accept_tags: Counter = Counter()
    reject_tags: Counter = Counter()
    for state, cmd in _corpus():
        r1 = Z._step_python(state, cmd)
        r2 = Z._step_python(state, cmd)
        # determinism
        assert (r1.ok, r1.error, r1.effects) == (r2.ok, r2.error, r2.effects)
        assert isinstance(r1, Z.ZUSDStepResult)
        tag = str(cmd.tag)
        if r1.ok:
            assert r1.state is not None, f"accept must carry state ({tag})"
            assert Z.check_invariants(r1.state) == [], f"accept must be invariant-clean ({tag})"
            accept_tags[tag] += 1
        else:
            assert r1.state is None, f"reject must not leak state ({tag})"
            reject_tags[tag] += 1

    missing_accept = _KNOWN_TAGS - set(accept_tags)
    missing_reject = _KNOWN_TAGS - set(reject_tags)
    assert not missing_accept, f"tags never accepted (vacuous coverage): {missing_accept}"
    assert not missing_reject, f"tags never rejected (vacuous coverage): {missing_reject}"


# --------------------------------------------------------------------------------
# step_multi (two-vault) -- same dispatch-table refactor, same structural guards.
# --------------------------------------------------------------------------------
_PER_VAULT_TAGS = {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd", "liquidate"}


def _ready_multi() -> "Z.ZUSDMultiState":
    return Z.ZUSDMultiState(
        now_epoch=5, oracle_seen=True, oracle_last_update_epoch=5,
        price_e8=100 * E8, price_pending_e8=100 * E8,
        vault_a=Z.ZUSDVault(collateral_e8=10000 * E8, debt_e8=1000 * E8),
        vault_b=Z.ZUSDVault(collateral_e8=8000 * E8, debt_e8=500 * E8),
        free_debt_e8=1000 * E8, sp_debt_e8=500 * E8,  # free + sp == total vault debt (1500)
        base_rate_bps=200, base_rate_borrow_bump_bps=50,
        base_rate_redeem_bump_bps=50, borrow_fee_max_bps=500, redemption_fee_max_bps=500,
    )


def _liq_multi(which: str) -> "Z.ZUSDMultiState":
    va = Z.ZUSDVault(100 * E8, 1000 * E8) if which == "a" else Z.ZUSDVault(10000 * E8, 0)
    vb = Z.ZUSDVault(100 * E8, 1000 * E8) if which == "b" else Z.ZUSDVault(10000 * E8, 0)
    return Z.ZUSDMultiState(
        now_epoch=5, oracle_seen=True, oracle_last_update_epoch=5,
        price_e8=10 * E8, price_pending_e8=10 * E8, vault_a=va, vault_b=vb,
        free_debt_e8=0, sp_debt_e8=1000 * E8, max_sp_coll_e8=10 ** 30,
    )


def _rand_multi_args(rng: random.Random, tag: str) -> dict:
    if tag == "advance_epoch":
        return {"delta": rng.choice([0, 1, 5, -1, 200])}
    if tag in ("bootstrap_oracle", "oracle_report"):
        return {"auth_ok": rng.choice([True, False]),
                "price_e8": rng.choice([0, -1, 100 * E8, 90 * E8, 50 * E8])}
    if tag == "oracle_commit":
        return {"auth_ok": rng.choice([True, False])}
    a: dict = {}
    if tag in _PER_VAULT_TAGS:
        a["vault"] = rng.choice(["a", "b", "bad", None])
    if tag == "redeem_zusd":
        a["vault"] = rng.choice(["a", "b", None, "bad"])
    if tag != "liquidate":
        a["amount_e8"] = rng.choice([0, -1, 1, 100 * E8, 500 * E8, 1000 * E8, 10 ** 9])
    return a


def _multi_corpus():
    rng = random.Random(20260614)
    bases = [Z.ZUSDMultiState(), _ready_multi(), _liq_multi("a"), _liq_multi("b")]
    items = []
    for base in bases:
        for tag in sorted(_KNOWN_TAGS):
            for _ in range(6):
                items.append((base, Z.ZUSDMultiCommand(tag=tag, args=_rand_multi_args(rng, tag))))
    for _ in range(300):
        s = rng.choice([Z.ZUSDMultiState(), _ready_multi()])
        for _ in range(rng.randint(1, 8)):
            tag = rng.choice(sorted(_KNOWN_TAGS))
            cmd = Z.ZUSDMultiCommand(tag=tag, args=_rand_multi_args(rng, tag))
            items.append((s, cmd))
            r = Z.step_multi(s, cmd)
            if r.ok and r.state is not None:
                s = r.state
    return items


def test_multi_dispatch_table_is_total_and_matches_known_commands():
    assert set(Z._ZUSD_MULTI_STEP_HANDLERS.keys()) == _KNOWN_TAGS


def test_multi_unknown_tag_is_rejected_fail_closed():
    r = Z.step_multi(Z.ZUSDMultiState(), Z.ZUSDMultiCommand(tag="nope", args={}))
    assert r.ok is False and r.state is None and "unknown action" in (r.error or "")


def test_multi_step_is_total_deterministic_and_fail_closed_over_corpus():
    """Two-vault analogue: total/deterministic/fail-closed; accepts are invariant-clean;
    every tag exercised on accept AND reject (incl. per-vault liquidation accept)."""
    accept_tags: Counter = Counter()
    reject_tags: Counter = Counter()
    for state, cmd in _multi_corpus():
        r1 = Z.step_multi(state, cmd)
        r2 = Z.step_multi(state, cmd)
        assert (r1.ok, r1.error, r1.effects) == (r2.ok, r2.error, r2.effects)
        assert isinstance(r1, Z.ZUSDMultiStepResult)
        tag = str(cmd.tag)
        if r1.ok:
            assert r1.state is not None
            assert Z.check_multi_invariants(r1.state) == [], f"accept must be invariant-clean ({tag})"
            accept_tags[tag] += 1
        else:
            assert r1.state is None, f"reject must not leak state ({tag})"
            reject_tags[tag] += 1
    assert not (_KNOWN_TAGS - set(accept_tags)), f"tags never accepted: {_KNOWN_TAGS - set(accept_tags)}"
    assert not (_KNOWN_TAGS - set(reject_tags)), f"tags never rejected: {_KNOWN_TAGS - set(reject_tags)}"


def test_handlers_return_tuple_or_reject_when_they_return():
    """Each handler's contract: when it RETURNS (rather than raising on malformed
    input, which the dispatcher's `except` wrapper catches), it returns either
    (ZUSDState, dict) on success or a reject ZUSDStepResult with ok=False -- never
    anything else (the dispatcher relies on this discriminated-union shape)."""
    rng = random.Random(7)
    saw_tuple = saw_reject = saw_raise = 0
    for tag, handler in Z._ZUSD_STEP_HANDLERS.items():
        for base in (Z.ZUSDState(), _ready_state(), _liquidatable_state()):
            try:
                res = handler(base, Z.ZUSDCommand(tag=tag, args=_rand_args(rng, tag)))
            except Exception:
                saw_raise += 1  # malformed input -> raise -> caught by the dispatcher
                continue
            if isinstance(res, Z.ZUSDStepResult):
                assert res.ok is False  # handlers only emit rejects, never accepts
                saw_reject += 1
            else:
                ns, eff = res
                assert isinstance(ns, Z.ZUSDState) and isinstance(eff, dict)
                saw_tuple += 1
    # Non-vacuity: the contract was exercised in all three shapes.
    assert saw_tuple and saw_reject and saw_raise
