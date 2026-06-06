"""Step bindings for clearinghouse_core.feature.

Every step drives the LIVE pure core in ``src/core/perp_np_clearinghouse.py``.
No model, no fixture stand-in: a green scenario is the live authority behaving
as the front door says it does. Rejections are caught so a ``Then`` step can
assert BOTH that a rejection happened AND that it was a no-op (state identity).
"""
from __future__ import annotations

from copy import deepcopy
from decimal import Decimal, InvalidOperation

from src.core import perp_np_clearinghouse as ch
from tests.bdd.runner import StepRegistry

registry = StepRegistry()
step = registry.step

E8 = 100_000_000


def make_context() -> dict:
    return {"state": None, "pre_state": None, "pre_snapshot": None, "error": None}


def _amount(s: str) -> int:
    """Human units -> e8. Supports decimals and negatives (e.g. '1.00', '-1')."""
    # REVIEW [B -> A-]: the first front-door draft used float+round, which can
    # hide decimal drift in behavioral specs. Feature amounts are consensus
    # examples, so parse them exactly and reject values below e8 precision.
    try:
        scaled = Decimal(s) * E8
    except InvalidOperation as exc:
        raise AssertionError(f"invalid decimal amount {s!r}") from exc
    if scaled != scaled.to_integral_value():
        raise AssertionError(f"amount {s!r} is not representable at e8 precision")
    return int(scaled)


def _attempt(ctx: dict, fn) -> None:
    """Run a (possibly rejecting) pure transition; record the post-state or error.

    On rejection the pure core should raise before observable mutation. The
    Then-step checks both rebinding and structural equality.
    """
    ctx["pre_state"] = ctx["state"]
    ctx["pre_snapshot"] = deepcopy(ctx["state"])
    ctx["error"] = None
    try:
        ctx["state"] = fn(ctx["state"])
    except Exception as exc:  # noqa: BLE001 -- asserted on in a Then step
        ctx["error"] = exc


# --- Given ---------------------------------------------------------------------
@step("an initialized {market} market at index price {price} with insurance seed {seed}")
def _init(ctx, market, price, seed):
    ctx["market"] = market
    ctx["state"] = ch.init_market(_amount(price), insurance_seed_e8=_amount(seed))


@step("wallet {w} has deposited {amt} collateral")
def _given_deposited(ctx, w, amt):
    ctx["state"] = ch.deposit(ctx["state"], w, _amount(amt))


# --- When ----------------------------------------------------------------------
@step("wallet {w} deposits {amt} collateral")
def _when_deposit(ctx, w, amt):
    _attempt(ctx, lambda st: ch.deposit(st, w, _amount(amt)))


@step("wallet {w} withdraws {amt} collateral")
def _when_withdraw(ctx, w, amt):
    _attempt(ctx, lambda st: ch.withdraw(st, w, _amount(amt)))


# --- Then ----------------------------------------------------------------------
@step("wallet {w} has collateral {amt}")
def _then_collateral(ctx, w, amt):
    acct = ctx["state"].by_pubkey().get(w)
    assert acct is not None, f"no account for {w}"
    assert acct.collateral_e8 == _amount(amt), (acct.collateral_e8, _amount(amt))


@step("wallet {w} has a flat position")
def _then_flat(ctx, w):
    assert ctx["state"].by_pubkey()[w].position_base == 0


@step("wallet {w} has an account")
def _then_has_account(ctx, w):
    assert w in ctx["state"].by_pubkey()


@step("wallet {w} account nonce is {n}")
def _then_nonce(ctx, w, n):
    assert ctx["state"].by_pubkey()[w].nonce == int(n)


@step("collateral conservation holds")
def _then_conservation(ctx):
    # The live authority's OWN invariant set: (I) net-zero, (II) value
    # conservation D + I_ext == Sigma coll + F + I, insurance ledger, solvency.
    violations = ch.check_invariants(ctx["state"], require_margin=False)
    assert violations == [], violations


@step("the transition is rejected")
def _then_rejected(ctx):
    assert ctx["error"] is not None, "expected a rejection but the transition succeeded"


@step("the market state is unchanged")
def _then_unchanged(ctx):
    # REVIEW [B+ -> A-]: identity alone proves the runner did not rebind state,
    # but it would miss an in-place mutation before raising. Keep the identity
    # check and add a structural snapshot comparison for the actual no-op claim.
    assert ctx["state"] is ctx["pre_state"], "reject must be a no-op (state identity preserved)"
    assert ctx["state"] == ctx["pre_snapshot"], "reject mutated the market state before raising"
