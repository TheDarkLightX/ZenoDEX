# [TESTER] v1
"""Production-readiness regression: the isolated-perp epoch-lifecycle actions
(advance_epoch, publish_clearing_price, settle_epoch) are OPERATOR-ONLY at the
authority path (``apply_perp_ops``).

Background: the pure-core perp_v2 guards for these lifecycle actions do NOT check
caller authorization — ``guard_advance_epoch`` only checks the epoch bound, and
``guard_publish_clearing_price`` / ``guard_settle_epoch`` check phase but not
``auth_ok`` (per-account actions like set_position DO check auth in the core).
Operator authorization for the lifecycle actions is therefore *shell-delegated*
(``_require_operator`` in ``_apply_isolated_*``), as documented in
``docs/SECURITY_POSTURE.md``. These tests lock that delegation in at the
integration level so a non-operator cannot drive epoch lifecycle / settlement:
each action is rejected with ``operator only`` from a non-operator sender, while
the operator is NOT rejected for being a non-operator (the rejection is
operator-specific, not a universal block).

Production posture only; no settlement-behavior change.
"""

from __future__ import annotations

from src.core.dex import DexState
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable

_OPERATOR = "00" * 48
_ATTACKER = "ff" * 48
_QUOTE = "0x" + "44" * 32
_OPERATOR_ONLY = "operator only"


def _op(market_id: str, action: str, **kw: object) -> dict[str, object]:
    o: dict[str, object] = {
        "module": "TauPerp", "version": "0.1", "market_id": market_id, "action": action}
    o.update(kw)
    return o


def _apply(state: DexState, sender: str, ops: list[dict[str, object]]):
    cfg = PerpEngineConfig(operator_pubkey=_OPERATOR, allow_isolated_markets=True)
    return apply_perp_ops(
        config=cfg, state=state, operations={"5": ops},
        tx_sender_pubkey=sender, block_timestamp=0)


def _fresh_market(market_id: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = _apply(state, _OPERATOR, [_op(market_id, "init_market", quote_asset=_QUOTE)])
    assert res.ok, res.error
    return res.state


def _seed_oracle(state: DexState, market_id: str) -> None:
    gs = state.perps.markets[market_id].global_state
    gs["oracle_seen"] = True
    gs["oracle_last_update_epoch"] = max(0, int(gs.get("now_epoch", 0)) - 1)
    gs["index_price_e8"] = 100_000_000


def test_advance_epoch_is_operator_only() -> None:
    """advance_epoch from a non-operator is rejected with 'operator only'; the
    operator is accepted (so the rejection is operator-specific)."""
    mid = "perp:opgate-advance"
    state = _fresh_market(mid)

    attacker = _apply(state, _ATTACKER, [_op(mid, "advance_epoch", delta=1)])
    assert attacker.ok is False
    assert attacker.error == _OPERATOR_ONLY

    operator = _apply(state, _OPERATOR, [_op(mid, "advance_epoch", delta=1)])
    assert operator.ok is True, operator.error          # not blocked for being operator


def test_publish_clearing_price_is_operator_only() -> None:
    """publish_clearing_price from a non-operator is rejected with 'operator only';
    the operator (in an otherwise-valid state) is accepted."""
    mid = "perp:opgate-publish"
    state = _fresh_market(mid)
    state = _apply(state, _OPERATOR, [_op(mid, "advance_epoch", delta=1)]).state  # epoch 0 -> 1
    _seed_oracle(state, mid)

    attacker = _apply(state, _ATTACKER, [_op(mid, "publish_clearing_price", price_e8=100_000_000)])
    assert attacker.ok is False
    assert attacker.error == _OPERATOR_ONLY

    operator = _apply(state, _OPERATOR, [_op(mid, "publish_clearing_price", price_e8=100_000_000)])
    assert operator.ok is True, operator.error


def test_settle_epoch_is_operator_only() -> None:
    """settle_epoch from a non-operator is rejected with 'operator only'. (The
    operator check precedes settlement preconditions, so the non-operator is
    rejected as 'operator only' regardless of settle-readiness — pinning the
    authorization barrier ahead of the rest of the settle gate.)"""
    mid = "perp:opgate-settle"
    state = _fresh_market(mid)
    state = _apply(state, _OPERATOR, [_op(mid, "advance_epoch", delta=1)]).state
    _seed_oracle(state, mid)
    state = _apply(state, _OPERATOR, [_op(mid, "publish_clearing_price", price_e8=100_000_000)]).state

    attacker = _apply(state, _ATTACKER, [_op(mid, "settle_epoch")])
    assert attacker.ok is False
    assert attacker.error == _OPERATOR_ONLY

    # The operator is not rejected for being a non-operator (it clears the
    # authority barrier; later settlement preconditions are out of scope here).
    operator = _apply(state, _OPERATOR, [_op(mid, "settle_epoch")])
    assert operator.error != _OPERATOR_ONLY
