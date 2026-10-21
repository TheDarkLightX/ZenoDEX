# [TESTER] v1
"""
Atomic route settlement (split-routing) — engine test matrix.

Covers the mandatory matrix in docs/ATOMIC_ROUTE_SETTLEMENT_DESIGN.md:
  1.  2-pool and 3-pool atomic splits settle (exact-in and exact-out)
  2.  any leg failure rejects the WHOLE route with zero state change
  3.  duplicate / missing / extra leg indices rejected
  4.  stale quote receipt rejected
  5.  tampered pool fingerprint rejected
  6.  exact-in min-out and exact-out max-in violations rejected
  7.  deterministic replay -> identical state root
  8.  user balance + pool conservation across all legs
  9.  backend intent_id determinism (signer parity foundation)
  10. single-pool swap path unaffected (route surface is additive)
plus strong-validator boundary tests (forged fills, reserved fields,
engine-witness gating).
"""

from __future__ import annotations

import copy

from src.agents.intent_signer import create_route_intent_from_quote_receipt
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexConfig, DexState
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
from src.core.settlement import FillAction
from src.core.settlement_strong_validator import validate_settlement_strong
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import (
    SignedIntentEnvelope,
    create_signed_intent_operation,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

SENDER = "0x" + "ab" * 48
OTHER = "0x" + "cd" * 48
PROTOCOL_FEE_RECIPIENT = "0x" + "ef" * 48


def _pool(pool_id: str, *, asset0: str = "A", asset1: str = "B", r0: int = 1_000, r1: int = 1_000, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=r0,
        reserve1=r1,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _engine_config(
    *,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
) -> DexEngineConfig:
    return DexEngineConfig(
        allow_missing_settlement=True,
        require_intent_signatures=False,
        dex_config=DexConfig(
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        ),
    )


def _state(pools: dict, *, balances: BalanceTable) -> DexState:
    return DexState(balances=balances, pools=pools, lp_balances=LPTable())


def _exact_in_route_setup(n_pools: int, *, amount_in: int, fee_bps: int = 0):
    pools = {f"p{i}": _pool(f"p{i}", fee_bps=fee_bps) for i in range(1, n_pools + 1)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=amount_in)
    assert quote is not None
    assert all(len(leg.hops) == 1 for leg in quote.legs)
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    return pools, quote, receipt


def _route_intent(receipt, pools, *, sender: str = SENDER, slippage_bps: int = 0, nonce: int = 1, **kwargs):
    return create_route_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=slippage_bps,
        nonce=nonce,
        **kwargs,
    )


def _apply(
    state: DexState,
    envelopes: list[SignedIntentEnvelope],
    *,
    sender: str = SENDER,
    config: DexEngineConfig | None = None,
):
    ops = create_signed_intent_operation(envelopes)
    return apply_ops(
        config=config or _engine_config(),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )


def _assert_asset_conservation(pre_state: DexState, post_state: DexState, assets: tuple[str, ...]) -> None:
    for asset in assets:
        def total(state: DexState, bound_asset: str = asset) -> int:
            balance_sum = sum(
                amount
                for (pubkey, a), amount in state.balances.get_all_balances().items()
                if a == bound_asset
            )
            reserve_sum = 0
            for pool in state.pools.values():
                if pool.asset0 == bound_asset:
                    reserve_sum += int(pool.reserve0)
                if pool.asset1 == bound_asset:
                    reserve_sum += int(pool.reserve1)
            return balance_sum + reserve_sum

        assert total(pre_state) == total(post_state), f"conservation violated for {asset}"


# ---------------------------------------------------------------------------
# 1. successful atomic splits
# ---------------------------------------------------------------------------


def test_route_exact_in_two_pool_split_settles_atomically() -> None:
    pools, quote, receipt = _exact_in_route_setup(2, amount_in=600)
    assert len(quote.legs) == 2
    intent = _route_intent(receipt, pools)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)
    pre_state = copy.deepcopy(state)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert res.ok, res.error

    fills = res.settlement.fills
    assert len(fills) == 1
    fill = fills[0]
    assert fill.action == FillAction.FILL
    assert fill.amount_in_filled == 600
    assert fill.amount_out_filled == int(quote.amount_out)
    assert res.state.balances.get(SENDER, "A") == 10_000 - 600
    assert res.state.balances.get(SENDER, "B") == int(quote.amount_out)
    _assert_asset_conservation(pre_state, res.state, ("A", "B"))


def test_route_exact_in_three_pool_split_settles_atomically() -> None:
    pools, quote, receipt = _exact_in_route_setup(3, amount_in=900)
    assert len(quote.legs) == 3
    intent = _route_intent(receipt, pools)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)
    pre_state = copy.deepcopy(state)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert res.ok, res.error
    fill = res.settlement.fills[0]
    assert fill.action == FillAction.FILL
    assert fill.amount_in_filled == 900
    assert fill.amount_out_filled == int(quote.amount_out)
    # every pool moved (true 3-way split)
    for pool_id in pools:
        assert res.state.pools[pool_id].reserve0 > 1_000
    _assert_asset_conservation(pre_state, res.state, ("A", "B"))


def test_route_exact_out_two_pool_split_settles_atomically() -> None:
    pools = {f"p{i}": _pool(f"p{i}") for i in (1, 2)}
    quote = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=400)
    assert quote is not None
    assert all(len(leg.hops) == 1 for leg in quote.legs)
    receipt = make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools)
    intent = _route_intent(receipt, pools)
    assert intent.kind.value == "ROUTE_EXACT_OUT"

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)
    pre_state = copy.deepcopy(state)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert res.ok, res.error
    fill = res.settlement.fills[0]
    assert fill.action == FillAction.FILL
    assert fill.amount_out_filled == int(quote.amount_out)
    assert fill.amount_in_filled == int(quote.amount_in)
    assert res.state.balances.get(SENDER, "B") == int(quote.amount_out)
    _assert_asset_conservation(pre_state, res.state, ("A", "B"))


def test_route_fee_paid_is_sum_of_leg_fees() -> None:
    from src.core.cpmm import compute_fee_total

    pools, quote, receipt = _exact_in_route_setup(2, amount_in=600, fee_bps=30)
    intent = _route_intent(receipt, pools)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert res.ok, res.error
    fill = res.settlement.fills[0]
    expected_fee = sum(compute_fee_total(int(leg.amount_in), 30) for leg in quote.legs)
    assert fill.fee_paid == expected_fee


# ---------------------------------------------------------------------------
# 2. atomicity: any leg failure -> whole route rejected, zero state change
# ---------------------------------------------------------------------------


def test_route_rejects_atomically_when_shared_pool_drifts_in_batch() -> None:
    # Two routes share p2. Whichever processes second sees p2 drifted from its
    # receipt snapshot and must reject WITHOUT touching its other pool.
    pools = {f"p{i}": _pool(f"p{i}") for i in (1, 2, 3)}
    pools_r1 = {pid: pools[pid] for pid in ("p1", "p2")}
    pools_r2 = {pid: pools[pid] for pid in ("p2", "p3")}

    q1 = best_route_exact_in_2hop(pools_by_id=pools_r1, asset_in="A", asset_out="B", amount_in=600)
    q2 = best_route_exact_in_2hop(pools_by_id=pools_r2, asset_in="A", asset_out="B", amount_in=600)
    assert q1 is not None and q2 is not None
    assert len(q1.legs) == 2 and len(q2.legs) == 2
    r1 = make_route_quote_receipt(kind="exact_in", quote=q1, pools_by_id=pools_r1)
    r2 = make_route_quote_receipt(kind="exact_in", quote=q2, pools_by_id=pools_r2)

    i1 = _route_intent(r1, pools_r1, sender=SENDER, nonce=1)
    i2 = _route_intent(r2, pools_r2, sender=SENDER, nonce=2)

    balances = BalanceTable()
    balances.set(SENDER, "A", 20_000)
    state = _state(pools, balances=balances)

    res = _apply(
        state,
        [
            SignedIntentEnvelope(intent=i1, quote_receipt=r1),
            SignedIntentEnvelope(intent=i2, quote_receipt=r2),
        ],
    )
    assert res.ok, res.error
    actions = {f.intent_id: f for f in res.settlement.fills}
    f1 = actions[i1.intent_id]

    # Canonical determinism: routes clear in ascending intent_id order, so the
    # smaller intent_id MUST be the winner (it sees pristine pools) and the
    # larger MUST reject on drift.
    winner_intent, loser_intent = (i1, i2) if i1.intent_id < i2.intent_id else (i2, i1)
    filled = actions[winner_intent.intent_id]
    rejected = actions[loser_intent.intent_id]
    assert filled.action == FillAction.FILL
    assert rejected.action == FillAction.REJECT
    assert rejected.reason == "ROUTE_POOL_STATE_DRIFT"

    # The rejected route produced ZERO effects: balances reflect ONLY the
    # filled route's totals, and the rejected route's exclusive pool (the one
    # the filled route does not touch) is unmoved.
    exclusive_pool = "p1" if rejected is f1 else "p3"
    assert res.state.balances.get(SENDER, "A") == 20_000 - int(filled.amount_in_filled)
    assert res.state.balances.get(SENDER, "B") == int(filled.amount_out_filled)
    assert res.state.pools[exclusive_pool].reserve0 == 1_000
    assert res.state.pools[exclusive_pool].reserve1 == 1_000


def test_route_rejects_atomically_on_insufficient_total_balance() -> None:
    # Sender can afford the first leg but not the route total: the route must
    # reject as a unit with no partial application.
    pools, quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)
    leg0_in = int(quote.legs[0].amount_in)
    assert leg0_in < 600

    balances = BalanceTable()
    balances.set(SENDER, "A", leg0_in)  # covers leg 0 only
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert res.ok, res.error
    fill = res.settlement.fills[0]
    assert fill.action == FillAction.REJECT
    assert fill.reason == "INSUFFICIENT_BALANCE"
    assert res.state.balances.get(SENDER, "A") == leg0_in
    assert res.state.balances.get(SENDER, "B") == 0
    for pool_id in pools:
        assert res.state.pools[pool_id].reserve0 == 1_000
        assert res.state.pools[pool_id].reserve1 == 1_000


# ---------------------------------------------------------------------------
# 3. leg coverage: duplicate / missing / extra rejected
# ---------------------------------------------------------------------------


def _with_leg_indices(receipt, pools, leg_indices: list[int]):
    intent = _route_intent(receipt, pools)
    intent.set_field("leg_indices", leg_indices)
    return intent


def test_route_rejects_duplicate_leg_indices() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _with_leg_indices(receipt, pools, [0, 0, 1])

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "invalid route intent" in res.error

def test_route_rejects_missing_leg_index() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _with_leg_indices(receipt, pools, [0])

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "route_leg_coverage_mismatch" in res.error


def test_route_rejects_extra_leg_index() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _with_leg_indices(receipt, pools, [0, 1, 2])

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "route_leg_coverage_mismatch" in res.error


# ---------------------------------------------------------------------------
# 4./5. stale receipt + tampered fingerprints
# ---------------------------------------------------------------------------


def test_route_rejects_stale_quote_receipt() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)

    # Pool state moves after the quote was issued.
    pools["p1"].reserve0 += 7

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "invalid quote receipt" in res.error


def test_route_rejects_tampered_receipt_pool_fingerprint() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)

    tampered = copy.deepcopy(receipt)
    tampered["body"]["pools"]["p1"] = "0x" + "00" * 32

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=tampered)])
    assert not res.ok
    assert "invalid quote receipt" in res.error


# ---------------------------------------------------------------------------
# 6. totals violations
# ---------------------------------------------------------------------------


def test_route_rejects_unsatisfiable_min_out() -> None:
    pools, quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)
    intent.set_field("total_min_amount_out", int(quote.amount_out) + 1)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "route_min_out_unsatisfiable" in res.error


def test_route_rejects_unsatisfiable_max_in() -> None:
    pools = {f"p{i}": _pool(f"p{i}") for i in (1, 2)}
    quote = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=400)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools)
    intent = _route_intent(receipt, pools)
    intent.set_field("total_max_amount_in", int(quote.amount_in) - 1)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "route_max_in_unsatisfiable" in res.error


# ---------------------------------------------------------------------------
# 7. deterministic replay
# ---------------------------------------------------------------------------


def test_route_deterministic_replay_identical_post_state() -> None:
    def run():
        pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
        intent = _route_intent(receipt, pools)
        balances = BalanceTable()
        balances.set(SENDER, "A", 10_000)
        state = _state(pools, balances=balances)
        res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
        assert res.ok, res.error
        balances_snapshot = tuple(sorted(res.state.balances.get_all_balances().items()))
        pools_snapshot = tuple(
            (pid, int(p.reserve0), int(p.reserve1), int(p.lp_supply))
            for pid, p in sorted(res.state.pools.items())
        )
        fills_snapshot = tuple(
            (f.intent_id, f.action.value, f.reason, f.amount_in_filled, f.amount_out_filled, f.fee_paid)
            for f in res.settlement.fills
        )
        return balances_snapshot, pools_snapshot, fills_snapshot

    assert run() == run()


# ---------------------------------------------------------------------------
# 9. backend intent id determinism (signer parity foundation)
# ---------------------------------------------------------------------------


def test_route_intent_id_deterministic_for_same_inputs() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    a = _route_intent(receipt, pools)
    b = _route_intent(receipt, pools)
    assert a.intent_id == b.intent_id
    c = _route_intent(receipt, pools, nonce=2)
    assert c.intent_id != a.intent_id


# ---------------------------------------------------------------------------
# 10. additive surface: swap-only batches do not need route bindings
# ---------------------------------------------------------------------------


def test_compute_settlement_signature_backward_compatible() -> None:
    pools = {"p1": _pool("p1")}
    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    # No route_bindings kwarg: legacy call shape still works.
    settlement = compute_settlement(intents=[], pools=pools, balances=balances, lp_balances=LPTable())
    assert settlement.fills == []


# ---------------------------------------------------------------------------
# engine boundary: receipt sharing, reserved fields, witness requirements
# ---------------------------------------------------------------------------


def test_route_receipt_cannot_be_shared_with_swap_intent() -> None:
    from src.agents.intent_signer import create_swap_intent

    pools, quote, receipt = _exact_in_route_setup(2, amount_in=600)
    route_intent = _route_intent(receipt, pools, nonce=1)
    leg0 = quote.legs[0].hops[0]
    swap_intent = create_swap_intent(
        pool_id=leg0.pool_id,
        asset_in="A",
        asset_out="B",
        amount_in=int(leg0.amount_in),
        min_amount_out=0,
        deadline=9999999999,
        sender_pubkey=SENDER,
        quote_receipt_hash=receipt["receipt_hash"],
        quote_receipt_leg_index=0,
        nonce=2,
    )

    balances = BalanceTable()
    balances.set(SENDER, "A", 20_000)
    state = _state(pools, balances=balances)

    res = _apply(
        state,
        [
            SignedIntentEnvelope(intent=route_intent, quote_receipt=receipt),
            SignedIntentEnvelope(intent=swap_intent, quote_receipt=receipt),
        ],
    )
    assert not res.ok
    assert "quote receipt bound by route intent cannot be shared" in res.error


def test_route_rejects_two_routes_binding_same_receipt() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    i1 = _route_intent(receipt, pools, sender=SENDER, nonce=1)
    i2 = _route_intent(receipt, pools, sender=SENDER, nonce=2)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(
        state,
        [
            SignedIntentEnvelope(intent=i1, quote_receipt=receipt),
            SignedIntentEnvelope(intent=i2, quote_receipt=receipt),
        ],
    )
    assert not res.ok
    assert "quote receipt already bound by route intent" in res.error


def test_route_rejects_user_supplied_reserved_binding_fields() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)
    intent.set_field("route_legs", [{"pool_id": "p1"}])

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "must not carry reserved binding fields" in res.error


def test_route_rejects_leg_index_field_on_route_intent() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)
    intent.set_field("quote_receipt_leg_index", 0)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    assert not res.ok
    assert "must not carry quote_receipt_leg_index" in res.error


def test_route_requires_receipt_witness() -> None:
    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    intent = _route_intent(receipt, pools)

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=intent, quote_receipt=None)])
    assert not res.ok
    assert "missing quote receipt witness" in res.error


def test_route_kind_without_hash_or_receipt_fails_closed() -> None:
    from src.state.intents import Intent, IntentKind

    pools, _quote, _receipt = _exact_in_route_setup(2, amount_in=600)
    bare = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_IN,
        intent_id="0x" + "11" * 32,
        sender_pubkey=SENDER,
        deadline=9999999999,
        fields={"nonce": 1},
    )

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)

    res = _apply(state, [SignedIntentEnvelope(intent=bare)])
    assert not res.ok
    assert "route intent requires quote receipt witness" in res.error


def test_route_rejects_multi_hop_receipt() -> None:
    # Pools A/X and X/B force a 2-hop leg: unsupported for v1 route intents.
    pools = {
        "pax": _pool("pax", asset0="A", asset1="X"),
        "pxb": _pool("pxb", asset0="B", asset1="X", r0=2_000, r1=2_000),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    assert any(len(leg.hops) > 1 for leg in quote.legs)
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)

    try:
        create_route_intent_from_quote_receipt(
            receipt=receipt,
            pools_by_id=pools,
            sender_pubkey=SENDER,
            deadline=9999999999,
            slippage_bps=0,
            nonce=1,
        )
        raise AssertionError("expected unsupported_route_receipt")
    except ValueError as exc:
        assert "route_multi_hop_leg_unsupported" in str(exc)


# ---------------------------------------------------------------------------
# strong validator boundary (untrusted settlement / fields)
# ---------------------------------------------------------------------------


def _validator_fixture(
    *,
    fee_bps: int = 0,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
):
    """Engine-equivalent inputs for direct strong-validator calls."""
    from src.core.route_settlement import (
        resolve_route_binding_from_receipt,
        route_binding_to_fields,
    )
    from src.state.intents import Intent

    pools, quote, receipt = _exact_in_route_setup(2, amount_in=600, fee_bps=fee_bps)
    intent = _route_intent(receipt, pools)
    binding, err = resolve_route_binding_from_receipt(receipt)
    assert binding is not None, err

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)

    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={intent.intent_id: binding},
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    assert settlement.fills[0].action == FillAction.FILL

    sanitized_fields = dict(intent.fields or {})
    sanitized_fields.pop("quote_receipt_hash", None)
    sanitized_fields.update(route_binding_to_fields(binding))
    sanitized = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        salt=intent.salt,
        fields=sanitized_fields,
    )
    return pools, balances, settlement, sanitized, quote


def test_validator_accepts_engine_equivalent_route_settlement() -> None:
    pools, balances, settlement, sanitized, _quote = _validator_fixture()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[sanitized],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert ok, err


def test_validator_rejects_forged_route_fill_totals() -> None:
    pools, balances, settlement, sanitized, _quote = _validator_fixture()
    settlement.fills[0].amount_out_filled += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[sanitized],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "route amount_out_filled mismatch" in err


def test_validator_rejects_route_binding_without_engine_witness_gate() -> None:
    pools, balances, settlement, sanitized, _quote = _validator_fixture()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[sanitized],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=False,
    )
    assert not ok
    assert "route binding requires validated engine witness" in err


def test_validator_rejects_route_fields_on_swap_intent() -> None:
    from src.agents.intent_signer import create_swap_intent

    pools = {"p1": _pool("p1")}
    swap = create_swap_intent(
        pool_id="p1",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=0,
        deadline=9999999999,
        sender_pubkey=SENDER,
        nonce=1,
    )
    swap.set_field("route_legs", [])

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    settlement = compute_settlement(intents=[swap], pools=pools, balances=balances, lp_balances=LPTable())

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[swap],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "route binding fields only supported for route intents" in err


def test_validator_rejects_tampered_route_leg_amounts() -> None:
    pools, balances, settlement, sanitized, _quote = _validator_fixture()
    legs = sanitized.get_field("route_legs")
    legs[0]["amount_out"] += 1
    # Keep the claimed fill consistent with the tampered binding so the replay
    # equality (not fill bookkeeping) is what catches the lie.
    settlement.fills[0].amount_out_filled += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[sanitized],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert ("route replay failed" in err) or ("route intent/binding mismatch" in err)


def _two_route_shared_pool_fixture():
    """Two routes sharing p2 (sanitized + bindings), sorted by intent_id."""
    from src.core.route_settlement import (
        resolve_route_binding_from_receipt,
        route_binding_to_fields,
    )
    from src.state.intents import Intent

    pools = {f"p{i}": _pool(f"p{i}") for i in (1, 2, 3)}
    pools_r1 = {pid: pools[pid] for pid in ("p1", "p2")}
    pools_r2 = {pid: pools[pid] for pid in ("p2", "p3")}
    q1 = best_route_exact_in_2hop(pools_by_id=pools_r1, asset_in="A", asset_out="B", amount_in=600)
    q2 = best_route_exact_in_2hop(pools_by_id=pools_r2, asset_in="A", asset_out="B", amount_in=600)
    assert q1 is not None and q2 is not None
    r1 = make_route_quote_receipt(kind="exact_in", quote=q1, pools_by_id=pools_r1)
    r2 = make_route_quote_receipt(kind="exact_in", quote=q2, pools_by_id=pools_r2)
    i1 = _route_intent(r1, pools_r1, sender=SENDER, nonce=1)
    i2 = _route_intent(r2, pools_r2, sender=SENDER, nonce=2)

    def sanitize(intent, receipt):
        binding, err = resolve_route_binding_from_receipt(receipt)
        assert binding is not None, err
        fields = dict(intent.fields or {})
        fields.pop("quote_receipt_hash", None)
        fields.update(route_binding_to_fields(binding))
        return (
            Intent(
                module=intent.module,
                version=intent.version,
                kind=intent.kind,
                intent_id=intent.intent_id,
                sender_pubkey=intent.sender_pubkey,
                deadline=intent.deadline,
                salt=intent.salt,
                fields=fields,
            ),
            binding,
        )

    s1, b1 = sanitize(i1, r1)
    s2, b2 = sanitize(i2, r2)
    pairs = sorted([(s1, b1), (s2, b2)], key=lambda pair: pair[0].intent_id)
    (lo, lo_binding), (hi, hi_binding) = pairs

    balances = BalanceTable()
    balances.set(SENDER, "A", 20_000)
    return pools, balances, lo, lo_binding, hi, hi_binding


def test_validator_rejects_forged_non_canonical_route_winner() -> None:
    # Forge: canonical order kept, but the canonical winner (lo) is marked
    # REJECT and the competing route (hi) fills instead. The must-fill
    # discipline has to catch the unjustified reject.
    from src.core.settlement import Fill, Settlement

    pools, balances, lo, _lo_binding, hi, hi_binding = _two_route_shared_pool_fixture()

    hi_only = compute_settlement(
        intents=[hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={hi.intent_id: hi_binding},
    )
    assert hi_only.fills[0].action == FillAction.FILL

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(lo.intent_id, FillAction.REJECT), (hi.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=lo.intent_id, action=FillAction.REJECT, reason="ROUTE_POOL_STATE_DRIFT"),
            hi_only.fills[0],
        ],
        balance_deltas=hi_only.balance_deltas,
        reserve_deltas=hi_only.reserve_deltas,
        lp_deltas=hi_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "route reject not justified" in err


def test_validator_rejects_non_ascending_route_order() -> None:
    from src.core.settlement import Fill, Settlement

    pools, balances, lo, lo_binding, hi, _hi_binding = _two_route_shared_pool_fixture()

    lo_only = compute_settlement(
        intents=[lo],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={lo.intent_id: lo_binding},
    )
    assert lo_only.fills[0].action == FillAction.FILL

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(hi.intent_id, FillAction.REJECT), (lo.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=hi.intent_id, action=FillAction.REJECT, reason="ROUTE_POOL_STATE_DRIFT"),
            lo_only.fills[0],
        ],
        balance_deltas=lo_only.balance_deltas,
        reserve_deltas=lo_only.reserve_deltas,
        lp_deltas=lo_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "ascending intent_id order" in err


def test_validator_rejects_non_route_intent_settled_before_route() -> None:
    from src.agents.intent_signer import create_swap_intent
    from src.core.settlement import Fill, Settlement

    pools, balances, lo, lo_binding, _hi, _hi_binding = _two_route_shared_pool_fixture()
    swap = create_swap_intent(
        pool_id="p3",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=0,
        deadline=9999999999,
        sender_pubkey=SENDER,
        nonce=3,
    )

    lo_only = compute_settlement(
        intents=[lo],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={lo.intent_id: lo_binding},
    )
    assert lo_only.fills[0].action == FillAction.FILL

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(swap.intent_id, FillAction.REJECT), (lo.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=swap.intent_id, action=FillAction.REJECT, reason="SLIPPAGE"),
            lo_only.fills[0],
        ],
        balance_deltas=lo_only.balance_deltas,
        reserve_deltas=lo_only.reserve_deltas,
        lp_deltas=lo_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[lo, swap],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "non-canonical settlement phase order" in err


def test_validator_rejects_create_pool_settled_after_route() -> None:
    # Codex r2 HIGH: compute creates pools BEFORE routes. A forged settlement
    # that lists a route first, then a CREATE_POOL spending the route's freshly
    # received output, must be rejected (phase order CREATE_POOL < route).
    from src.core.settlement import Fill, FillAction, Settlement
    from src.state.intents import Intent, IntentKind

    pools, _quote, receipt = _exact_in_route_setup(2, amount_in=600)
    route = _route_intent(receipt, pools, nonce=1)

    from src.core.route_settlement import (
        resolve_route_binding_from_receipt,
        route_binding_to_fields,
    )

    binding, err = resolve_route_binding_from_receipt(receipt)
    assert binding is not None, err

    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    route_only = compute_settlement(
        intents=[route],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={route.intent_id: binding},
    )
    assert route_only.fills[0].action == FillAction.FILL

    sanitized_fields = dict(route.fields or {})
    sanitized_fields.pop("quote_receipt_hash", None)
    sanitized_fields.update(route_binding_to_fields(binding))
    sanitized_route = Intent(
        module="TauSwap",
        version="0.1",
        kind=route.kind,
        intent_id=route.intent_id,
        sender_pubkey=route.sender_pubkey,
        deadline=route.deadline,
        fields=sanitized_fields,
    )

    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id="0x" + "fe" * 32,
        sender_pubkey=SENDER,
        deadline=9999999999,
        fields={
            "asset0": "B",
            "asset1": "C",
            "fee_bps": 0,
            "amount0": 100,
            "amount1": 100,
            "nonce": 2,
        },
    )

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[
            (sanitized_route.intent_id, FillAction.FILL),
            (create_pool.intent_id, FillAction.REJECT),
        ],
        fills=[
            route_only.fills[0],
            Fill(intent_id=create_pool.intent_id, action=FillAction.REJECT, reason="INSUFFICIENT_BALANCE"),
        ],
        balance_deltas=route_only.balance_deltas,
        reserve_deltas=route_only.reserve_deltas,
        lp_deltas=route_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[sanitized_route, create_pool],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "non-canonical settlement phase order" in err


def test_validator_rejects_route_reject_with_stripped_binding() -> None:
    # Codex r2 MEDIUM: a forged settlement marks the canonical winner (lo)
    # REJECT but strips its binding fields, then fills the competing route
    # (hi). Under the engine gate every admitted route carries a binding, so a
    # binding-less route REJECT must fail closed.
    from src.core.settlement import Fill, FillAction, Settlement
    from src.state.intents import Intent

    pools, balances, lo, _lo_binding, hi, hi_binding = _two_route_shared_pool_fixture()

    hi_only = compute_settlement(
        intents=[hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={hi.intent_id: hi_binding},
    )
    assert hi_only.fills[0].action == FillAction.FILL

    # Strip lo's engine-injected binding fields.
    stripped_fields = {
        k: v
        for k, v in (lo.fields or {}).items()
        if k not in ("route_legs", "route_pool_fingerprints")
    }
    stripped_lo = Intent(
        module="TauSwap",
        version="0.1",
        kind=lo.kind,
        intent_id=lo.intent_id,
        sender_pubkey=lo.sender_pubkey,
        deadline=lo.deadline,
        fields=stripped_fields,
    )

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(stripped_lo.intent_id, FillAction.REJECT), (hi.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=stripped_lo.intent_id, action=FillAction.REJECT, reason="ROUTE_POOL_STATE_DRIFT"),
            hi_only.fills[0],
        ],
        balance_deltas=hi_only.balance_deltas,
        reserve_deltas=hi_only.reserve_deltas,
        lp_deltas=hi_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[stripped_lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "route reject missing engine binding" in err


def test_validator_rejects_route_reject_with_tampered_binding() -> None:
    # Codex r2 MEDIUM: tamper lo's binding so it no longer matches the signed
    # route, then mark lo REJECT and fill hi. The binding-mismatch must fail
    # closed rather than "justify" the reject.
    from src.core.settlement import Fill, FillAction, Settlement
    from src.state.intents import Intent

    pools, balances, lo, _lo_binding, hi, hi_binding = _two_route_shared_pool_fixture()

    hi_only = compute_settlement(
        intents=[hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={hi.intent_id: hi_binding},
    )
    assert hi_only.fills[0].action == FillAction.FILL

    tampered_fields = dict(lo.fields or {})
    tampered_legs = [dict(leg) for leg in tampered_fields["route_legs"]]
    tampered_legs[0]["amount_out"] = int(tampered_legs[0]["amount_out"]) + 1
    tampered_fields["route_legs"] = tampered_legs
    tampered_lo = Intent(
        module="TauSwap",
        version="0.1",
        kind=lo.kind,
        intent_id=lo.intent_id,
        sender_pubkey=lo.sender_pubkey,
        deadline=lo.deadline,
        fields=tampered_fields,
    )

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(tampered_lo.intent_id, FillAction.REJECT), (hi.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=tampered_lo.intent_id, action=FillAction.REJECT, reason="ROUTE_POOL_STATE_DRIFT"),
            hi_only.fills[0],
        ],
        balance_deltas=hi_only.balance_deltas,
        reserve_deltas=hi_only.reserve_deltas,
        lp_deltas=hi_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[tampered_lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    # amount_out tamper passes the intent/binding shape check (exact-in does
    # not bind total-out) but the kernel replay rejects the inflated leg while
    # fingerprints still match → flagged as inconsistent with the snapshot.
    assert "route reject binding inconsistent with pinned snapshot" in err


def test_validator_rejects_route_reject_with_faked_drift_fingerprint() -> None:
    # Defense-in-depth: tamper lo's route_pool_fingerprints so phase-1 replay
    # yields ROUTE_POOL_STATE_DRIFT (fingerprint matches neither pre- nor
    # current-state). Without the pre-state snapshot anchor this fake drift
    # would "justify" the reject and let hi win.
    from src.core.settlement import Fill, FillAction, Settlement
    from src.state.intents import Intent

    pools, balances, lo, _lo_binding, hi, hi_binding = _two_route_shared_pool_fixture()

    hi_only = compute_settlement(
        intents=[hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={hi.intent_id: hi_binding},
    )
    assert hi_only.fills[0].action == FillAction.FILL

    tampered_fields = dict(lo.fields or {})
    tampered_fps = dict(tampered_fields["route_pool_fingerprints"])
    some_pool = next(iter(tampered_fps))
    tampered_fps[some_pool] = "0x" + "00" * 32  # matches no real pool
    tampered_fields["route_pool_fingerprints"] = tampered_fps
    tampered_lo = Intent(
        module="TauSwap",
        version="0.1",
        kind=lo.kind,
        intent_id=lo.intent_id,
        sender_pubkey=lo.sender_pubkey,
        deadline=lo.deadline,
        fields=tampered_fields,
    )

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(tampered_lo.intent_id, FillAction.REJECT), (hi.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=tampered_lo.intent_id, action=FillAction.REJECT, reason="ROUTE_POOL_STATE_DRIFT"),
            hi_only.fills[0],
        ],
        balance_deltas=hi_only.balance_deltas,
        reserve_deltas=hi_only.reserve_deltas,
        lp_deltas=hi_only.lp_deltas,
    )

    ok, err = validate_settlement_strong(
        settlement=forged,
        intents=[tampered_lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "does not pin the pre-state snapshot" in err


def test_validator_rejects_route_fill_pinning_drifted_state() -> None:
    # Codex r3 coverage: a route FILL whose binding pins a DRIFTED (non-pre-
    # state) snapshot must be rejected by the fill anchor — a route may fill
    # only against its pinned pre-state snapshot, never a re-pinned current
    # state.
    import dataclasses

    from src.core.quote_receipts import pool_state_fingerprint
    from src.state.intents import Intent

    pools, balances, settlement, sanitized, _quote = _validator_fixture()

    fps = dict(sanitized.get_field("route_pool_fingerprints"))
    some_pool = next(iter(fps))
    drifted_pool = dataclasses.replace(
        pools[some_pool],
        reserve0=int(pools[some_pool].reserve0) + 100,
        reserve1=int(pools[some_pool].reserve1) + 100,
    )
    fps[some_pool] = pool_state_fingerprint(drifted_pool)
    tampered_fields = dict(sanitized.fields or {})
    tampered_fields["route_pool_fingerprints"] = fps
    tampered = Intent(
        module="TauSwap",
        version="0.1",
        kind=sanitized.kind,
        intent_id=sanitized.intent_id,
        sender_pubkey=sanitized.sender_pubkey,
        deadline=sanitized.deadline,
        fields=tampered_fields,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[tampered],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert not ok
    assert "route fill binding does not pin the pre-state snapshot" in err


def test_apply_ops_rejects_forged_non_canonical_route_winner() -> None:
    # Codex r3 coverage: the full engine path with require_settlement_match=
    # False must reject a forged op-3 settlement that fills the non-canonical
    # (higher intent_id) route and rejects the canonical winner. Exercises the
    # strong validator's must-fill discipline end-to-end through apply_ops.
    from src.core.route_settlement import resolve_route_binding_from_receipt
    from src.core.settlement import Fill, FillAction, Settlement
    from src.integration.operations import create_settlement_operation

    pools = {f"p{i}": _pool(f"p{i}") for i in (1, 2, 3)}
    pools_r1 = {pid: pools[pid] for pid in ("p1", "p2")}
    pools_r2 = {pid: pools[pid] for pid in ("p2", "p3")}
    q1 = best_route_exact_in_2hop(pools_by_id=pools_r1, asset_in="A", asset_out="B", amount_in=600)
    q2 = best_route_exact_in_2hop(pools_by_id=pools_r2, asset_in="A", asset_out="B", amount_in=600)
    assert q1 is not None and q2 is not None
    r1 = make_route_quote_receipt(kind="exact_in", quote=q1, pools_by_id=pools_r1)
    r2 = make_route_quote_receipt(kind="exact_in", quote=q2, pools_by_id=pools_r2)
    i1 = _route_intent(r1, pools_r1, sender=SENDER, nonce=1)
    i2 = _route_intent(r2, pools_r2, sender=SENDER, nonce=2)

    lo, hi = (i1, i2) if i1.intent_id < i2.intent_id else (i2, i1)
    hi_receipt = r1 if hi is i1 else r2
    hi_binding, berr = resolve_route_binding_from_receipt(hi_receipt)
    assert hi_binding is not None, berr

    balances = BalanceTable()
    balances.set(SENDER, "A", 20_000)
    state = _state(pools, balances=balances)

    hi_only = compute_settlement(
        intents=[hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={hi.intent_id: hi_binding},
    )
    assert hi_only.fills[0].action == FillAction.FILL

    forged = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(lo.intent_id, FillAction.REJECT), (hi.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=lo.intent_id, action=FillAction.REJECT, reason="ROUTE_POOL_STATE_DRIFT"),
            hi_only.fills[0],
        ],
        balance_deltas=hi_only.balance_deltas,
        reserve_deltas=hi_only.reserve_deltas,
        lp_deltas=hi_only.lp_deltas,
    )

    ops = create_signed_intent_operation(
        [
            SignedIntentEnvelope(intent=i1, quote_receipt=r1),
            SignedIntentEnvelope(intent=i2, quote_receipt=r2),
        ]
    )
    ops.update(create_settlement_operation(forged))

    res = apply_ops(
        config=DexEngineConfig(require_intent_signatures=False, require_settlement_match=False),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )
    assert not res.ok
    assert "route reject not justified" in res.error


def test_validator_accepts_justified_route_drift_reject() -> None:
    # The CANONICAL two-route outcome (lo fills, hi rejects on drift) must
    # still validate: the must-fill check has to recognize the drift as a
    # justified reject at hi's replay position.
    pools, balances, lo, lo_binding, hi, hi_binding = _two_route_shared_pool_fixture()

    canonical = compute_settlement(
        intents=[lo, hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={lo.intent_id: lo_binding, hi.intent_id: hi_binding},
    )
    by_id = {f.intent_id: f for f in canonical.fills}
    assert by_id[lo.intent_id].action == FillAction.FILL
    assert by_id[hi.intent_id].action == FillAction.REJECT

    ok, err = validate_settlement_strong(
        settlement=canonical,
        intents=[lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )
    assert ok, err


def test_validator_accepts_rejected_route_action_without_binding_fields() -> None:
    from src.state.intents import Intent, IntentKind

    pools = {"p1": _pool("p1")}
    bare = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_IN,
        intent_id="0x" + "22" * 32,
        sender_pubkey=SENDER,
        deadline=9999999999,
        fields={"nonce": 1},
    )
    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    settlement = compute_settlement(intents=[bare], pools=pools, balances=balances, lp_balances=LPTable())
    assert settlement.fills[0].action == FillAction.REJECT
    assert settlement.fills[0].reason == "ROUTE_BINDING_MISSING"

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[bare],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=False,
    )
    assert ok, err


def test_route_exact_in_captures_protocol_fee_end_to_end() -> None:
    pools, _quote, receipt = _exact_in_route_setup(
        2,
        amount_in=600,
        fee_bps=100,
    )
    intent = _route_intent(receipt, pools)
    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)
    pre_state = copy.deepcopy(state)

    res = _apply(
        state,
        [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)],
        config=_engine_config(
            protocol_fee_share_bps=5_000,
            protocol_fee_recipient_pubkey=PROTOCOL_FEE_RECIPIENT,
        ),
    )

    assert res.ok, res.error
    fill = res.settlement.fills[0]
    assert fill.protocol_fee_paid > 0
    assert (
        res.state.balances.get(PROTOCOL_FEE_RECIPIENT, "A")
        == fill.protocol_fee_paid
    )
    reserve_credit = sum(
        delta.delta_add
        for delta in res.settlement.reserve_deltas
        if delta.asset == "A"
    )
    assert reserve_credit + fill.protocol_fee_paid == fill.amount_in_filled
    _assert_asset_conservation(pre_state, res.state, ("A", "B"))


def test_route_exact_out_captures_protocol_fee_end_to_end() -> None:
    pools = {f"p{i}": _pool(f"p{i}", fee_bps=100) for i in (1, 2)}
    quote = best_route_exact_out_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_out=400,
    )
    assert quote is not None
    receipt = make_route_quote_receipt(
        kind="exact_out",
        quote=quote,
        pools_by_id=pools,
    )
    intent = _route_intent(receipt, pools)
    balances = BalanceTable()
    balances.set(SENDER, "A", 10_000)
    state = _state(pools, balances=balances)
    pre_state = copy.deepcopy(state)

    res = _apply(
        state,
        [SignedIntentEnvelope(intent=intent, quote_receipt=receipt)],
        config=_engine_config(
            protocol_fee_share_bps=5_000,
            protocol_fee_recipient_pubkey=PROTOCOL_FEE_RECIPIENT,
        ),
    )

    assert res.ok, res.error
    fill = res.settlement.fills[0]
    assert fill.protocol_fee_paid > 0
    assert (
        res.state.balances.get(PROTOCOL_FEE_RECIPIENT, "A")
        == fill.protocol_fee_paid
    )
    reserve_credit = sum(
        delta.delta_add
        for delta in res.settlement.reserve_deltas
        if delta.asset == "A"
    )
    assert reserve_credit + fill.protocol_fee_paid == fill.amount_in_filled
    _assert_asset_conservation(pre_state, res.state, ("A", "B"))


def test_validator_rejects_tampered_route_protocol_fee() -> None:
    pools, balances, settlement, sanitized, _quote = _validator_fixture(
        fee_bps=100,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=PROTOCOL_FEE_RECIPIENT,
    )
    settlement.fills[0].protocol_fee_paid += 1

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[sanitized],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=PROTOCOL_FEE_RECIPIENT,
    )

    assert not ok
    assert "route protocol_fee_paid mismatch" in err


def test_validator_rejects_tampered_route_reject_reason() -> None:
    pools, balances, lo, lo_binding, hi, hi_binding = _two_route_shared_pool_fixture()
    canonical = compute_settlement(
        intents=[lo, hi],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        route_bindings={lo.intent_id: lo_binding, hi.intent_id: hi_binding},
    )
    rejected_fill = next(
        fill for fill in canonical.fills if fill.action == FillAction.REJECT
    )
    rejected_fill.reason = "INSUFFICIENT_BALANCE"

    ok, err = validate_settlement_strong(
        settlement=canonical,
        intents=[lo, hi],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        allow_snapshot_bound_quote_bindings=True,
    )

    assert not ok
    assert "route reject reason mismatch" in err
