# [TESTER] v1

from __future__ import annotations

from dataclasses import replace

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexConfig, DexState, step_with_candidate_settlement
from src.core.liquidity import create_pool
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _single_swap_setup(*, amount_in: int = 1000, nonce: int = 1) -> tuple[DexState, Intent, str, str, str, str]:
    sender = "0x" + "47" * 48
    asset0 = "0x" + "47" * 32
    asset1 = "0x" + "48" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=sender,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(sender, asset0, 10_000_000)
    balances.set(sender, asset1, 0)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(47),
        sender_pubkey=sender,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": int(amount_in),
            "min_amount_out": 1,
            "nonce": int(nonce),
        },
    )
    return state, intent, pool_id, sender, asset0, asset1


def _candidate_for(state: DexState, intent: Intent):
    return compute_settlement(
        intents=[intent],
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering="greedy_ab_refined",
    )


def test_candidate_settlement_rejects_nonce_replay_before_auth_shape_side_effects() -> None:
    state, intent, _pool_id, sender, asset0, asset1 = _single_swap_setup()
    nonces = NonceTable()
    nonces.set_last(sender, 1)
    state = replace(state, nonces=nonces)
    candidate = _candidate_for(state, intent)

    result = step_with_candidate_settlement(
        DexConfig(settlement_validation="strong_replay"),
        state,
        [intent],
        candidate_settlement=candidate,
    )

    assert not result.ok
    assert result.error == "nonce sequence invalid"
    assert result.state is None
    assert result.effects is None
    assert state.nonces.get_last(sender) == 1
    assert state.balances.get(sender, asset0) == 10_000_000
    assert state.balances.get(sender, asset1) == 0


def test_candidate_settlement_rejects_auth_shape_projection_amount_drift() -> None:
    state, producer_intent, _pool_id, sender, asset0, asset1 = _single_swap_setup(amount_in=1000)
    candidate = _candidate_for(state, producer_intent)
    consumer_intent = replace(
        producer_intent,
        fields={**dict(producer_intent.fields or {}), "amount_in": 1001},
    )

    result = step_with_candidate_settlement(
        DexConfig(settlement_validation="strong_replay"),
        state,
        [consumer_intent],
        candidate_settlement=candidate,
    )

    assert not result.ok
    assert result.error == f"swap amount_in_filled mismatch for intent_id={producer_intent.intent_id}"
    assert result.state is None
    assert result.effects is None
    assert state.nonces.get_last(sender) == 0
    assert state.balances.get(sender, asset0) == 10_000_000
    assert state.balances.get(sender, asset1) == 0


def test_candidate_settlement_rejects_raw_quote_transport_without_engine_witness() -> None:
    state, intent, _pool_id, sender, asset0, asset1 = _single_swap_setup()
    intent = replace(
        intent,
        fields={
            **dict(intent.fields or {}),
            "quote_receipt_hash": "0x" + "49" * 32,
            "quote_receipt_leg_index": 0,
        },
    )
    candidate = _candidate_for(state, intent)

    result = step_with_candidate_settlement(
        DexConfig(settlement_validation="strong_replay"),
        state,
        [intent],
        candidate_settlement=candidate,
    )

    assert not result.ok
    assert result.error is not None
    assert "quote receipt transport metadata requires validated engine witness" in result.error
    assert result.state is None
    assert result.effects is None
    assert state.nonces.get_last(sender) == 0
    assert state.balances.get(sender, asset0) == 10_000_000
    assert state.balances.get(sender, asset1) == 0


def test_candidate_settlement_rejects_snapshot_fingerprint_external_boundary_mismatch() -> None:
    state, intent, _pool_id, sender, asset0, asset1 = _single_swap_setup()
    intent = replace(
        intent,
        fields={**dict(intent.fields or {}), "quote_pool_fingerprint": "stale-pool-fingerprint"},
    )
    candidate = _candidate_for(state, intent)

    result = step_with_candidate_settlement(
        DexConfig(settlement_validation="strong_replay", allow_snapshot_bound_quote_bindings=True),
        state,
        [intent],
        candidate_settlement=candidate,
    )

    assert not result.ok
    assert result.error is not None
    assert "quote receipt pool snapshot mismatch" in result.error
    assert result.state is None
    assert result.effects is None
    assert state.nonces.get_last(sender) == 0
    assert state.balances.get(sender, asset0) == 10_000_000
    assert state.balances.get(sender, asset1) == 0
