from __future__ import annotations

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.cpmm import swap_exact_in_with_protocol_fee
from src.core.settlement import FillAction
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

ALICE = "alice"
BOB = "bob"
TREASURY = "protocol_treasury"
ASSET0 = "0x" + "11" * 32
ASSET1 = "0x" + "22" * 32
POOL_ID = "pool"


def _pool() -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=100,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _balances() -> BalanceTable:
    balances = BalanceTable()
    balances.set(ALICE, ASSET0, 10_000)
    return balances


def _exact_in_intent() -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "01" * 32,
        sender_pubkey=ALICE,
        deadline=0,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_in": 10_000,
            "min_amount_out": 1,
            "recipient": BOB,
        },
    )


def test_compute_settlement_captures_exact_in_protocol_fee_to_treasury() -> None:
    pools = {POOL_ID: _pool()}
    balances = _balances()
    lp = LPTable()
    intent = _exact_in_intent()

    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=lp,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )

    fill = settlement.fills[0]
    assert fill.action == FillAction.FILL
    assert fill.fee_paid == 100
    assert fill.protocol_fee_paid == 50
    assert fill.amount_out_filled == 9_802

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp,
        mode="strong_proof_carrying",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )
    assert ok, err

    next_balances, next_pools, _next_lp = apply_settlement_pure(settlement, balances, pools, lp)
    assert next_balances.get(ALICE, ASSET0) == 0
    assert next_balances.get(TREASURY, ASSET0) == 50
    assert next_balances.get(BOB, ASSET1) == 9_802
    assert next_pools[POOL_ID].reserve0 == 1_009_950
    assert next_pools[POOL_ID].reserve1 == 990_198


def test_cpmm_exact_in_protocol_fee_is_deducted_from_input_reserve() -> None:
    quote = swap_exact_in_with_protocol_fee(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=100,
        protocol_fee_share_bps=5_000,
    )

    assert quote.fee_total == 100
    assert quote.protocol_fee == 50
    assert quote.lp_fee == 50
    assert quote.new_reserve_in == 1_000_000 + 10_000 - quote.protocol_fee
    assert quote.new_reserve_in == 1_009_950
    assert quote.new_reserve_out == 990_198


def test_strong_validator_rejects_exact_in_protocol_fee_without_recipient() -> None:
    pools = {POOL_ID: _pool()}
    balances = _balances()
    lp = LPTable()
    intent = _exact_in_intent()

    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=lp,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp,
        mode="strong_proof_carrying",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=None,
    )
    assert ok is False
    assert err is not None and "protocol_fee_recipient_pubkey is required" in err


def test_strong_validator_rejects_numeric_string_protocol_fee_paid() -> None:
    pools = {POOL_ID: _pool()}
    balances = _balances()
    lp = LPTable()
    intent = _exact_in_intent()
    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=lp,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )
    settlement.fills[0].protocol_fee_paid = str(settlement.fills[0].protocol_fee_paid)

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp,
        mode="strong_proof_carrying",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )

    assert ok is False
    assert err == f"swap protocol_fee_paid must be int for intent_id={intent.intent_id}"


def test_compute_settlement_captures_exact_out_protocol_fee_to_treasury() -> None:
    pools = {POOL_ID: _pool()}
    balances = _balances()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id="0x" + "02" * 32,
        sender_pubkey=ALICE,
        deadline=0,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_out": 1_000,
            "max_amount_in": 10_000,
            "recipient": BOB,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )

    fill = settlement.fills[0]
    assert fill.action == FillAction.FILL
    assert fill.amount_in_filled == 1_013
    assert fill.amount_out_filled == 1_000
    assert fill.fee_paid == 11
    assert fill.protocol_fee_paid == 5

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )
    assert ok, err

    next_balances, next_pools, _next_lp = apply_settlement_pure(settlement, balances, pools, LPTable())
    assert next_balances.get(ALICE, ASSET0) == 8_987
    assert next_balances.get(TREASURY, ASSET0) == 5
    assert next_balances.get(BOB, ASSET1) == 1_000
    assert next_pools[POOL_ID].reserve0 == 1_001_008
    assert next_pools[POOL_ID].reserve1 == 999_000


def test_strong_validator_rejects_exact_out_protocol_fee_without_recipient() -> None:
    pools = {POOL_ID: _pool()}
    balances = _balances()
    lp = LPTable()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id="0x" + "03" * 32,
        sender_pubkey=ALICE,
        deadline=0,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_out": 1_000,
            "max_amount_in": 10_000,
            "recipient": BOB,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=lp,
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=TREASURY,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp,
        mode="strong_proof_carrying",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=None,
    )
    assert ok is False
    assert err is not None and "protocol_fee_recipient_pubkey is required" in err
