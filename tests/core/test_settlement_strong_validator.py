# [TESTER] v1

from __future__ import annotations

from dataclasses import replace

import src.core.settlement_strong_validator as strong_validator
from src.core.batch_clearing import compute_settlement, validate_settlement
from src.core.dex import DexConfig, DexState
from src.core.dex import step as dex_step
from src.core.liquidity import create_pool
from src.core.quote_receipts import pool_state_fingerprint
from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _setup_liquidity_context() -> tuple[str, str, str, str, PoolState, BalanceTable, LPTable]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    lp_balances = LPTable()
    lp_balances.set(pk, pool_id, lp_minted)
    lp_balances.set("0x" + "00" * 48, pool_id, pool.lp_supply - lp_minted)
    return pk, asset0, asset1, pool_id, pool, balances, lp_balances


def _setup_swap_context() -> tuple[str, str, str, str, PoolState, BalanceTable, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(900),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    return pk, asset0, asset1, pool_id, pool, balances, intent, settlement


def _setup_create_pool_context() -> tuple[str, str, str, BalanceTable, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(901),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
        },
    )
    settlement = compute_settlement([intent], {}, balances, LPTable())
    return pk, asset0, asset1, balances, intent, settlement


def _setup_swap_exact_out_context(
    *, reverse: bool = False
) -> tuple[str, str, str, str, PoolState, BalanceTable, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    if reverse:
        swap_asset_in = asset1
        swap_asset_out = asset0
    else:
        swap_asset_in = asset0
        swap_asset_out = asset1

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(904 if not reverse else 905),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": swap_asset_in,
            "asset_out": swap_asset_out,
            "amount_out": 1_000,
            "max_amount_in": 10_000,
        },
    )
    settlement = compute_settlement(
        [intent],
        {pool_id: pool},
        balances,
        LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    return pk, asset0, asset1, pool_id, pool, balances, intent, settlement


def _setup_add_liquidity_context() -> tuple[str, str, str, str, PoolState, BalanceTable, LPTable, Intent, Settlement]:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(906),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    return pk, asset0, asset1, pool_id, pool, balances, lp_balances, intent, settlement


def _setup_remove_liquidity_context() -> tuple[str, str, str, str, PoolState, BalanceTable, LPTable, Intent, Settlement]:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(907),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    return pk, asset0, asset1, pool_id, pool, balances, lp_balances, intent, settlement


def test_quote_binding_error_without_context_returns_reason() -> None:
    assert strong_validator._quote_binding_error("plain reason") == "plain reason"


def test_validate_settlement_strong_fail_closed_on_internal_crash_with_detail(monkeypatch) -> None:
    def _boom(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError("bad\nnews")

    monkeypatch.setattr(strong_validator, "_validate_settlement_strong_impl", _boom)
    ok, err = strong_validator.validate_settlement_strong(
        settlement=Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        ),
        intents=[],
        pre_balances=BalanceTable(),
        pre_pools={},
        pre_lp_balances=LPTable(),
    )
    assert ok is False
    assert err == "strong validator crashed: RuntimeError: bad news"


def test_validate_settlement_strong_fail_closed_on_internal_crash_without_detail(monkeypatch) -> None:
    def _boom(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError()

    monkeypatch.setattr(strong_validator, "_validate_settlement_strong_impl", _boom)
    ok, err = strong_validator.validate_settlement_strong(
        settlement=Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        ),
        intents=[],
        pre_balances=BalanceTable(),
        pre_pools={},
        pre_lp_balances=LPTable(),
    )
    assert ok is False
    assert err == "strong validator crashed: RuntimeError"


def test_validate_settlement_strong_truncates_long_internal_crash_detail(monkeypatch) -> None:
    def _boom(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError("x" * 400)

    monkeypatch.setattr(strong_validator, "_validate_settlement_strong_impl", _boom)
    ok, err = strong_validator.validate_settlement_strong(
        settlement=Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        ),
        intents=[],
        pre_balances=BalanceTable(),
        pre_pools={},
        pre_lp_balances=LPTable(),
    )
    assert ok is False
    assert err is not None
    assert err.startswith("strong validator crashed: RuntimeError: ")
    assert len(err) == len("strong validator crashed: RuntimeError: ") + 200


def test_aggregate_helpers_drop_zero_entries() -> None:
    aggregated_balance = strong_validator._aggregate_balance_deltas(
        [
            BalanceDelta(pubkey="0x" + "11" * 48, asset="0x" + "01" * 32, delta_add=0, delta_sub=0),
            BalanceDelta(pubkey="0x" + "11" * 48, asset="0x" + "02" * 32, delta_add=5, delta_sub=0),
        ]
    )
    assert aggregated_balance == [
        BalanceDelta(pubkey="0x" + "11" * 48, asset="0x" + "02" * 32, delta_add=5, delta_sub=0)
    ]

    aggregated_reserve = strong_validator._aggregate_reserve_deltas(
        [
            ReserveDelta(pool_id=_iid(1), asset="0x" + "01" * 32, delta_add=0, delta_sub=0),
            ReserveDelta(pool_id=_iid(1), asset="0x" + "02" * 32, delta_add=0, delta_sub=7),
        ]
    )
    assert aggregated_reserve == [
        ReserveDelta(pool_id=_iid(1), asset="0x" + "02" * 32, delta_add=0, delta_sub=7)
    ]

    aggregated_lp = strong_validator._aggregate_lp_deltas(
        [
            LPDelta(pubkey="0x" + "11" * 48, pool_id=_iid(2), delta_add=0, delta_sub=0),
            LPDelta(pubkey="0x" + "22" * 48, pool_id=_iid(2), delta_add=9, delta_sub=0),
        ]
    )
    assert aggregated_lp == [
        LPDelta(pubkey="0x" + "22" * 48, pool_id=_iid(2), delta_add=9, delta_sub=0)
    ]


def test_check_canonical_deltas_rejects_invalid_balance_scalar_fields() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=_iid(1), asset=_iid(2), delta_add=False, delta_sub=1)],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "balance_deltas contains invalid delta_add"

    settlement.balance_deltas = [BalanceDelta(pubkey=_iid(1), asset=_iid(2), delta_add=1, delta_sub=False)]
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "balance_deltas contains invalid delta_sub"


def test_check_canonical_deltas_rejects_invalid_reserve_scalar_fields() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=_iid(1), asset=_iid(2), delta_add=False, delta_sub=1)],
        lp_deltas=[],
        events=None,
    )
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "reserve_deltas contains invalid delta_add"

    settlement.reserve_deltas = [ReserveDelta(pool_id=_iid(1), asset=_iid(2), delta_add=1, delta_sub=False)]
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "reserve_deltas contains invalid delta_sub"


def test_check_canonical_deltas_rejects_invalid_lp_scalar_fields() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=_iid(1), pool_id=_iid(2), delta_add=False, delta_sub=1)],
        events=None,
    )
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "lp_deltas contains invalid delta_add"

    settlement.lp_deltas = [LPDelta(pubkey=_iid(1), pool_id=_iid(2), delta_add=1, delta_sub=False)]
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "lp_deltas contains invalid delta_sub"


def test_strong_validator_allows_reject_without_fill_details() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, _settlement = _setup_swap_context()
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.REJECT)],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_strong_validator_rejects_unsupported_validation_mode() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="bad_mode",
    )
    assert ok is False
    assert err == "unsupported validation mode: 'bad_mode'"


def test_strong_validator_rejects_duplicate_input_intent_ids() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent, intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "duplicate intent_id in input intents"


def test_strong_validator_rejects_included_intents_mismatch() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.included_intents = [(_iid(999), FillAction.REJECT)]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"settlement included_intents mismatch: missing=['{intent.intent_id}'] extra=['{_iid(999)}']"


def test_strong_validator_rejects_duplicate_included_intents() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.included_intents = [
        (intent.intent_id, FillAction.FILL),
        (intent.intent_id, FillAction.REJECT),
    ]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement included_intents contains duplicate intent_id entries"


def test_strong_validator_rejects_duplicate_fill_ids() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills = [settlement.fills[0], settlement.fills[0]]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement fills contains duplicate intent_id entries"


def test_strong_validator_rejects_extra_fill_id() -> None:
    _pk, asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills.append(
        Fill(
            intent_id=_iid(998),
            action=FillAction.REJECT,
            reason="UNSUPPORTED",
            amount_in_filled=0,
            amount_out_filled=0,
            fee_paid=0,
        )
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    del asset0
    assert ok is False
    assert err == f"settlement fills contains intent_ids not in input intents: ['{_iid(998)}']"


def test_strong_validator_rejects_missing_fill_for_filled_intent() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills = []
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing Fill for filled intent_id: {intent.intent_id}"


def test_strong_validator_rejects_fill_action_mismatch() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills[0].action = FillAction.REJECT
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"Fill.action mismatch for intent_id={intent.intent_id}: FillAction.REJECT != FillAction.FILL"


def test_strong_validator_rejects_invalid_recipient() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "recipient": ""},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid recipient for intent_id={intent.intent_id}"


def test_strong_validator_rejects_invalid_quote_receipt_hash() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "quote_receipt_hash": ""},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "invalid quote_receipt_hash" in err


def test_strong_validator_rejects_missing_quote_pool_fingerprint() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "quote_pool_fingerprint": ""},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "missing quote_pool_fingerprint" in err


def test_strong_validator_rejects_missing_pool_id() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    fields = dict(intent.fields or {})
    del fields["pool_id"]
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields=fields,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing pool_id for intent_id={intent.intent_id}"


def test_strong_validator_rejects_pool_not_found() -> None:
    _pk, _asset0, _asset1, _pool_id, _pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not found for intent_id={intent.intent_id}: {intent.get_field('pool_id')}"


def test_strong_validator_rejects_invalid_asset_ids() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "asset_out": 7},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid asset_in/out for intent_id={intent.intent_id}"


def test_strong_validator_rejects_create_pool_duplicate_existing_pool_id() -> None:
    pk, asset0, asset1, balances, intent, settlement = _setup_create_pool_context()
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL duplicates existing pool_id={pool_id}"


def test_strong_validator_rejects_create_pool_fill_amount0_mismatch() -> None:
    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.fills[0].amount0_used += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.amount0_used mismatch for intent_id={intent.intent_id}"


def test_strong_validator_rejects_create_pool_reserve_only_donation_witness() -> None:
    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.reserve_deltas[0].delta_add += 1_000_000
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas mismatch vs replay"


def test_strong_validator_rejects_create_pool_apply_error_for_insufficient_balance() -> None:
    _pk, asset0, asset1, _balances, intent, settlement = _setup_create_pool_context()
    balances = BalanceTable()
    balances.set(intent.sender_pubkey, asset0, 1)
    balances.set(intent.sender_pubkey, asset1, 1)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"CREATE_POOL balance/LP apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_swap_on_inactive_pool() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    inactive_pool = replace(pool, status=PoolStatus.FROZEN)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: inactive_pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"


def test_strong_validator_rejects_swap_asset_mismatch() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "asset_out": intent.get_field("asset_in")},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap asset mismatch for intent_id={intent.intent_id}"


def test_strong_validator_rejects_add_liquidity_on_inactive_pool() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(902),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: replace(pool, status=PoolStatus.FROZEN)},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"


def test_strong_validator_rejects_remove_liquidity_on_inactive_pool() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(903),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: replace(pool, status=PoolStatus.FROZEN)},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"

def test_legacy_validate_allows_k_decrease_but_strong_rejects() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )

    # Malicious settlement: drains too much output from the pool (k decreases),
    # but keeps reserves non-negative and passes pure conservation checks.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=100,
                amount_out_filled=200,  # impossible under CPMM reserves=(1000,1000) with fee_bps=30
                fee_paid=1,  # any non-negative value; legacy doesn't check
                reserve_in_before=1_000,
                reserve_out_before=1_000,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[
            ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=100, delta_sub=0),
            ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=0, delta_sub=200),
        ],
        lp_deltas=[],
        events=None,
    )

    ok_legacy, err_legacy = validate_settlement(
        settlement=settlement,
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
    )
    assert ok_legacy is True, err_legacy

    ok_strong, err_strong = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_strong is False
    assert err_strong is not None


def test_dex_step_preserves_created_pool_curve_config() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, expected_pool, _lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
        curve_tag="CUBIC_SUM_V1",
        curve_params={"p": 2, "q": 1},
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    config = DexConfig()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "amount0": 2_000_000,
                "amount1": 2_000_000,
                "curve_tag": "CUBIC_SUM_V1",
                "curve_params": {"p": 2, "q": 1},
                "nonce": 1,
            },
        )
    ]

    res = dex_step(config, state, intents)
    assert res.ok, res.error
    assert res.state is not None
    assert pool_id in res.state.pools

    got_pool = res.state.pools[pool_id]
    assert got_pool.curve_tag == expected_pool.curve_tag
    assert got_pool.curve_params == expected_pool.curve_params


def test_strong_proof_carrying_requires_swap_reserve_witnesses() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(3),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 10,
            "max_amount_in": 1_000,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    assert len(settlement.fills) == 1

    fill = settlement.fills[0]
    assert fill.reserve_in_before is not None
    assert fill.reserve_out_before is not None
    witness_in = int(fill.reserve_in_before)
    witness_out = int(fill.reserve_out_before)

    ok_replay, err_replay = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_replay is True, err_replay

    # BVA over witness presence/mismatch:
    # - missing witness: proof-carrying must reject
    # - correct witness: proof-carrying must accept
    # - off-by-one witness: proof-carrying must reject

    fill.reserve_in_before = None
    fill.reserve_out_before = None
    ok_pc, err_pc = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc is False
    assert err_pc is not None

    fill.reserve_in_before = witness_in
    fill.reserve_out_before = witness_out
    ok_pc2, err_pc2 = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc2 is True, err_pc2

    fill.reserve_in_before = witness_in + 1
    fill.reserve_out_before = witness_out
    ok_pc3, err_pc3 = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc3 is False
    assert err_pc3 is not None


def test_strong_validator_rejects_nonconserving_cow_netted_settlement() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(10),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )

    # Malicious settlement: marks a swap as COW_NETTED but does not include any
    # counterparty transfer. This would violate asset conservation if accepted.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=200,  # created-from-nothing if no offsetting debit exists
                fee_paid=0,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok_strong, err_strong = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_strong is False
    assert err_strong is not None


def test_strong_validator_accepts_exact_reciprocal_cow_netted_pair() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk0, asset0, 1_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 1_000)
    intent0 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(920),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 50,
        },
    )
    intent1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(921),
        sender_pubkey=pk1,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset1,
            "asset_out": asset0,
            "amount_in": 50,
            "min_amount_out": 100,
        },
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent0.intent_id, FillAction.FILL), (intent1.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent0.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=50,
                fee_paid=0,
            ),
            Fill(
                intent_id=intent1.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=50,
                amount_out_filled=100,
                fee_paid=0,
            ),
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk0, asset=asset1, delta_add=50, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset0, delta_add=100, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=0, delta_sub=50),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent0, intent1],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )

    assert ok is True, err
    assert err is None


def test_strong_validator_accepts_multiple_disjoint_cow_netted_pairs() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    pk2 = "0x" + "33" * 48
    pk3 = "0x" + "44" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk0, asset0, 1_000)
    balances.set(pk1, asset1, 1_000)
    balances.set(pk2, asset0, 1_000)
    balances.set(pk3, asset1, 1_000)

    rows = [
        (_iid(922), pk0, asset0, asset1, 100, 50),
        (_iid(923), pk1, asset1, asset0, 50, 100),
        (_iid(924), pk2, asset0, asset1, 17, 23),
        (_iid(925), pk3, asset1, asset0, 23, 17),
    ]
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=intent_id,
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": amount_out,
            },
        )
        for intent_id, sender, asset_in, asset_out, amount_in, amount_out in rows
    ]
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL) for intent in intents],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=amount_in,
                amount_out_filled=amount_out,
                fee_paid=0,
            )
            for intent, (
                _intent_id,
                _sender,
                _asset_in,
                _asset_out,
                amount_in,
                amount_out,
            ) in zip(intents, rows, strict=True)
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk0, asset=asset1, delta_add=50, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset0, delta_add=100, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=0, delta_sub=50),
            BalanceDelta(pubkey=pk2, asset=asset0, delta_add=0, delta_sub=17),
            BalanceDelta(pubkey=pk2, asset=asset1, delta_add=23, delta_sub=0),
            BalanceDelta(pubkey=pk3, asset=asset0, delta_add=17, delta_sub=0),
            BalanceDelta(pubkey=pk3, asset=asset1, delta_add=0, delta_sub=23),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=intents,
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )

    assert ok is True, err
    assert err is None


def test_strong_validator_rejects_ambiguous_and_nonreciprocal_cow_pairs() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    pk2 = "0x" + "33" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    other_pool_id = compute_pool_id(asset0, asset1, 31, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    other_pool_state = replace(pool_state, pool_id=other_pool_id, fee_bps=31)
    balances = BalanceTable()
    balances.set(pk0, asset0, 1_000)
    balances.set(pk1, asset1, 1_000)
    balances.set(pk2, asset1, 1_000)

    def _intent(
        n: int,
        sender: str,
        pool: str,
        asset_in: str,
        asset_out: str,
        amount_in: int,
        min_out: int,
    ) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(n),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_out,
            },
        )

    def _settlement(rows: list[tuple[Intent, int, int]]) -> Settlement:
        return Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[(intent.intent_id, FillAction.FILL) for intent, _amount_in, _amount_out in rows],
            fills=[
                Fill(
                    intent_id=intent.intent_id,
                    action=FillAction.FILL,
                    reason="COW_NETTED",
                    amount_in_filled=amount_in,
                    amount_out_filled=amount_out,
                    fee_paid=0,
                )
                for intent, amount_in, amount_out in rows
            ],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        )

    same_direction = [
        (_intent(930, pk0, pool_id, asset0, asset1, 100, 50), 100, 50),
        (_intent(931, pk1, pool_id, asset0, asset1, 50, 100), 50, 100),
    ]
    ok, err = validate_settlement_strong(
        settlement=_settlement(same_direction),
        intents=[row[0] for row in same_direction],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "exactly one reciprocal counterparty" in err

    cross_pool = [
        (_intent(932, pk0, pool_id, asset0, asset1, 100, 50), 100, 50),
        (_intent(933, pk1, other_pool_id, asset1, asset0, 50, 100), 50, 100),
    ]
    ok, err = validate_settlement_strong(
        settlement=_settlement(cross_pool),
        intents=[row[0] for row in cross_pool],
        pre_balances=balances,
        pre_pools={pool_id: pool_state, other_pool_id: other_pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "exactly one reciprocal counterparty" in err

    mismatched = [
        (_intent(934, pk0, pool_id, asset0, asset1, 100, 40), 100, 49),
        (_intent(935, pk1, pool_id, asset1, asset0, 50, 100), 50, 100),
    ]
    ok, err = validate_settlement_strong(
        settlement=_settlement(mismatched),
        intents=[row[0] for row in mismatched],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "exactly one reciprocal counterparty" in err

    ambiguous = [
        (_intent(936, pk0, pool_id, asset0, asset1, 100, 50), 100, 50),
        (_intent(937, pk1, pool_id, asset1, asset0, 50, 100), 50, 100),
        (_intent(938, pk2, pool_id, asset1, asset0, 50, 100), 50, 100),
    ]
    ok, err = validate_settlement_strong(
        settlement=_settlement(ambiguous),
        intents=[row[0] for row in ambiguous],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "matches=[" in err


def test_strong_validator_rejects_stale_quote_receipt_pool_fingerprint() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    quoted_pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    drifted_pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_001,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(20),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_pool_fingerprint": pool_state_fingerprint(quoted_pool),
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: drifted_pool},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: drifted_pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_snapshot_bound_quote_bindings=True,
    )
    assert ok is False
    assert err is not None
    assert "quote receipt pool snapshot mismatch" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert f"quote_pool_fingerprint='{pool_state_fingerprint(quoted_pool)}'" in err
    assert "actual_pool_fingerprint=" in err


def test_strong_validator_rejects_quote_receipt_binding_on_non_swap_intent() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(21),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
            "quote_receipt_hash": "0xdeadbeef",
            "quote_pool_fingerprint": "not-applicable",
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt binding only supported for swap intents" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert "intent_kind='CREATE_POOL'" in err


def test_strong_validator_rejects_quote_receipt_leg_index_without_hash() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(22),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_receipt_leg_index": 0,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert "strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation" in err


def test_strong_validator_rejects_invalid_quote_receipt_leg_index() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(23),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xdeadbeef",
            "quote_pool_fingerprint": pool_state_fingerprint(pool_state),
            "quote_receipt_leg_index": -1,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "invalid quote_receipt_leg_index" in err
    assert f"intent_id='{intent.intent_id}'" in err


def test_strong_validator_rejects_unsanitized_quote_receipt_hash_without_engine_witness() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(24),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xdeadbeef",
            "quote_pool_fingerprint": pool_state_fingerprint(pool_state),
            "quote_receipt_leg_index": 0,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert "strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation" in err


def test_strong_validator_rejects_duplicate_balance_delta_keys() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(30),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1000,
            "min_amount_out": 1,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    first_delta = settlement.balance_deltas[0]
    settlement.balance_deltas = [
        BalanceDelta(
            pubkey=first_delta.pubkey,
            asset=first_delta.asset,
            delta_add=first_delta.delta_add,
            delta_sub=400,
        ),
        BalanceDelta(
            pubkey=first_delta.pubkey,
            asset=first_delta.asset,
            delta_add=0,
            delta_sub=first_delta.delta_sub - 400,
        ),
        *settlement.balance_deltas[1:],
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas contains duplicate keys"


def test_strong_validator_rejects_zero_delta_entry() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(31),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1000,
            "min_amount_out": 1,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    settlement.balance_deltas.append(
        BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=0)
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas contains a zero entry"


def test_strong_validator_rejects_stringly_typed_create_pool_amounts() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    valid_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(40),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
        },
    )

    settlement = compute_settlement([valid_intent], {}, balances, LPTable())
    ok_valid, err_valid = validate_settlement_strong(
        settlement=settlement,
        intents=[valid_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_valid is True, err_valid

    malformed_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=valid_intent.intent_id,
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": "2000000",
            "amount1": 2_000_000,
        },
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL amount0 for intent_id={valid_intent.intent_id}"


def test_strong_validator_rejects_stringly_typed_add_liquidity_amounts() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()

    valid_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(41),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([valid_intent], {pool_id: pool}, balances, lp_balances)
    ok_valid, err_valid = validate_settlement_strong(
        settlement=settlement,
        intents=[valid_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok_valid is True, err_valid

    malformed_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=valid_intent.intent_id,
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": "100000",
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount0_desired for intent_id={valid_intent.intent_id}"


def test_strong_validator_rejects_stringly_typed_remove_liquidity_amounts() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    del asset0
    del asset1

    valid_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(42),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([valid_intent], {pool_id: pool}, balances, lp_balances)
    ok_valid, err_valid = validate_settlement_strong(
        settlement=settlement,
        intents=[valid_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok_valid is True, err_valid

    malformed_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=valid_intent.intent_id,
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": "1000",
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid lp_amount for intent_id={valid_intent.intent_id}"


def test_strong_validator_rejects_duplicate_reserve_delta_keys() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    del asset0
    del asset1

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(43),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    first_delta = settlement.reserve_deltas[0]
    settlement.reserve_deltas = [
        ReserveDelta(
            pool_id=first_delta.pool_id,
            asset=first_delta.asset,
            delta_add=first_delta.delta_add // 2,
            delta_sub=0,
        ),
        ReserveDelta(
            pool_id=first_delta.pool_id,
            asset=first_delta.asset,
            delta_add=first_delta.delta_add - (first_delta.delta_add // 2),
            delta_sub=0,
        ),
        *settlement.reserve_deltas[1:],
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas contains duplicate keys"


def test_strong_validator_rejects_duplicate_lp_delta_keys() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    del asset0
    del asset1

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(44),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    first_delta = settlement.lp_deltas[0]
    settlement.lp_deltas = [
        LPDelta(
            pubkey=first_delta.pubkey,
            pool_id=first_delta.pool_id,
            delta_add=first_delta.delta_add // 2,
            delta_sub=0,
        ),
        LPDelta(
            pubkey=first_delta.pubkey,
            pool_id=first_delta.pool_id,
            delta_add=first_delta.delta_add - (first_delta.delta_add // 2),
            delta_sub=0,
        ),
        *settlement.lp_deltas[1:],
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas contains duplicate keys"


def test_strong_validator_accepts_reverse_direction_swap_exact_in() -> None:
    pk, asset0, asset1, pool_id, pool, balances, _intent, _settlement = _setup_swap_context()
    reverse_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(908),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset1,
            "asset_out": asset0,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([reverse_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[reverse_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True, err


def test_strong_validator_accepts_reverse_direction_swap_exact_out() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_exact_out_context(reverse=True)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True, err


def test_strong_validator_rejects_exact_in_field_kernel_and_apply_failures(monkeypatch) -> None:
    _pk, asset0, asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()

    invalid_amount_intent = replace(intent, fields={**intent.fields, "amount_in": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount_in for intent_id={intent.intent_id}"

    invalid_min_out_intent = replace(intent, fields={**intent.fields, "min_amount_out": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_min_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid min_amount_out for intent_id={intent.intent_id}"

    amount_in_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    amount_in_mismatch.fills[0].amount_in_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_in_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_in_filled mismatch for intent_id={intent.intent_id}"

    def _boom_exact_in(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("boom")

    monkeypatch.setattr(strong_validator, "swap_exact_in_for_pool", _boom_exact_in)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap_exact_in kernel error for intent_id={intent.intent_id}:")
    monkeypatch.undo()

    amount_out_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    amount_out_mismatch.fills[0].amount_out_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_out_filled mismatch for intent_id={intent.intent_id}"

    slippage_intent = replace(
        intent,
        fields={**intent.fields, "min_amount_out": int(settlement.fills[0].amount_out_filled or 0) + 1},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[slippage_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap slippage for intent_id={intent.intent_id}"

    fee_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    fee_mismatch.fills[0].fee_paid += 1
    ok, err = validate_settlement_strong(
        settlement=fee_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={intent.intent_id}"

    low_balances = BalanceTable()
    low_balances.set(intent.sender_pubkey, asset0, 1)
    low_balances.set(intent.sender_pubkey, asset1, 0)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_exact_out_field_kernel_and_apply_failures(monkeypatch) -> None:
    _pk, asset0, asset1, pool_id, pool, balances, intent, settlement = _setup_swap_exact_out_context()

    invalid_amount_out_intent = replace(intent, fields={**intent.fields, "amount_out": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount_out for intent_id={intent.intent_id}"

    invalid_max_in_intent = replace(intent, fields={**intent.fields, "max_amount_in": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_max_in_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid max_amount_in for intent_id={intent.intent_id}"

    amount_out_mismatch = compute_settlement(
        [intent], {pool_id: pool}, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    amount_out_mismatch.fills[0].amount_out_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_out_filled mismatch for intent_id={intent.intent_id}"

    def _boom_exact_out(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("boom")

    monkeypatch.setattr(strong_validator, "swap_exact_out_for_pool", _boom_exact_out)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap_exact_out kernel error for intent_id={intent.intent_id}:")
    monkeypatch.undo()

    amount_in_mismatch = compute_settlement(
        [intent], {pool_id: pool}, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    amount_in_mismatch.fills[0].amount_in_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_in_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_in_filled mismatch for intent_id={intent.intent_id}"

    slippage_intent = replace(intent, fields={**intent.fields, "max_amount_in": 1})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[slippage_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap slippage for intent_id={intent.intent_id}"

    fee_mismatch = compute_settlement(
        [intent], {pool_id: pool}, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    fee_mismatch.fills[0].fee_paid += 1
    ok, err = validate_settlement_strong(
        settlement=fee_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={intent.intent_id}"

    low_balances = BalanceTable()
    low_balances.set(intent.sender_pubkey, asset0, 1)
    low_balances.set(intent.sender_pubkey, asset1, 0)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_create_pool_field_and_fill_failures() -> None:
    _pk, asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()

    missing_field_intent = replace(intent, fields={k: v for k, v in intent.fields.items() if k != "amount1"})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[missing_field_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing CREATE_POOL fields for intent_id={intent.intent_id}"

    invalid_asset_intent = replace(intent, fields={**intent.fields, "asset1": 7})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_asset_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL asset ids for intent_id={intent.intent_id}"

    invalid_fee_intent = replace(intent, fields={**intent.fields, "fee_bps": 10_001})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_fee_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL fee_bps for intent_id={intent.intent_id}"

    invalid_amount1_intent = replace(intent, fields={**intent.fields, "amount1": 0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL amount1 for intent_id={intent.intent_id}"

    invalid_created_at_intent = replace(intent, fields={**intent.fields, "created_at": -1})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_created_at_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL created_at for intent_id={intent.intent_id}"

    computation_error_intent = replace(intent, fields={**intent.fields, "asset1": asset0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[computation_error_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"CREATE_POOL computation error for intent_id={intent.intent_id}:")

    amount1_mismatch = compute_settlement([intent], {}, balances, LPTable())
    amount1_mismatch.fills[0].amount1_used += 1
    ok, err = validate_settlement_strong(
        settlement=amount1_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.amount1_used mismatch for intent_id={intent.intent_id}"

    lp_minted_mismatch = compute_settlement([intent], {}, balances, LPTable())
    lp_minted_mismatch.fills[0].lp_minted += 1
    ok, err = validate_settlement_strong(
        settlement=lp_minted_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.lp_minted mismatch for intent_id={intent.intent_id}"


def test_strong_validator_rejects_add_liquidity_field_fill_and_apply_failures() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()

    missing_field_intent = replace(intent, fields={k: v for k, v in intent.fields.items() if k != "amount1_desired"})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[missing_field_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing ADD_LIQUIDITY fields for intent_id={intent.intent_id}"

    invalid_amount1_intent = replace(intent, fields={**intent.fields, "amount1_desired": 0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount1_desired for intent_id={intent.intent_id}"

    invalid_amount0_min_intent = replace(intent, fields={**intent.fields, "amount0_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount0_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount0_min for intent_id={intent.intent_id}"

    invalid_amount1_min_intent = replace(intent, fields={**intent.fields, "amount1_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount1_min for intent_id={intent.intent_id}"

    computation_error_intent = replace(intent, fields={**intent.fields, "amount0_min": intent.get_field("amount0_desired") + 1})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[computation_error_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"ADD_LIQUIDITY computation error for intent_id={intent.intent_id}:")

    amount0_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount0_mismatch.fills[0].amount0_used += 1
    ok, err = validate_settlement_strong(
        settlement=amount0_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={intent.intent_id}"

    amount1_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount1_mismatch.fills[0].amount1_used += 1
    ok, err = validate_settlement_strong(
        settlement=amount1_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={intent.intent_id}"

    lp_minted_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    lp_minted_mismatch.fills[0].lp_minted += 1
    ok, err = validate_settlement_strong(
        settlement=lp_minted_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={intent.intent_id}"

    low_balances = BalanceTable()
    low_balances.set(pk, pool.asset0, 1)
    low_balances.set(pk, pool.asset1, 1)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"ADD_LIQUIDITY apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_remove_liquidity_field_fill_and_apply_failures() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_remove_liquidity_context()

    missing_lp_amount_intent = replace(intent, fields={k: v for k, v in intent.fields.items() if k != "lp_amount"})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[missing_lp_amount_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent.intent_id}"

    invalid_amount0_min_intent = replace(intent, fields={**intent.fields, "amount0_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount0_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount0_min for intent_id={intent.intent_id}"

    invalid_amount1_min_intent = replace(intent, fields={**intent.fields, "amount1_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount1_min for intent_id={intent.intent_id}"

    computation_error_intent = replace(intent, fields={**intent.fields, "amount0_min": pool.reserve0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[computation_error_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"REMOVE_LIQUIDITY computation error for intent_id={intent.intent_id}:")

    lp_burned_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    lp_burned_mismatch.fills[0].lp_burned += 1
    ok, err = validate_settlement_strong(
        settlement=lp_burned_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={intent.intent_id}"

    amount0_out_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount0_out_mismatch.fills[0].amount0_out += 1
    ok, err = validate_settlement_strong(
        settlement=amount0_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={intent.intent_id}"

    amount1_out_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount1_out_mismatch.fills[0].amount1_out += 1
    ok, err = validate_settlement_strong(
        settlement=amount1_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={intent.intent_id}"

    low_lp_balances = LPTable()
    low_lp_balances.set(pk, pool_id, 1)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=low_lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"REMOVE_LIQUIDITY apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_replay_and_event_mismatches() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.balance_deltas[0].delta_sub += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas mismatch vs replay"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.reserve_deltas[0].delta_add += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas mismatch vs replay"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.lp_deltas[0].delta_add += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas mismatch vs replay"

    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.events[0]["fee_bps"] += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "events mismatch vs replay"


def test_check_canonical_deltas_rejects_unsorted_and_zero_reserve_lp_entries() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.reserve_deltas = list(reversed(settlement.reserve_deltas))
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas not sorted canonically"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.reserve_deltas.append(
        ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=0, delta_sub=0)
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas contains a zero entry"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.lp_deltas.append(
        LPDelta(pubkey=intent.sender_pubkey, pool_id=pool_id, delta_add=0, delta_sub=0)
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas contains a zero entry"


def test_strong_validator_rejects_cow_netted_variants_and_legacy_failure() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 10_000)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    exact_out_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(909),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 100,
            "max_amount_in": 1_000,
            "recipient": pk1,
        },
    )
    exact_out_settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(exact_out_intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=exact_out_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=100,
                fee_paid=0,
            )
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=exact_out_settlement,
        intents=[exact_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={exact_out_intent.intent_id}"

    exact_in_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(910),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )
    cow_settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(exact_in_intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=exact_in_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=50,
                fee_paid=0,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=50, delta_sub=0),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=cow_settlement,
        intents=[exact_in_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None
    assert err.startswith(
        f"COW_NETTED fill requires exactly one reciprocal counterparty: intent_id={exact_in_intent.intent_id}"
    )


def test_strong_validator_rejects_quote_hash_and_snapshot_binding_without_engine_witness() -> None:
    pk, asset0, asset1, pool_id, pool, balances, _intent, _settlement = _setup_swap_context()

    invalid_hash_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(911),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
            "quote_receipt_hash": "",
        },
    )
    settlement = compute_settlement([invalid_hash_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_hash_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "invalid quote_receipt_hash" in err

    unsanitized_hash_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(917),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xdeadbeef",
        },
    )
    settlement = compute_settlement([unsanitized_hash_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[unsanitized_hash_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err

    snapshot_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(912),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
            "quote_pool_fingerprint": pool_state_fingerprint(pool),
        },
    )
    settlement = compute_settlement([snapshot_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[snapshot_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt snapshot binding requires validated engine witness" in err

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[snapshot_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_snapshot_bound_quote_bindings=True,
    )
    assert ok is True, err


def test_strong_validator_rejects_cow_netted_input_and_apply_errors() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    def _settlement_for(intent_id: str, *, amount_in_filled: int = 100, amount_out_filled: int = 50, fee_paid: int = 0) -> Settlement:
        return Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[(intent_id, FillAction.FILL)],
            fills=[
                Fill(
                    intent_id=intent_id,
                    action=FillAction.FILL,
                    reason="COW_NETTED",
                    amount_in_filled=amount_in_filled,
                    amount_out_filled=amount_out_filled,
                    fee_paid=fee_paid,
                )
            ],
            balance_deltas=[
                BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
                BalanceDelta(pubkey=pk1, asset=asset1, delta_add=amount_out_filled, delta_sub=0),
            ],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        )

    invalid_amount_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(913),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": False,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )
    ok, err = validate_settlement_strong(
        settlement=_settlement_for(invalid_amount_intent.intent_id),
        intents=[invalid_amount_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"invalid amount_in for intent_id={invalid_amount_intent.intent_id}"

    invalid_min_out_intent = replace(
        invalid_amount_intent,
        intent_id=_iid(914),
        fields={**invalid_amount_intent.fields, "amount_in": 100, "min_amount_out": False},
    )
    ok, err = validate_settlement_strong(
        settlement=_settlement_for(invalid_min_out_intent.intent_id),
        intents=[invalid_min_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"invalid min_amount_out for intent_id={invalid_min_out_intent.intent_id}"

    base_intent = replace(
        invalid_amount_intent,
        intent_id=_iid(915),
        fields={**invalid_amount_intent.fields, "amount_in": 100, "min_amount_out": 10},
    )
    ok, err = validate_settlement_strong(
        settlement=_settlement_for(base_intent.intent_id, fee_paid=1),
        intents=[base_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED fee_paid must be 0: intent_id={base_intent.intent_id}"

    ok, err = validate_settlement_strong(
        settlement=_settlement_for(base_intent.intent_id, amount_in_filled=99),
        intents=[base_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED amount_in_filled mismatch: intent_id={base_intent.intent_id}"

    ok, err = validate_settlement_strong(
        settlement=_settlement_for(base_intent.intent_id, amount_out_filled=9),
        intents=[base_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED slippage: intent_id={base_intent.intent_id}"

    counterparty_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(919),
        sender_pubkey=pk1,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset1,
            "asset_out": asset0,
            "amount_in": 50,
            "min_amount_out": 100,
            "recipient": pk0,
        },
    )
    low_balance_pair = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(base_intent.intent_id, FillAction.FILL), (counterparty_intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=base_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=50,
                fee_paid=0,
            ),
            Fill(
                intent_id=counterparty_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=50,
                amount_out_filled=100,
                fee_paid=0,
            ),
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    low_balances = BalanceTable()
    low_balances.set(pk0, asset0, 1)
    low_balances.set(pk1, asset1, 50)
    ok, err = validate_settlement_strong(
        settlement=low_balance_pair,
        intents=[base_intent, counterparty_intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"COW_NETTED apply error for intent_id={base_intent.intent_id}:")


def test_strong_validator_rejects_unsupported_intent_kind() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, _intent, _settlement = _setup_swap_context()
    weird_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind="MYSTERY_KIND",
        intent_id=_iid(916),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(weird_intent.intent_id, FillAction.FILL)],
        fills=[Fill(intent_id=weird_intent.intent_id, action=FillAction.FILL)],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[weird_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "unsupported intent kind for strong validation: MYSTERY_KIND"


# ---------------------------------------------------------------------------
# [TESTER] v2 — Golden characterization + precedence + no-op-on-reject suite
# for the strict behavior-preserving refactor of
# `_validate_settlement_strong_impl`.
#
# These pin the CURRENT observable behavior of the strong validator: the EXACT
# reject code/message per rule, the ORDER (precedence) in which rules fire when
# an input violates two rules at once, and that a rejected input leaves the
# replay state (balances / pools / lp) unchanged. They are the oracle: they must
# remain identically green after the refactor. Any drift = the refactor is wrong.
# ---------------------------------------------------------------------------


def _snapshot_balances(balances: BalanceTable) -> dict:
    return dict(balances.get_all_balances())


def _snapshot_lp(lp: LPTable) -> dict:
    return dict(lp.get_all_balances())


def _snapshot_pools(pools: dict) -> dict:
    # Capture the reserves/supply that the replay would mutate in place.
    return {
        pid: (int(p.reserve0), int(p.reserve1), int(p.lp_supply))
        for pid, p in pools.items()
    }


# --- GOLDEN: a passing (accepted) settlement for each supported intent kind ---


def test_golden_accepts_passing_swap_exact_in() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_golden_accepts_passing_swap_exact_out() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_exact_out_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_golden_accepts_passing_create_pool() -> None:
    _pk, _a0, _a1, balances, intent, settlement = _setup_create_pool_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_golden_accepts_passing_add_liquidity() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_golden_accepts_passing_remove_liquidity() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_remove_liquidity_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


# --- PRECEDENCE: top-level rule ordering (which rule fires first) ---


def test_precedence_mode_check_before_fee_params() -> None:
    # Bad mode AND bad protocol_fee_share_bps. Mode check (first) must win.
    # MUTATION CAUGHT: moving the protocol_fee_share_bps check above the mode check.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="bogus_mode",
        protocol_fee_share_bps=99999,  # also invalid
    )
    assert ok is False
    assert err == "unsupported validation mode: 'bogus_mode'"


def test_precedence_fee_bps_range_before_recipient_required() -> None:
    # Out-of-range fee bps AND missing recipient pubkey. Range check fires first.
    # MUTATION CAUGHT: reordering the recipient-required check above the bps-range check.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        protocol_fee_share_bps=20000,  # out of [0,10000] AND >0 with no recipient
        protocol_fee_recipient_pubkey=None,
    )
    assert ok is False
    assert err == "protocol_fee_share_bps must be an int in [0, 10000]"


def test_precedence_duplicate_intent_id_before_included_mismatch() -> None:
    # Duplicate input intent ids AND included_intents mismatch. Dup check is first.
    # MUTATION CAUGHT: reordering the included-intents-mismatch check above duplicate-intent-id.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.included_intents = [(_iid(123456), FillAction.REJECT)]  # also mismatched
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent, intent],  # duplicate
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "duplicate intent_id in input intents"


def test_precedence_included_mismatch_before_duplicate_included() -> None:
    # included_intents set-mismatch AND contains a duplicate id. Set-mismatch fires first.
    # MUTATION CAUGHT: reordering the duplicate-included-entries check above set-mismatch.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    # Two copies of a WRONG id => set mismatch (missing real id, extra wrong id) AND duplicates.
    settlement.included_intents = [
        (_iid(777), FillAction.REJECT),
        (_iid(777), FillAction.REJECT),
    ]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"settlement included_intents mismatch: missing=['{intent.intent_id}'] extra=['{_iid(777)}']"


def test_precedence_duplicate_fill_before_extra_fill() -> None:
    # fills has a duplicated id AND an extra (not-in-intents) id. Duplicate check is first.
    # MUTATION CAUGHT: reordering the extra-fill-id check above duplicate-fill-id.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    extra = Fill(
        intent_id=_iid(888),
        action=FillAction.REJECT,
        reason="UNSUPPORTED",
        amount_in_filled=0,
        amount_out_filled=0,
        fee_paid=0,
    )
    # Duplicate the legitimate fill AND append an unknown one.
    settlement.fills = [settlement.fills[0], settlement.fills[0], extra]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement fills contains duplicate intent_id entries"


def test_precedence_cow_pair_index_before_per_intent_replay() -> None:
    # The up-front _validate_cow_pair_index runs before the per-intent replay loop.
    # A COW_NETTED fill with allow_cow_netting=False is rejected by the up-front index
    # check, NOT by the in-loop COW check. Both emit the same string but the up-front
    # one fires first (proven because no replay/recipient errors surface).
    # MUTATION CAUGHT: moving the _validate_cow_pair_index call below the replay loop.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills[0].reason = "COW_NETTED"
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=False,
    )
    assert ok is False
    assert err == f"COW_NETTED not allowed for intent_id={intent.intent_id}"


def test_precedence_quote_binding_runs_before_reject_skip() -> None:
    # Quote-binding checks run for EVERY included intent, BEFORE the action==REJECT skip.
    # A REJECT-action intent carrying a quote_receipt_leg_index still fails on the binding.
    # MUTATION CAUGHT: moving the action==REJECT early-continue above the quote-binding block.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    intent.fields["quote_receipt_leg_index"] = 0
    settlement.included_intents = [(intent.intent_id, FillAction.REJECT)]
    settlement.fills = [
        Fill(
            intent_id=intent.intent_id,
            action=FillAction.REJECT,
            reason="UNSUPPORTED",
            amount_in_filled=0,
            amount_out_filled=0,
            fee_paid=0,
        )
    ]
    # Make deltas/events empty so a (wrong) post-loop path could not mask this.
    settlement.balance_deltas = []
    settlement.reserve_deltas = []
    settlement.lp_deltas = []
    settlement.events = None
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    # The leg-index format check passes (0 is valid), then the unconditional
    # "transport metadata requires validated engine witness" reject fires.
    assert err is not None
    assert err.startswith("quote receipt transport metadata requires validated engine witness")


def test_precedence_leg_index_format_before_engine_witness() -> None:
    # Within the leg-index block: the format-validity check (negative => invalid) fires
    # BEFORE the unconditional engine-witness reject.
    # MUTATION CAUGHT: dropping/reordering the leg-index format check vs the witness reject.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    intent.fields["quote_receipt_leg_index"] = -1  # invalid format
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith("invalid quote_receipt_leg_index")


def test_precedence_recipient_validated_before_create_pool_body() -> None:
    # recipient validation (332-335) runs for CREATE_POOL too, BEFORE the CREATE_POOL body.
    # An invalid recipient rejects with the recipient message, not a CREATE_POOL field error.
    # MUTATION CAUGHT: moving the recipient check after the per-kind dispatch.
    _pk, _a0, _a1, balances, intent, settlement = _setup_create_pool_context()
    intent.fields["recipient"] = ""  # invalid
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid recipient for intent_id={intent.intent_id}"


def test_precedence_create_pool_dispatched_before_shared_pool_lookup() -> None:
    # CREATE_POOL is dispatched BEFORE the shared `pool_id not in pools` lookup, so a
    # CREATE_POOL intent (which has no pre-existing pool) never trips pool-not-found.
    # A CREATE_POOL with a bad fill is rejected by the CREATE_POOL body, proving the
    # create branch was taken instead of the generic pool lookup.
    # MUTATION CAUGHT: moving the CREATE_POOL branch below the shared pool lookup.
    _pk, _a0, _a1, balances, intent, settlement = _setup_create_pool_context()
    settlement.fills[0].amount0_used = 999999  # mismatch vs kernel
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.amount0_used mismatch for intent_id={intent.intent_id}"


def test_precedence_canonical_deltas_before_balance_mismatch() -> None:
    # Post-loop: _check_canonical_deltas runs BEFORE the balance_deltas-vs-replay compare.
    # A settlement whose balance_deltas are both non-canonical (zero entry) is rejected
    # by the canonical check, not the replay-mismatch check.
    # MUTATION CAUGHT: reordering the balance_deltas replay compare above _check_canonical_deltas.
    _pk, asset0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    # Inject a zero-valued balance delta (non-canonical) at the front.
    settlement.balance_deltas = [
        BalanceDelta(pubkey="0x" + "11" * 48, asset=asset0, delta_add=0, delta_sub=0)
    ] + list(settlement.balance_deltas)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas contains a zero entry"


def test_precedence_balance_mismatch_before_events_mismatch() -> None:
    # Post-loop compare order: balance_deltas mismatch is reported BEFORE events mismatch.
    # MUTATION CAUGHT: reordering the events compare above the balance_deltas compare.
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    # Corrupt balance_deltas (drop one) AND corrupt events simultaneously.
    settlement.balance_deltas = list(settlement.balance_deltas)[:-1]
    settlement.events = [{"type": "BOGUS"}]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas mismatch vs replay"


def test_precedence_reserve_mismatch_before_lp_mismatch() -> None:
    # Post-loop compare: reserve_deltas mismatch is reported BEFORE lp_deltas mismatch.
    # add_liquidity touches BOTH reserves and lp, so corrupting both is meaningful.
    # MUTATION CAUGHT: reordering the lp_deltas compare above the reserve_deltas compare.
    _pk, _a0, _a1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    # Drop a reserve delta AND drop an lp delta.
    settlement.reserve_deltas = list(settlement.reserve_deltas)[:-1]
    settlement.lp_deltas = []
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas mismatch vs replay"


def test_precedence_lp_mismatch_before_events_mismatch() -> None:
    # Post-loop compare: lp_deltas mismatch is reported BEFORE events mismatch.
    # MUTATION CAUGHT: reordering the events compare above the lp_deltas compare.
    _pk, _a0, _a1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.lp_deltas = []  # mismatch vs replay
    settlement.events = [{"type": "BOGUS"}]  # also mismatch
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas mismatch vs replay"


# --- NO-OP ON REJECT: a rejected input must not mutate replay state ---
# The impl operates on local copies (pre_balances / pre_pools / pre_lp_balances
# are deep-copied before replay). These tests pin that the ORIGINAL caller-owned
# state objects are never mutated, even when replay partially applies before the
# reject fires. MUTATION CAUGHT (all three): replaying against the originals
# instead of copies (dropping _copy_balance_table / replace(pool) / _copy_lp_table).


def test_no_op_on_reject_swap_does_not_mutate_inputs() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    bal_before = _snapshot_balances(balances)
    pools_before = _snapshot_pools({pool_id: pool})
    # Corrupt the fee so the swap applies balances+reserves locally then rejects on
    # the fee_paid mismatch — a path that partially mutates the LOCAL copies.
    settlement.fills[0].fee_paid = (settlement.fills[0].fee_paid or 0) + 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={intent.intent_id}"
    assert _snapshot_balances(balances) == bal_before
    assert _snapshot_pools({pool_id: pool}) == pools_before


def test_no_op_on_reject_add_liquidity_does_not_mutate_inputs() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    bal_before = _snapshot_balances(balances)
    pools_before = _snapshot_pools({pool_id: pool})
    lp_before = _snapshot_lp(lp_balances)
    # Corrupt events so replay fully applies (mutating local copies) then rejects post-loop.
    settlement.events = [{"type": "BOGUS"}]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert _snapshot_balances(balances) == bal_before
    assert _snapshot_pools({pool_id: pool}) == pools_before
    assert _snapshot_lp(lp_balances) == lp_before


def test_no_op_on_reject_remove_liquidity_does_not_mutate_inputs() -> None:
    _pk, _a0, _a1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_remove_liquidity_context()
    bal_before = _snapshot_balances(balances)
    pools_before = _snapshot_pools({pool_id: pool})
    lp_before = _snapshot_lp(lp_balances)
    settlement.events = [{"type": "BOGUS"}]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert _snapshot_balances(balances) == bal_before
    assert _snapshot_pools({pool_id: pool}) == pools_before
    assert _snapshot_lp(lp_balances) == lp_before


def test_no_op_on_accept_does_not_mutate_inputs() -> None:
    # Even on the ACCEPT path the caller-owned inputs must be untouched (replay uses copies).
    # MUTATION CAUGHT: replaying against the originals (would mutate on accept too).
    _pk, _a0, _a1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    bal_before = _snapshot_balances(balances)
    pools_before = _snapshot_pools({pool_id: pool})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None
    assert _snapshot_balances(balances) == bal_before
    assert _snapshot_pools({pool_id: pool}) == pools_before


# --- MULTI-INTENT: cross-intent state threading + interleaved precedence ---
# These witness the two properties single-intent tests are blind to: sequential
# pool-reserve visibility (intent[1] reads intent[0]'s mutation) + per-intent
# delta accumulation, and per-intent interleaved reject precedence.


def _setup_two_swap_same_pool_context() -> tuple[str, str, str, str, PoolState, BalanceTable, Intent, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    def _mk(n: int) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(n),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1_000,
                "min_amount_out": 1,
            },
        )

    i0 = _mk(800)
    i1 = _mk(801)
    settlement = compute_settlement([i0, i1], {pool_id: pool}, balances, LPTable())
    return pk, asset0, asset1, pool_id, pool, balances, i0, i1, settlement


def test_golden_accepts_two_sequential_swaps_same_pool() -> None:
    # HIGHEST-VALUE multi-intent probe. intent[1]'s expected amount_out is derived
    # from the pool reserves AFTER intent[0]'s swap; the two fills carry different
    # outputs (996 vs 995). Accepting this requires the replay to thread the pool
    # mutation between iterations AND aggregate per-intent balance/reserve deltas.
    # MUTATION CAUGHT: per-intent context reset (loses pool mutation), or accumulator
    # lists not shared by reference (loses cross-intent delta aggregation).
    _pk, _a0, _a1, pool_id, pool, balances, i0, i1, settlement = _setup_two_swap_same_pool_context()
    out_values = sorted(int(f.amount_out_filled or 0) for f in settlement.fills)
    assert out_values[0] != out_values[1]  # proves sequential reserve dependence
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[i0, i1],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_precedence_first_intent_reject_wins_over_second_intent_reject() -> None:
    # Two intents BOTH defective: intent[0] has a fee_paid mismatch (in-loop replay
    # reject), intent[1] has a bad quote binding (in-loop preamble reject). The loop
    # processes intents in included order and short-circuits on the FIRST, so the
    # error is intent[0]'s replay reject — proving per-intent checks stay interleaved
    # in a single pass (not split into separate all-intent pre-passes that reorder).
    # MUTATION CAUGHT: hoisting quote-binding (or any pre-rule) into its own pass over
    # all intents ahead of the replay loop — would surface intent[1]'s error first.
    _pk, _a0, _a1, pool_id, pool, balances, i0, i1, settlement = _setup_two_swap_same_pool_context()
    # Defect intent[1]: add a quote binding (engine-witness reject).
    i1.fields["quote_receipt_leg_index"] = 0
    # Defect intent[0]: corrupt its fee_paid so replay rejects.
    fill_by_id = {f.intent_id: f for f in settlement.fills}
    fill_by_id[i0.intent_id].fee_paid = (fill_by_id[i0.intent_id].fee_paid or 0) + 1
    # Force included order so intent[0] is processed first.
    settlement.included_intents = [
        (i0.intent_id, FillAction.FILL),
        (i1.intent_id, FillAction.FILL),
    ]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[i0, i1],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={i0.intent_id}"


def test_golden_accepts_swap_with_nonzero_protocol_fee() -> None:
    # Accept-path coverage for the protocol-fee swap branch (protocol_fee_share_bps>0):
    # exercises swap_exact_in_with_protocol_fee + the protocol-fee balance/reserve
    # deltas. A regression in this branch fails ONLY by over-rejecting a valid
    # settlement, which reject-path tests cannot catch.
    # MUTATION CAUGHT: dropping/altering the protocol-fee delta or fee computation
    # in the SWAP_EXACT_IN protocol-fee branch.
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    fee_pk = "0x" + "77" * 48
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    from src.core.cpmm import compute_fee_total, swap_exact_in_with_protocol_fee

    amount_in = 10_000
    quote = swap_exact_in_with_protocol_fee(
        reserve_in=2_000_000,
        reserve_out=2_000_000,
        amount_in=amount_in,
        fee_bps=30,
        protocol_fee_share_bps=2000,
    )
    fee = compute_fee_total(amount_in, 30)
    assert int(quote.protocol_fee) > 0  # the branch is actually exercised

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(820),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": amount_in,
            "min_amount_out": 1,
        },
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="FILLED",
                amount_in_filled=amount_in,
                amount_out_filled=int(quote.amount_out),
                fee_paid=int(fee),
                protocol_fee_paid=int(quote.protocol_fee),
            )
        ],
        balance_deltas=sorted(
            [
                BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=amount_in),
                BalanceDelta(pubkey=pk, asset=asset1, delta_add=int(quote.amount_out), delta_sub=0),
                BalanceDelta(pubkey=fee_pk, asset=asset0, delta_add=int(quote.protocol_fee), delta_sub=0),
            ],
            key=lambda d: (d.pubkey, d.asset),
        ),
        reserve_deltas=sorted(
            [
                ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=amount_in - int(quote.protocol_fee), delta_sub=0),
                ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=0, delta_sub=int(quote.amount_out)),
            ],
            key=lambda d: (d.pool_id, d.asset),
        ),
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        protocol_fee_share_bps=2000,
        protocol_fee_recipient_pubkey=fee_pk,
    )
    assert ok is True
    assert err is None
