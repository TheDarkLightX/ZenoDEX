from __future__ import annotations

import sys
from types import ModuleType

import pytest

import src.integration.validation as validation
from src.agents.intent_signer import create_swap_intent_from_quote_receipt
from src.core.batch_clearing import compute_settlement
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.core.settlement import BalanceDelta, Fill, FillAction, ReserveDelta, Settlement
from src.integration.tau_gate import TauGateConfig
from src.integration.validation import apply_operations, validate_operations
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


class _FakeUniformBatchCertificate:
    pool_id = "p_ab"


def _minimal_uniform_batch_validation_inputs() -> tuple[Intent, Settlement, BalanceTable, dict[str, PoolState]]:
    pk = "0x" + "11" * 48
    pool = PoolState(
        pool_id="p_ab",
        asset0="A",
        asset1="B",
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=10,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(900),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool.pool_id,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 1,
            "min_amount_out": 0,
        },
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.REJECT)],
        fills=[Fill(intent_id=intent.intent_id, action=FillAction.REJECT, reason="test")],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    return intent, settlement, BalanceTable(), {pool.pool_id: pool}


def test_validate_operations_rejects_uniform_batch_certificate_when_protocol_fees_enabled_before_cert_parse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    intent, settlement, balances, pools = _minimal_uniform_batch_validation_inputs()
    monkeypatch.setattr(
        validation.UniformBatchCertificateV1,
        "from_obj",
        lambda obj: (_ for _ in ()).throw(AssertionError("certificate parser should not run")),
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        uniform_batch_certificate={"bad": "ignored"},
        protocol_fee_share_bps=1,
        protocol_fee_recipient_pubkey="treasury",
    )

    assert ok is False
    assert err == "uniform batch certificate cannot be used when protocol fees are enabled"


def test_validate_operations_rejects_uniform_batch_certificate_missing_pool(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    intent, settlement, balances, _pools = _minimal_uniform_batch_validation_inputs()
    monkeypatch.setattr(
        validation.UniformBatchCertificateV1,
        "from_obj",
        lambda obj: _FakeUniformBatchCertificate(),
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        block_timestamp=0,
        uniform_batch_certificate={"fake": "cert"},
    )

    assert ok is False
    assert err == "uniform batch certificate pool not found: p_ab"


def test_validate_operations_routes_uniform_batch_certificate_to_uniform_validator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    intent, settlement, balances, pools = _minimal_uniform_batch_validation_inputs()
    monkeypatch.setattr(
        validation.UniformBatchCertificateV1,
        "from_obj",
        lambda obj: _FakeUniformBatchCertificate(),
    )
    monkeypatch.setattr(
        validation,
        "validate_uniform_batch_settlement_v1",
        lambda **kwargs: (False, "uniform validator rejected"),
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        uniform_batch_certificate={"fake": "cert"},
    )

    assert ok is False
    assert err == "uniform validator rejected"


def test_validate_operations_rejects_k_decrease_settlement() -> None:
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
    # but keeps reserves non-negative.
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
                fee_paid=1,
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

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        block_timestamp=0,
    )
    assert ok is False
    assert err is not None


def test_validate_operations_accepts_cow_netted_settlement_when_swap_ordering_matches() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    pools = {pool_id: pool_state}

    balances = BalanceTable()
    balances.set(pk_a, asset0, 1_000)
    balances.set(pk_a, asset1, 0)
    balances.set(pk_b, asset0, 0)
    balances.set(pk_b, asset1, 2_000)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(11),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 150,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(12),
            sender_pubkey=pk_b,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset1,
                "asset_out": asset0,
                "amount_in": 200,
                "min_amount_out": 90,
            },
        ),
    ]
    settlement = compute_settlement(
        intents,
        pools,
        balances,
        LPTable(),
        swap_ordering="cow_pair_netting_v1",
    )

    ok_default, _err_default = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
    )
    assert ok_default is False

    ok_cow, err_cow = validate_operations(
        intents=intents,
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        swap_ordering="cow_pair_netting_v1",
    )
    assert ok_cow is True
    assert err_cow is None


def test_validate_operations_accepts_empty_batch_without_settlement() -> None:
    ok, err = validate_operations(
        intents=[],
        settlement=None,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
    )
    assert ok is True
    assert err is None


def test_validate_operations_rejects_unsanitized_quote_bound_intent_without_engine_path() -> None:
    pk = "0x" + "11" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            curve_tag="CPMM",
            curve_params="",
            lp_supply=0,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }

    balances = BalanceTable()
    balances.set(pk, "A", 10_000)
    balances.set(pk, "B", 0)

    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=pk,
        deadline=9999999999,
        slippage_bps=0,
    )
    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert "strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation" in err


def test_validate_operations_requires_explicit_opt_in_for_snapshot_bound_quote_binding() -> None:
    pk = "0x" + "11" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            curve_tag="CPMM",
            curve_params="",
            lp_supply=0,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }

    balances = BalanceTable()
    balances.set(pk, "A", 10_000)
    balances.set(pk, "B", 0)

    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=pk,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent = intent.without_field("quote_receipt_hash").without_field(
        "quote_receipt_leg_index"
    )

    settlement = compute_settlement(
        intents=[intent],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok_default, err_default = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
    )
    assert ok_default is False
    assert err_default is not None
    assert "quote receipt snapshot binding requires validated engine witness" in err_default
    assert f"intent_id='{intent.intent_id}'" in err_default
    assert "only pass sanitized quote_pool_fingerprint through the validated engine path" in err_default

    ok_validated, err_validated = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools=pools,
        lp_balances=LPTable(),
        block_timestamp=0,
        settlement_validation="strong_replay",
        quote_bindings_validated=True,
    )
    assert ok_validated is True
    assert err_validated is None


def test_validate_operations_rejects_settlement_without_intents() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_operations(
        intents=[],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
    )
    assert ok is False
    assert err == "Settlement provided without intents"


def test_validate_operations_rejects_intents_without_settlement() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(50),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=None,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
    )
    assert ok is False
    assert err == "Settlement required when intents are present"


def test_validate_operations_rejects_expired_intent() -> None:
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
        intent_id=_iid(51),
        sender_pubkey=pk,
        deadline=5,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool_state}, balances, LPTable())

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        block_timestamp=6,
    )
    assert ok is False
    assert err == f"Intent expired: {intent.intent_id}"


def test_validate_operations_sanitizes_tau_gate_rejection(monkeypatch: pytest.MonkeyPatch) -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(52),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
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

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr(
        "src.integration.tau_gate.validate_settlement_swaps",
        lambda *args, **kwargs: (False, "first line\nsecond line " + ("x" * 300)),
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )
    assert ok is False
    assert err is not None
    assert err.startswith("Tau gate rejected settlement: ")
    assert "\n" not in err
    assert len(err) <= len("Tau gate rejected settlement: ") + 200


def test_validate_operations_accepts_tau_gate_enabled_success(monkeypatch: pytest.MonkeyPatch) -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(53),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
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

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr(
        "src.integration.tau_gate.validate_settlement_swaps",
        lambda *args, **kwargs: (True, None),
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )

    assert ok is True
    assert err is None


def test_validate_operations_reports_tau_gate_unavailable(monkeypatch: pytest.MonkeyPatch) -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(54),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
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

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))
    dummy_tau_gate = ModuleType("src.integration.tau_gate")
    monkeypatch.setitem(sys.modules, "src.integration.tau_gate", dummy_tau_gate)

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )

    assert ok is False
    assert err == "Tau gate unavailable: ImportError"


def test_validate_operations_reports_tau_gate_crash_without_detail(monkeypatch: pytest.MonkeyPatch) -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(55),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
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

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))

    def crash(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise RuntimeError("")

    monkeypatch.setattr("src.integration.tau_gate.validate_settlement_swaps", crash)

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )

    assert ok is False
    assert err == "Tau gate crashed: RuntimeError"


def test_validate_operations_reports_tau_gate_crash_with_detail(monkeypatch: pytest.MonkeyPatch) -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(57),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
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

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))

    def crash(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise RuntimeError("detail message")

    monkeypatch.setattr("src.integration.tau_gate.validate_settlement_swaps", crash)

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )

    assert ok is False
    assert err == "Tau gate crashed: RuntimeError: detail message"


def test_validate_operations_preserves_short_tau_gate_rejection(monkeypatch: pytest.MonkeyPatch) -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(56),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": "0x" + "22" * 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )
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

    monkeypatch.setattr("src.integration.validation.validate_settlement_strong", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr(
        "src.integration.tau_gate.validate_settlement_swaps",
        lambda *args, **kwargs: (False, "short detail"),
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=BalanceTable(),
        pools={},
        lp_balances=None,
        block_timestamp=0,
        tau_gate_config=TauGateConfig(enabled=True),
    )

    assert ok is False
    assert err == "Tau gate rejected settlement: short detail"


def test_apply_operations_applies_valid_swap_settlement() -> None:
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
    pools = {pool_id: pool_state}

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(53),
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
    settlement = compute_settlement([intent], pools, balances, LPTable())

    apply_operations(settlement, balances, pools, LPTable())

    assert balances.get(pk, asset0) == 9_900
    assert balances.get(pk, asset1) > 0
    assert pools[pool_id].reserve0 == 1_100
    assert pools[pool_id].reserve1 < 1_000
