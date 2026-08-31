from __future__ import annotations

from src.agents.intent_signer import create_swap_intent, create_swap_intent_from_quote_receipt, create_swap_intents_from_quote_receipt
from src.core.dex import DexState
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration import dex_engine as dex_engine_mod
from src.integration.dex_engine import DexEngineConfig, DexFaultInjectionConfig, apply_ops
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.operations import SignedIntentEnvelope, create_intent_operation, create_signed_intent_operation
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


_FAULT_STAGES = (
    "after_raw_validation",
    "after_intent_parse",
    "after_settlement_parse",
    "after_preconditions",
    "after_signature_verification",
    "after_nonce_validation",
    "after_settlement_compute",
    "after_settlement_validation",
    "after_proof_verification",
    "after_apply_pure",
)


def _create_pool_intent_dict(*, intent_id: str, sender: str, asset0: str, asset1: str, deadline: int = 9999999999) -> dict:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": int(deadline),
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }


def _base_state_and_ops(*, deadline: int = 9999999999) -> tuple[DexState, dict, str]:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    ops = {
        "2": [
            _create_pool_intent_dict(
                intent_id="0x" + "01" * 32,
                sender=sender,
                asset0=asset0,
                asset1=asset1,
                deadline=deadline,
            )
        ]
    }
    return state, ops, sender


def test_fault_injection_rejects_every_stage_without_mutating_state() -> None:
    for stage in _FAULT_STAGES:
        state, ops, sender = _base_state_and_ops()
        before = snapshot_from_state(state).data

        res = apply_ops(
            config=DexEngineConfig(
                allow_missing_settlement=True,
                require_intent_signatures=False,
                enable_test_fault_injection=True,
                fault_injection=DexFaultInjectionConfig(fail_at_stage=stage),
            ),
            state=state,
            operations=ops,
            block_timestamp=0,
            tx_sender_pubkey=sender,
        )

        after = snapshot_from_state(state).data
        assert not res.ok
        assert res.error == f"fault injected: {stage}"
        assert res.state is None
        assert res.settlement is None
        assert before == after


def test_fault_injection_requires_explicit_test_enable() -> None:
    state, ops, sender = _base_state_and_ops()

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            fault_injection=DexFaultInjectionConfig(fail_at_stage="after_intent_parse"),
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == "fault injection disabled"


def test_expired_intent_rejects_before_nonce_and_settlement_compute(monkeypatch) -> None:
    state, ops, sender = _base_state_and_ops(deadline=0)

    def _unexpected_nonce(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("nonce validation should not run for expired intents")

    def _unexpected_compute(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("settlement compute should not run for expired intents")

    monkeypatch.setattr(dex_engine_mod, "_validate_and_apply_nonce_batch", _unexpected_nonce)
    monkeypatch.setattr(dex_engine_mod, "compute_settlement", _unexpected_compute)

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=1,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == f"Intent expired: {ops['2'][0]['intent_id']}"


def test_missing_intent_signature_rejects_before_nonce_and_settlement_compute(monkeypatch) -> None:
    state, ops, sender = _base_state_and_ops()

    def _unexpected_nonce(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("nonce validation should not run for missing signatures")

    def _unexpected_compute(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("settlement compute should not run for missing signatures")

    monkeypatch.setattr(dex_engine_mod, "_validate_and_apply_nonce_batch", _unexpected_nonce)
    monkeypatch.setattr(dex_engine_mod, "compute_settlement", _unexpected_compute)

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=True,
            allow_unsigned_intents_if_tx_sender_matches=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error == f"missing intent signature: {ops['2'][0]['intent_id']}"


def test_attached_quote_receipt_mismatch_rejects_before_nonce_and_settlement_compute(monkeypatch) -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent = intent.with_field("nonce", 1)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])
    ops["2"][0]["amount_in"] = int(ops["2"][0]["amount_in"]) + 1

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    def _unexpected_nonce(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("nonce validation should not run for mismatched quote receipts")

    def _unexpected_compute(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("settlement compute should not run for mismatched quote receipts")

    monkeypatch.setattr(dex_engine_mod, "_validate_and_apply_nonce_batch", _unexpected_nonce)
    monkeypatch.setattr(dex_engine_mod, "compute_settlement", _unexpected_compute)

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error is not None
    assert "exact-in quote receipt leg mismatch" in res.error
    assert f"intent_id='{intent.intent_id}'" in res.error
    assert "quoted_amount_in=123" in res.error
    assert "amount_in=124" in res.error


def test_missing_attached_quote_receipt_rejects_before_nonce_and_settlement_compute(monkeypatch) -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
    )
    intent = intent.with_field("nonce", 1)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    def _unexpected_nonce(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("nonce validation should not run when attached quote receipt witness is missing")

    def _unexpected_compute(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("settlement compute should not run when attached quote receipt witness is missing")

    monkeypatch.setattr(dex_engine_mod, "_validate_and_apply_nonce_batch", _unexpected_nonce)
    monkeypatch.setattr(dex_engine_mod, "compute_settlement", _unexpected_compute)

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error is not None
    assert "missing quote receipt witness" in res.error
    assert f"intent_id='{intent.intent_id}'" in res.error


def test_incomplete_split_quote_receipt_rejects_before_nonce_and_settlement_compute(monkeypatch) -> None:
    sender = "0x" + "ac" * 48
    pools = {
        "p1": PoolState(
            pool_id="p1",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
        "p2": PoolState(
            pool_id="p2",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=1_000,
            fee_bps=0,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert q is not None
    assert len(q.legs) >= 2
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9999999999,
        slippage_bps=0,
        nonce_start=1,
    )
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intents[0], quote_receipt=receipt)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    def _unexpected_nonce(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("nonce validation should not run for incomplete split quote receipt bindings")

    def _unexpected_compute(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("settlement compute should not run for incomplete split quote receipt bindings")

    monkeypatch.setattr(dex_engine_mod, "_validate_and_apply_nonce_batch", _unexpected_nonce)
    monkeypatch.setattr(dex_engine_mod, "compute_settlement", _unexpected_compute)

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error is not None
    assert "incomplete quote receipt leg coverage" in res.error
    assert f"quote_hash='{receipt['receipt_hash']}'" in res.error
    assert "expected_leg_indices=[0, 1]" in res.error
    assert "observed_leg_indices=[0]" in res.error


def test_attached_multi_hop_quote_receipt_rejects_before_nonce_and_settlement_compute(monkeypatch) -> None:
    sender = "0x" + "aa" * 48
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
        "p_bc": PoolState(
            pool_id="p_bc",
            asset0="B",
            asset1="C",
            reserve0=2_000,
            reserve1=1_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        ),
    }
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="C", amount_in=123)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 2
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools)
    first_hop = q.legs[0].hops[0]
    intent = create_swap_intent(
        pool_id=first_hop.pool_id,
        asset_in=first_hop.asset_in,
        asset_out=first_hop.asset_out,
        amount_in=int(first_hop.amount_in),
        min_amount_out=int(first_hop.amount_out),
        deadline=9999999999,
        sender_pubkey=sender,
        quote_receipt_hash=str(receipt["receipt_hash"]),
        quote_pool_fingerprint=str(receipt["body"]["pools"][first_hop.pool_id]),
        quote_receipt_leg_index=0,
        nonce=1,
    )
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    balances.set(sender, "C", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())

    def _unexpected_nonce(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("nonce validation should not run for unsupported multi-hop quote receipt bindings")

    def _unexpected_compute(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError("settlement compute should not run for unsupported multi-hop quote receipt bindings")

    monkeypatch.setattr(dex_engine_mod, "_validate_and_apply_nonce_batch", _unexpected_nonce)
    monkeypatch.setattr(dex_engine_mod, "compute_settlement", _unexpected_compute)

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=ops,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )

    assert not res.ok
    assert res.error is not None
    assert "quote receipt multi-hop leg unsupported for direct intent binding" in res.error
    assert f"intent_id='{intent.intent_id}'" in res.error
    assert "hop_count=2" in res.error
