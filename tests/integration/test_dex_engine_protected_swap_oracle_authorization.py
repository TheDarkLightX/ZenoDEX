from __future__ import annotations

from src.agents.intent_signer import create_swap_intent_from_quote_receipt
from src.core.dex import DexState
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import SignedIntentEnvelope, create_signed_intent_operation
from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.integration.zeno_oracle_routing_authorization import protected_swap_runtime_facts
from src.state import BalanceTable, LPTable
from src.state.pools import PoolState, PoolStatus
from tests.integration.oracle_authorization_test_helpers import authorization_bundle


def _pool() -> PoolState:
    return PoolState(
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


def _state_and_intent(*, sender: str, block_timestamp: int = 42):
    pools = {"p_ab": _pool()}
    q = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=123)
    assert q is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools, quote_epoch=1)
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id=pools,
        sender_pubkey=sender,
        deadline=9_999_999_999,
        slippage_bps=0,
    )
    intent = intent.with_field("nonce", 1)
    balances = BalanceTable()
    balances.set(sender, "A", 10_000)
    balances.set(sender, "B", 0)
    state = DexState(balances=balances, pools=pools, lp_balances=LPTable())
    runtime = protected_swap_runtime_facts(intent=intent, receipt=receipt, now_epoch=block_timestamp)
    return state, intent, receipt, runtime


def _authorization_for(
    runtime: dict[str, object],
    *,
    observed_epoch: int | None = None,
    value_e8: int | None = None,
    expires_at_epoch: int | None = None,
) -> dict[str, object]:
    query_id = str(runtime["query_id"])
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    observed = int(int(runtime["now_epoch"]) - 1 if observed_epoch is None else observed_epoch)
    auth = {
        "consumer_module": "zenodex.routing",
        "action_kind": "protected_swap",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": "critical-routing-v1",
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed),
        "confidence_e8": 1,
        "deviation_bps": 1,
        "observed_epoch": observed,
        "expires_at_epoch": int(runtime["now_epoch"] if expires_at_epoch is None else expires_at_epoch),
        "feed_id": "feed:routing:protected-swap",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "routing"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "routing"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "routing"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "routing"}),
        "evidence_class": "O3",
        "economic_envelope_id": "routing-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "routing"}),
    }
    return authorization_bundle(auth)


def test_protected_swap_requires_oracle_authorization_when_configured() -> None:
    sender = "0x" + "aa" * 48
    state, intent, receipt, _runtime = _state_and_intent(sender=sender)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_oracle_authorization_for_protected_swaps=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )

    assert res.ok is False
    assert res.error is not None
    assert "oracle_authorization_required" in res.error


def test_protected_swap_accepts_matching_typed_oracle_authorization() -> None:
    sender = "0x" + "aa" * 48
    state, intent, receipt, runtime = _state_and_intent(sender=sender)
    intent = intent.with_field("oracle_authorization", _authorization_for(runtime))
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_oracle_authorization_for_protected_swaps=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )

    assert res.ok is True, res.error


def test_protected_swap_rejects_authorization_for_wrong_quote_value() -> None:
    sender = "0x" + "aa" * 48
    state, intent, receipt, runtime = _state_and_intent(sender=sender)
    intent = intent.with_field(
        "oracle_authorization",
        _authorization_for(
            runtime,
            value_e8=int(runtime["runtime_value_e8"]) + 1,
        ),
    )
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_oracle_authorization_for_protected_swaps=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )

    assert res.ok is False
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


def test_protected_swap_rejects_authorization_for_wrong_receipt_context() -> None:
    sender = "0x" + "aa" * 48
    state, intent, receipt, runtime = _state_and_intent(sender=sender)
    auth = _authorization_for(runtime)
    auth["authorization"]["pre_state_hash"] = semantic_hash("test.wrong-routing-pre-state", {"intent_id": intent.intent_id})
    intent = intent.with_field("oracle_authorization", auth)
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_oracle_authorization_for_protected_swaps=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )

    assert res.ok is False
    assert res.error is not None
    assert "pre_state_hash mismatch" in res.error


def test_protected_swap_rejects_expired_authorization() -> None:
    sender = "0x" + "aa" * 48
    state, intent, receipt, runtime = _state_and_intent(sender=sender)
    intent = intent.with_field(
        "oracle_authorization",
        _authorization_for(runtime, expires_at_epoch=1),
    )
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_oracle_authorization_for_protected_swaps=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization expired" in res.error


def test_protected_swap_rejects_stale_but_unexpired_authorization() -> None:
    sender = "0x" + "aa" * 48
    state, intent, receipt, runtime = _state_and_intent(sender=sender)
    intent = intent.with_field(
        "oracle_authorization",
        _authorization_for(
            runtime,
            observed_epoch=1,
            expires_at_epoch=42,
        ),
    )
    ops = create_signed_intent_operation([SignedIntentEnvelope(intent=intent, quote_receipt=receipt)])

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            require_oracle_authorization_for_protected_swaps=True,
        ),
        state=state,
        operations=ops,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization observed_epoch outside runtime freshness window" in res.error
