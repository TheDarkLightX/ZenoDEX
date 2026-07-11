from __future__ import annotations

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.liquidity import create_pool
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation, parse_intents
from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.integration.zeno_oracle_settlement_authorization import (
    critical_settlement_profile_id,
    critical_settlement_runtime_facts,
)
from src.state import BalanceTable, LPTable
from src.state.state_root import compute_state_root
from tests.integration.oracle_authorization_test_helpers import authorization_bundle

PRICE_HISTORY = (100, 110, 120)


def _state_intent_and_settlement() -> tuple[DexState, list[dict], dict, dict[str, object]]:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id, pool, _lp = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=10_000,
        amount1=10_000,
        fee_bps=30,
        creator_pubkey=sender,
    )
    balances = BalanceTable()
    balances.set(sender, asset0, 10_000)
    balances.set(sender, asset1, 0)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())
    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "01" * 32,
        "sender_pubkey": sender,
        "deadline": 9_999_999_999,
        "nonce": 1,
        "pool_id": pool_id,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 100,
        "min_amount_out": 1,
    }
    intents = parse_intents({"2": [intent_dict]})
    settlement = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    pre_state_hash = compute_state_root(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
    )
    runtime = critical_settlement_runtime_facts(
        settlement=settlement,
        pre_state_hash=pre_state_hash,
        price_history=PRICE_HISTORY,
        now_epoch=42,
    )
    return state, [intent_dict], settlement_op, runtime


def _authorization_for(
    runtime: dict[str, object],
    *,
    value_e8: int | None = None,
    observed_epoch: int = 41,
    evidence_class: str = "O3",
    expires_at_epoch: int | None = None,
) -> dict[str, object]:
    query_id = str(runtime["query_id"])
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    auth = {
        "consumer_module": "zenodex.settlement",
        "action_kind": "critical_settlement",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": critical_settlement_profile_id(),
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 1,
        "deviation_bps": 1,
        "observed_epoch": int(observed_epoch),
        "expires_at_epoch": int(runtime["now_epoch"] if expires_at_epoch is None else expires_at_epoch),
        "feed_id": "feed:settlement:price-curr",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "settlement"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "settlement"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "settlement"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "settlement"}),
        "evidence_class": evidence_class,
        "economic_envelope_id": "settlement-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "settlement"}),
    }
    return authorization_bundle(auth)


def test_critical_settlement_requires_oracle_authorization_when_configured() -> None:
    state, intent_dicts, settlement_op, _runtime = _state_intent_and_settlement()

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error == "critical_settlement_oracle_authorization_required"


def test_critical_settlement_rejects_transaction_supplied_receipt_graph_authorization() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    settlement_op["oracle_authorization"] = _authorization_for(runtime)

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authenticated oracle replay" in res.error


def test_critical_settlement_rejects_authorization_for_wrong_price_curr() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    settlement_op["oracle_authorization"] = _authorization_for(
        runtime,
        value_e8=int(runtime["runtime_value_e8"]) + 1,
    )

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


def test_critical_settlement_rejects_authorization_for_wrong_pre_state() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    auth = _authorization_for(runtime)
    auth["authorization"]["pre_state_hash"] = semantic_hash("test.wrong-critical-settlement-pre-state", {"case": 1})
    settlement_op["oracle_authorization"] = auth

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error is not None
    assert "pre_state_hash mismatch" in res.error


def test_critical_settlement_rejects_below_o3_authorization_evidence() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    settlement_op["oracle_authorization"] = _authorization_for(runtime, evidence_class="O2")

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error is not None
    assert "evidence_class below required O3" in res.error


def test_critical_settlement_rejects_expired_authorization() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    settlement_op["oracle_authorization"] = _authorization_for(runtime, expires_at_epoch=41)

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization expired" in res.error


def test_critical_settlement_rejects_stale_but_unexpired_authorization() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    settlement_op["oracle_authorization"] = _authorization_for(
        runtime,
        observed_epoch=39,
        expires_at_epoch=int(runtime["now_epoch"]),
    )

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            settlement_certificate_price_history=PRICE_HISTORY,
            require_oracle_authorization_for_critical_settlements=True,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization observed_epoch outside runtime freshness window" in res.error


def test_critical_settlement_rejects_authorization_without_price_history() -> None:
    state, intent_dicts, settlement_op, runtime = _state_intent_and_settlement()
    settlement_op["oracle_authorization"] = _authorization_for(runtime)

    res = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            require_oracle_authorization_for_critical_settlements=False,
        ),
        state=state,
        operations={"2": intent_dicts, "3": settlement_op},
        block_timestamp=42,
        tx_sender_pubkey=intent_dicts[0]["sender_pubkey"],
    )

    assert res.ok is False
    assert res.error == "critical settlement oracle authorization requires settlement_certificate_price_history"
