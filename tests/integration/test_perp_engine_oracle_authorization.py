from __future__ import annotations

from src.core.dex import DexState
from src.integration.perp_engine import (
    PerpEngineConfig,
    _isolated_settle_oracle_runtime_facts,
    apply_perp_ops,
)
from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tests.integration.oracle_authorization_test_helpers import authorization_bundle


def _op(market_id: str, action: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "0.1",
        "market_id": market_id,
        "action": action,
    }
    op.update(kwargs)
    return op


def _apply_result(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    operator_pubkey: str,
    require_authorization: bool = False,
    receipt_graph_root: str | None = None,
):
    cfg = PerpEngineConfig(
        operator_pubkey=operator_pubkey,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle=require_authorization,
        oracle_authorization_receipt_graph_root=receipt_graph_root,
    )
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=0,
    )


def _apply(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    operator_pubkey: str,
    require_authorization: bool = False,
) -> DexState:
    res = _apply_result(
        state=state,
        tx_sender_pubkey=tx_sender_pubkey,
        operator_pubkey=operator_pubkey,
        ops=ops,
        require_authorization=require_authorization,
    )
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _ready_market(*, market_id: str, operator: str, price_e8: int = 100_000_000) -> DexState:
    quote_asset = "0x" + "77" * 32
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=price_e8)],
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert hasattr(market, "global_state")
    market.global_state["oracle_seen"] = True
    market.global_state["oracle_last_update_epoch"] = max(0, int(market.global_state["now_epoch"]) - 1)
    market.global_state["index_price_e8"] = int(price_e8)
    return state


def _authorization_for(
    runtime: dict[str, object],
    *,
    observed_epoch: int,
    value_e8: int | None = None,
    evidence_class: str = "O3",
    expires_at_epoch: int | None = None,
) -> dict[str, object]:
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    query_id = str(runtime["query_id"])
    auth = {
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": "critical-perps-v1",
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 10_000,
        "deviation_bps": 5,
        "observed_epoch": int(observed_epoch),
        "expires_at_epoch": int(runtime["now_epoch"] if expires_at_epoch is None else expires_at_epoch),
        "feed_id": "feed:perps:index",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "perps"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "perps"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "perps"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "perps"}),
        "evidence_class": evidence_class,
        "economic_envelope_id": "perps-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "perps"}),
    }
    return authorization_bundle(auth)


def test_isolated_settle_requires_oracle_authorization_when_configured() -> None:
    market_id = "perp:auth-required"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch")],
    )

    assert res.ok is False
    assert res.error == "oracle_authorization_required"


def test_isolated_settle_accepts_matching_typed_oracle_authorization() -> None:
    market_id = "perp:auth-ok"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is True, res.error


def test_isolated_settle_accepts_configured_terminal_receipt_graph_root() -> None:
    # Arrange.
    market_id = "perp:auth-configured-root"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))
    configured_root = str(auth["authorization"]["receipt_graph_root"])

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=configured_root,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert.
    assert res.ok is True, res.error


def test_isolated_settle_rejects_different_configured_terminal_receipt_graph_root() -> None:
    # Arrange.
    market_id = "perp:auth-wrong-configured-root"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))
    wrong_root = semantic_hash("test.wrong-configured-root", {"market_id": market_id})

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=wrong_root,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert: policy-selected root mismatch closes settlement before mutation.
    assert res.ok is False
    assert res.state is None
    assert res.effects is None
    assert res.error is not None
    assert "receipt_graph_root does not match configured root" in res.error


def test_isolated_settle_rejects_authorization_for_different_oracle_value() -> None:
    market_id = "perp:auth-value-mismatch"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(
        runtime,
        observed_epoch=int(market.global_state["oracle_last_update_epoch"]),
        value_e8=int(runtime["runtime_value_e8"]) + 1,
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


def test_isolated_settle_rejects_malformed_runtime_facts(monkeypatch) -> None:
    import src.integration.perp_engine as perp_engine

    market_id = "perp:auth-malformed-runtime"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))

    def malformed_runtime_facts(*, market_id: str, market) -> dict[str, object]:
        facts = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
        facts["runtime_value_e8"] = True
        facts["now_epoch"] = False
        return facts

    monkeypatch.setattr(perp_engine, "_isolated_settle_oracle_runtime_facts", malformed_runtime_facts)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error == "oracle_authorization_rejected: malformed runtime facts"


def test_isolated_settle_sanitizes_oracle_verifier_internal_error(monkeypatch) -> None:
    import src.integration.perp_engine as perp_engine

    market_id = "perp:auth-verifier-bug"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))

    def broken_verifier(*args: object, **kwargs: object) -> dict[str, object]:
        raise RuntimeError("oracle verifier implementation bug")

    monkeypatch.setattr(perp_engine, "check_critical_consumer_authorization", broken_verifier)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error == "oracle_authorization_rejected: internal error: RuntimeError"


def test_clearinghouse_settle_sanitizes_oracle_verifier_internal_error(monkeypatch) -> None:
    import src.integration.perp_engine as perp_engine

    def broken_verifier(*args: object, **kwargs: object) -> dict[str, object]:
        raise RuntimeError("clearinghouse oracle verifier implementation bug")

    monkeypatch.setattr(perp_engine, "check_critical_consumer_authorization", broken_verifier)

    err = perp_engine._check_clearinghouse_settle_oracle_authorization(
        perp_engine._ClearinghouseSettleOracleAuthorizationRequest(
            config=perp_engine.PerpEngineConfig(),
            data={"oracle_authorization": {"present": True}},
            market_id="perp:ch2p:auth-verifier-bug",
            market_kind="clearinghouse_2p_v1",
            quote_asset="zUSD",
            state={
                "now_epoch": 1,
                "clearing_price_epoch": 1,
                "clearing_price_e8": 100_000_000,
                "index_price_e8": 100_000_000,
                "oracle_last_update_epoch": 1,
            },
            participant_pubkeys=("00" * 48, "11" * 48),
        )
    )

    assert err == "clearinghouse_settle_oracle_authorization_rejected: internal error: RuntimeError"


def test_isolated_settle_rejects_authorization_for_different_pre_state() -> None:
    market_id = "perp:auth-pre-state-mismatch"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))
    auth["authorization"]["pre_state_hash"] = semantic_hash("test.wrong-pre-state", {"market_id": market_id})

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "pre_state_hash mismatch" in res.error


def test_isolated_settle_rejects_below_o3_authorization_evidence() -> None:
    market_id = "perp:auth-evidence-floor"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(
        runtime,
        observed_epoch=int(market.global_state["oracle_last_update_epoch"]),
        evidence_class="O2",
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "evidence_class below required O3" in res.error


def test_isolated_settle_rejects_expired_authorization() -> None:
    market_id = "perp:auth-expired"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    observed_epoch = int(market.global_state["oracle_last_update_epoch"])
    auth = _authorization_for(
        runtime,
        observed_epoch=observed_epoch,
        expires_at_epoch=observed_epoch,
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization expired" in res.error


def test_isolated_settle_rejects_stale_but_unexpired_authorization() -> None:
    market_id = "perp:auth-stale-window"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]) - 3,
        expires_at_epoch=int(runtime["now_epoch"]),
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization observed_epoch outside runtime freshness window" in res.error
