#!/usr/bin/env python3
"""Check bounded perps oracle snapshot usability for ZenoOracle critical actions."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any, Callable, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.dex import DexState  # noqa: E402
from src.core.perps import (  # noqa: E402
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
    PerpsState,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot  # noqa: E402
from src.integration.perp_engine import (  # noqa: E402
    _ORACLE_PERPS_INDEX_QUERY_ID,
    _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    PerpEngineConfig,
    _ch2p_init_state_dict,
    _ch2p_step,
    _ch3p_init_state_dict,
    _ch3p_step,
    _isolated_settle_oracle_runtime_facts,
    _perps_clearinghouse_runtime_oracle_action_id,
    _perps_liquidate_account_runtime_oracle_action_id,
    _perps_runtime_oracle_action_id,
    apply_perp_ops,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.lp import LPTable  # noqa: E402

REPORT_SCHEMA = "zenodex.oracle.perps_snapshot_gate_check.v1"
OPERATOR = "00" * 48
LIQUIDATOR = "11" * 48
CH_A = "aa" * 48
CH_B = "bb" * 48
CH_C = "cc" * 48
QUOTE_ASSET = "0x" + "77" * 32
SETTLE_MARKET = "perp:snapshot-settle"
LIQUIDATE_MARKET = "perp:snapshot-liquidate"
CH2P_MARKET = "perp:ch2p:snapshot-settle"
CH3P_MARKET = "perp:ch3p:snapshot-settle"
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_live_perps_runtime_policy",
    "does_not_claim_full_perps_state_snapshot_theorem",
    "does_not_claim_live_oracle_network_safety",
}


def _op(market_id: str, action: str, **kwargs: object) -> dict[str, object]:
    obj: dict[str, object] = {
        "module": "TauPerp",
        "version": "0.1",
        "market_id": market_id,
        "action": action,
    }
    obj.update(kwargs)
    return obj


def _apply_or_raise(
    *,
    state: DexState,
    config: PerpEngineConfig,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
) -> DexState:
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=0,
    )
    if not result.ok or result.state is None:
        raise AssertionError(result.error or "perps operation rejected")
    return result.state


def _with_oracle_snapshot(state: DexState, *, market_id: str, price_e8: int) -> DexState:
    if state.perps is None:
        raise AssertionError("perps state missing")
    market = state.perps.markets[market_id]
    if not isinstance(market, PerpMarketState):
        raise AssertionError("expected isolated perps market")
    global_state = dict(market.global_state)
    now_epoch = int(global_state.get("now_epoch", 0))
    global_state["oracle_seen"] = True
    global_state["oracle_last_update_epoch"] = max(0, now_epoch - 1)
    global_state["index_price_e8"] = int(price_e8)
    markets = dict(state.perps.markets)
    markets[market_id] = replace(market, global_state=global_state, accounts=dict(market.accounts))
    return replace(state, perps=replace(state.perps, markets=markets))


def _ready_isolated_market(*, market_id: str, price_e8: int = 100_000_000) -> DexState:
    config = PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True)
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply_or_raise(
        state=state,
        config=config,
        tx_sender_pubkey=OPERATOR,
        ops=[_op(market_id, "init_market", quote_asset=QUOTE_ASSET)],
    )
    state = _apply_or_raise(
        state=state,
        config=config,
        tx_sender_pubkey=OPERATOR,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=price_e8)
    return _apply_or_raise(
        state=state,
        config=config,
        tx_sender_pubkey=OPERATOR,
        ops=[_op(market_id, "publish_clearing_price", price_e8=price_e8)],
    )


def _roundtrip_state(
    state: DexState,
    *,
    mutate_snapshot: Callable[[dict[str, Any]], None] | None = None,
) -> tuple[DexState, str]:
    snapshot = snapshot_from_state(state)
    data = copy.deepcopy(snapshot.data)
    if mutate_snapshot is not None:
        mutate_snapshot(data)
    restored = state_from_snapshot(data)
    return restored, snapshot.commitment_hex()


def _market(state: DexState, market_id: str) -> PerpMarketState:
    if state.perps is None:
        raise AssertionError("perps state missing")
    market = state.perps.markets.get(market_id)
    if not isinstance(market, PerpMarketState):
        raise AssertionError(f"isolated market missing: {market_id}")
    return market


def _ch2p_market(state: DexState, market_id: str) -> PerpClearinghouse2pMarketState:
    if state.perps is None:
        raise AssertionError("perps state missing")
    market = state.perps.markets.get(market_id)
    if not isinstance(market, PerpClearinghouse2pMarketState):
        raise AssertionError(f"2p clearinghouse market missing: {market_id}")
    return market


def _ch3p_market(state: DexState, market_id: str) -> PerpClearinghouse3pTransferMarketState:
    if state.perps is None:
        raise AssertionError("perps state missing")
    market = state.perps.markets.get(market_id)
    if not isinstance(market, PerpClearinghouse3pTransferMarketState):
        raise AssertionError(f"3p clearinghouse market missing: {market_id}")
    return market


def _accepted_bridge(*, action_kind: str, profile_id: str, action_id: str) -> dict[str, object]:
    return {
        "status": "accepted",
        "errors": [],
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
        "profile_id": profile_id,
        "action_id": action_id,
    }


def _ready_clearinghouse_2p_market(*, market_id: str = CH2P_MARKET, price_e8: int = 100_000_000) -> DexState:
    state_dict = _ch2p_init_state_dict()
    state_dict, _ = _ch2p_step(state_dict, tag="advance_epoch", args={"delta": 1})
    state_dict, _ = _ch2p_step(state_dict, tag="publish_clearing_price", args={"price_e8": int(price_e8)})
    market = PerpClearinghouse2pMarketState(
        quote_asset=QUOTE_ASSET,
        account_a_pubkey=CH_A,
        account_b_pubkey=CH_B,
        state=state_dict,
    )
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION_V5, markets={market_id: market}),
    )


def _ready_clearinghouse_3p_market(*, market_id: str = CH3P_MARKET, price_e8: int = 100_000_000) -> DexState:
    state_dict = _ch3p_init_state_dict()
    state_dict, _ = _ch3p_step(state_dict, tag="advance_epoch", args={"delta": 1})
    state_dict, _ = _ch3p_step(state_dict, tag="publish_clearing_price", args={"price_e8": int(price_e8)})
    market = PerpClearinghouse3pTransferMarketState(
        quote_asset=QUOTE_ASSET,
        account_a_pubkey=CH_A,
        account_b_pubkey=CH_B,
        account_c_pubkey=CH_C,
        state=state_dict,
    )
    return DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION_V5, markets={market_id: market}),
    )


def _case_result(name: str, *, ok: bool, errors: list[str], details: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "name": name,
        "ok": bool(ok),
        "status": "accepted" if ok else "rejected",
        "errors": list(errors),
        "details": dict(details),
    }


def settle_snapshot_roundtrip_case(*, tamper_snapshot: bool = False) -> dict[str, Any]:
    state = _ready_isolated_market(market_id=SETTLE_MARKET)
    before = _isolated_settle_oracle_runtime_facts(market_id=SETTLE_MARKET, market=_market(state, SETTLE_MARKET))

    def mutate(data: dict[str, Any]) -> None:
        markets = data["perps"]["markets"]
        for entry in markets:
            if entry["market_id"] == SETTLE_MARKET:
                entry["global_state"]["index_price_e8"] = int(entry["global_state"]["index_price_e8"]) + 1
                return
        raise AssertionError("settle market missing from snapshot")

    restored, commitment = _roundtrip_state(state, mutate_snapshot=mutate if tamper_snapshot else None)
    after = _isolated_settle_oracle_runtime_facts(market_id=SETTLE_MARKET, market=_market(restored, SETTLE_MARKET))
    errors: list[str] = []
    if before != after:
        errors.append("settle_runtime_facts_changed_after_snapshot_roundtrip")
    return _case_result(
        "isolated_settle_snapshot_runtime_facts_roundtrip",
        ok=not errors,
        errors=errors,
        details={
            "snapshot_commitment": commitment,
            "action_id": after["action_id"],
            "pre_state_hash": after["pre_state_hash"],
            "query_id": after["query_id"],
            "runtime_value_e8": after["runtime_value_e8"],
        },
    )


def settle_adapter_bridge_executes_after_snapshot_case() -> dict[str, Any]:
    state = _ready_isolated_market(market_id=SETTLE_MARKET)
    restored, commitment = _roundtrip_state(state)
    market = _market(restored, SETTLE_MARKET)
    expected_action_id = _perps_runtime_oracle_action_id(
        PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True),
        market_id=SETTLE_MARKET,
        action_kind="settle_epoch",
        market=market,
    )

    def verifier(_bridge: object) -> dict[str, object]:
        return _accepted_bridge(
            action_kind="settle_epoch",
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            action_id=expected_action_id,
        )

    config = PerpEngineConfig(
        operator_pubkey=OPERATOR,
        allow_isolated_markets=True,
        oracle_adapter_bridge_verifier=verifier,
        require_oracle_adapter_for_isolated_settle_epoch=True,
    )
    result = apply_perp_ops(
        config=config,
        state=restored,
        operations={"19": [_op(SETTLE_MARKET, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=OPERATOR,
        block_timestamp=0,
    )
    errors = [] if result.ok else [result.error or "settle_epoch_rejected_after_snapshot"]
    return _case_result(
        "isolated_settle_adapter_bridge_executes_after_snapshot",
        ok=result.ok,
        errors=errors,
        details={"snapshot_commitment": commitment, "action_id": expected_action_id},
    )


def stale_settle_adapter_bridge_rejected_after_snapshot_drift_case() -> dict[str, Any]:
    state = _ready_isolated_market(market_id=SETTLE_MARKET)
    config = PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True)
    stale_action_id = _perps_runtime_oracle_action_id(
        config,
        market_id=SETTLE_MARKET,
        action_kind="settle_epoch",
        market=_market(state, SETTLE_MARKET),
    )

    def mutate(data: dict[str, Any]) -> None:
        markets = data["perps"]["markets"]
        for entry in markets:
            if entry["market_id"] == SETTLE_MARKET:
                entry["global_state"]["index_price_e8"] = int(entry["global_state"]["index_price_e8"]) + 1
                return
        raise AssertionError("settle market missing from snapshot")

    restored, commitment = _roundtrip_state(state, mutate_snapshot=mutate)
    fresh_action_id = _perps_runtime_oracle_action_id(
        config,
        market_id=SETTLE_MARKET,
        action_kind="settle_epoch",
        market=_market(restored, SETTLE_MARKET),
    )

    def verifier(_bridge: object) -> dict[str, object]:
        return _accepted_bridge(
            action_kind="settle_epoch",
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            action_id=stale_action_id,
        )

    result = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey=OPERATOR,
            allow_isolated_markets=True,
            oracle_adapter_bridge_verifier=verifier,
            require_oracle_adapter_for_isolated_settle_epoch=True,
        ),
        state=restored,
        operations={"19": [_op(SETTLE_MARKET, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=OPERATOR,
        block_timestamp=0,
    )
    rejection = result.error or ""
    errors: list[str] = []
    if stale_action_id == fresh_action_id:
        errors.append("snapshot_drift_did_not_change_action_id")
    if result.ok:
        errors.append("stale_settle_action_id_was_accepted_after_snapshot_drift")
    elif "oracle_adapter_bridge action_id mismatch" not in rejection:
        errors.append("stale_settle_action_id_rejected_for_unexpected_reason")
    return _case_result(
        "isolated_settle_stale_action_id_rejected_after_snapshot_drift",
        ok=not errors,
        errors=errors,
        details={
            "snapshot_commitment": commitment,
            "stale_action_id": stale_action_id,
            "fresh_action_id": fresh_action_id,
            "rejection": rejection,
        },
    )


def liquidate_snapshot_action_id_roundtrip_case() -> dict[str, Any]:
    state = _ready_isolated_market(market_id=LIQUIDATE_MARKET)
    market = _market(state, LIQUIDATE_MARKET)
    accounts = dict(market.accounts)
    accounts[LIQUIDATOR] = PerpAccountState(
        position_base=10,
        entry_price_e8=100_000_000,
        collateral_quote=1,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    if state.perps is None:
        raise AssertionError("perps state missing")
    markets = dict(state.perps.markets)
    markets[LIQUIDATE_MARKET] = replace(market, accounts=accounts)
    state = replace(state, perps=PerpsState(version=state.perps.version, markets=markets))
    config = PerpEngineConfig(operator_pubkey=OPERATOR, allow_isolated_markets=True)
    before_action_id = _perps_liquidate_account_runtime_oracle_action_id(
        config,
        market_id=LIQUIDATE_MARKET,
        market=_market(state, LIQUIDATE_MARKET),
        account_pubkey=LIQUIDATOR,
        fraction_bps=5_000,
    )
    restored, commitment = _roundtrip_state(state)
    after_action_id = _perps_liquidate_account_runtime_oracle_action_id(
        config,
        market_id=LIQUIDATE_MARKET,
        market=_market(restored, LIQUIDATE_MARKET),
        account_pubkey=LIQUIDATOR,
        fraction_bps=5_000,
    )
    errors: list[str] = []
    if before_action_id != after_action_id:
        errors.append("liquidate_action_id_changed_after_snapshot_roundtrip")
    return _case_result(
        "isolated_liquidate_snapshot_action_id_roundtrip",
        ok=not errors,
        errors=errors,
        details={"snapshot_commitment": commitment, "action_id": after_action_id},
    )


def clearinghouse_2p_snapshot_action_id_roundtrip_case() -> dict[str, Any]:
    config = PerpEngineConfig()
    state = _ready_clearinghouse_2p_market()
    before_market = _ch2p_market(state, CH2P_MARKET)
    before_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=CH2P_MARKET,
        action_kind="settle_epoch",
        market_kind="clearinghouse_2p_v1",
        quote_asset=before_market.quote_asset,
        state=before_market.state,
        participant_pubkeys=(before_market.account_a_pubkey, before_market.account_b_pubkey),
    )
    restored, commitment = _roundtrip_state(state)
    after_market = _ch2p_market(restored, CH2P_MARKET)
    after_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=CH2P_MARKET,
        action_kind="settle_epoch",
        market_kind="clearinghouse_2p_v1",
        quote_asset=after_market.quote_asset,
        state=after_market.state,
        participant_pubkeys=(after_market.account_a_pubkey, after_market.account_b_pubkey),
    )
    errors: list[str] = []
    if before_action_id != after_action_id:
        errors.append("clearinghouse_2p_action_id_changed_after_snapshot_roundtrip")
    return _case_result(
        "clearinghouse_2p_snapshot_action_id_roundtrip",
        ok=not errors,
        errors=errors,
        details={"snapshot_commitment": commitment, "action_id": after_action_id},
    )


def clearinghouse_2p_adapter_bridge_executes_after_snapshot_case() -> dict[str, Any]:
    state = _ready_clearinghouse_2p_market()
    restored, commitment = _roundtrip_state(state)
    market = _ch2p_market(restored, CH2P_MARKET)
    config = PerpEngineConfig()
    expected_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=CH2P_MARKET,
        action_kind="settle_epoch",
        market_kind="clearinghouse_2p_v1",
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
    )

    def verifier(_bridge: object) -> dict[str, object]:
        return _accepted_bridge(
            action_kind="settle_epoch",
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            action_id=expected_action_id,
        )

    result = apply_perp_ops(
        config=PerpEngineConfig(
            oracle_adapter_bridge_verifier=verifier,
            require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        ),
        state=restored,
        operations={"19": [_op(CH2P_MARKET, "settle_epoch", version="1.0", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=OPERATOR,
        block_timestamp=0,
    )
    errors = [] if result.ok else [result.error or "clearinghouse_2p_settle_rejected_after_snapshot"]
    return _case_result(
        "clearinghouse_2p_adapter_bridge_executes_after_snapshot",
        ok=result.ok,
        errors=errors,
        details={"snapshot_commitment": commitment, "action_id": expected_action_id},
    )


def clearinghouse_3p_snapshot_action_id_roundtrip_case() -> dict[str, Any]:
    config = PerpEngineConfig()
    state = _ready_clearinghouse_3p_market()
    before_market = _ch3p_market(state, CH3P_MARKET)
    before_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=CH3P_MARKET,
        action_kind="settle_epoch",
        market_kind="clearinghouse_3p_transfer_v1",
        quote_asset=before_market.quote_asset,
        state=before_market.state,
        participant_pubkeys=(
            before_market.account_a_pubkey,
            before_market.account_b_pubkey,
            before_market.account_c_pubkey,
        ),
    )
    restored, commitment = _roundtrip_state(state)
    after_market = _ch3p_market(restored, CH3P_MARKET)
    after_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=CH3P_MARKET,
        action_kind="settle_epoch",
        market_kind="clearinghouse_3p_transfer_v1",
        quote_asset=after_market.quote_asset,
        state=after_market.state,
        participant_pubkeys=(
            after_market.account_a_pubkey,
            after_market.account_b_pubkey,
            after_market.account_c_pubkey,
        ),
    )
    errors: list[str] = []
    if before_action_id != after_action_id:
        errors.append("clearinghouse_3p_action_id_changed_after_snapshot_roundtrip")
    return _case_result(
        "clearinghouse_3p_snapshot_action_id_roundtrip",
        ok=not errors,
        errors=errors,
        details={"snapshot_commitment": commitment, "action_id": after_action_id},
    )


def clearinghouse_3p_adapter_bridge_executes_after_snapshot_case() -> dict[str, Any]:
    state = _ready_clearinghouse_3p_market()
    restored, commitment = _roundtrip_state(state)
    market = _ch3p_market(restored, CH3P_MARKET)
    config = PerpEngineConfig()
    expected_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=CH3P_MARKET,
        action_kind="settle_epoch",
        market_kind="clearinghouse_3p_transfer_v1",
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey, market.account_c_pubkey),
    )

    def verifier(_bridge: object) -> dict[str, object]:
        return _accepted_bridge(
            action_kind="settle_epoch",
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            action_id=expected_action_id,
        )

    result = apply_perp_ops(
        config=PerpEngineConfig(
            oracle_adapter_bridge_verifier=verifier,
            require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        ),
        state=restored,
        operations={"19": [_op(CH3P_MARKET, "settle_epoch", version="1.1", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=OPERATOR,
        block_timestamp=0,
    )
    errors = [] if result.ok else [result.error or "clearinghouse_3p_settle_rejected_after_snapshot"]
    return _case_result(
        "clearinghouse_3p_adapter_bridge_executes_after_snapshot",
        ok=result.ok,
        errors=errors,
        details={"snapshot_commitment": commitment, "action_id": expected_action_id},
    )


def invalid_oracle_shape_rejected_case() -> dict[str, Any]:
    state = _ready_isolated_market(market_id="perp:snapshot-invalid-oracle")

    def mutate(data: dict[str, Any]) -> None:
        markets = data["perps"]["markets"]
        for entry in markets:
            if entry["market_id"] == "perp:snapshot-invalid-oracle":
                entry["global_state"]["oracle_seen"] = False
                return
        raise AssertionError("invalid-oracle market missing from snapshot")

    errors: list[str] = []
    rejected = False
    rejection = ""
    try:
        _roundtrip_state(state, mutate_snapshot=mutate)
    except Exception as exc:  # expected fail-closed path
        rejected = True
        rejection = str(exc)
    if not rejected:
        errors.append("invalid_oracle_snapshot_shape_was_accepted")
    return _case_result(
        "invalid_oracle_snapshot_shape_rejected",
        ok=rejected,
        errors=errors,
        details={"rejection": rejection},
    )


def invalid_clearinghouse_snapshot_shape_rejected_case() -> dict[str, Any]:
    state = _ready_clearinghouse_2p_market(market_id="perp:ch2p:snapshot-invalid-net")

    def mutate(data: dict[str, Any]) -> None:
        markets = data["perps"]["markets"]
        for entry in markets:
            if entry["market_id"] == "perp:ch2p:snapshot-invalid-net":
                entry["state"]["position_base_a"] = int(entry["state"]["position_base_a"]) + 1
                return
        raise AssertionError("invalid clearinghouse market missing from snapshot")

    errors: list[str] = []
    rejected = False
    rejection = ""
    try:
        _roundtrip_state(state, mutate_snapshot=mutate)
    except Exception as exc:  # expected fail-closed path
        rejected = True
        rejection = str(exc)
    if not rejected:
        errors.append("invalid_clearinghouse_snapshot_shape_was_accepted")
    return _case_result(
        "invalid_clearinghouse_snapshot_shape_rejected",
        ok=rejected,
        errors=errors,
        details={"rejection": rejection},
    )


def build_report() -> dict[str, Any]:
    cases = [
        settle_snapshot_roundtrip_case(),
        settle_adapter_bridge_executes_after_snapshot_case(),
        stale_settle_adapter_bridge_rejected_after_snapshot_drift_case(),
        liquidate_snapshot_action_id_roundtrip_case(),
        clearinghouse_2p_snapshot_action_id_roundtrip_case(),
        clearinghouse_2p_adapter_bridge_executes_after_snapshot_case(),
        clearinghouse_3p_snapshot_action_id_roundtrip_case(),
        clearinghouse_3p_adapter_bridge_executes_after_snapshot_case(),
        invalid_oracle_shape_rejected_case(),
        invalid_clearinghouse_snapshot_shape_rejected_case(),
    ]
    errors = [f"{case['name']}:{error}" for case in cases for error in case["errors"]]
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "case_count": len(cases),
        "accepted_case_count": sum(1 for case in cases if case["ok"]),
        "error_count": len(errors),
        "errors": errors,
        "cases": cases,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = build_report()
    if args.format == "json":
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"status = {report['status']}")
        print(f"case_count = {report['case_count']}")
        print(f"accepted_case_count = {report['accepted_case_count']}")
        print(f"error_count = {report['error_count']}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
