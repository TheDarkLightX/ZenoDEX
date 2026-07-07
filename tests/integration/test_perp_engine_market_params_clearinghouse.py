from __future__ import annotations

from dataclasses import fields
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import sys

from src.core.dex import DexState
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpsState,
)
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _load_generated_ref(*, filename: str, module_name: str):
    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "perp_python" / filename
    spec = spec_from_file_location(module_name, ref_path)
    assert spec is not None and spec.loader is not None
    module = module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _ch2p_init_state_dict() -> dict[str, object]:
    ref = _load_generated_ref(
        filename="perp_epoch_clearinghouse_2p_v0_1_ref.py",
        module_name="perp_epoch_clearinghouse_2p_v0_1_ref_test",
    )
    s = ref.init_state()
    return {f.name: getattr(s, f.name) for f in fields(ref.State)}


def _ch3p_init_state_dict() -> dict[str, object]:
    ref = _load_generated_ref(
        filename="perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
        module_name="perp_epoch_clearinghouse_3p_transfer_v0_1_ref_test",
    )
    s = ref.init_state()
    return {f.name: getattr(s, f.name) for f in fields(ref.State)}


def _op(market_id: str, *, version: str, params: dict[str, object]) -> dict[str, object]:
    return {
        "module": "TauPerp",
        "version": version,
        "market_id": market_id,
        "action": "set_market_params",
        "params": params,
    }


def test_set_market_params_clearinghouse_2p_operator_only_and_mid_epoch_guard() -> None:
    market_id = "perp:ch2p:params"
    quote_asset = "0x" + "11" * 32
    operator = "00" * 48

    state_dict = _ch2p_init_state_dict()
    market = PerpClearinghouse2pMarketState(
        quote_asset=quote_asset,
        account_a_pubkey="aa" * 48,
        account_b_pubkey="bb" * 48,
        state=dict(state_dict),
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION_V5, markets={market_id: market}),
    )

    cfg = PerpEngineConfig(operator_pubkey=operator)

    # Operator-only.
    res_nonop = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, version="1.0", params={"maintenance_margin_bps": 700})]},
        tx_sender_pubkey="cc" * 48,
        block_timestamp=0,
    )
    assert res_nonop.ok is False
    assert res_nonop.error == "operator only"

    # Mid-epoch guard (simulate now_epoch advanced without settlement).
    mid_state = dict(state_dict)
    mid_state["now_epoch"] = 1
    perps_mid = PerpsState(
        version=PERPS_STATE_VERSION_V5,
        markets={
            market_id: PerpClearinghouse2pMarketState(
                quote_asset=quote_asset,
                account_a_pubkey="aa" * 48,
                account_b_pubkey="bb" * 48,
                state=mid_state,
            )
        },
    )
    mid = DexState(balances=state.balances, pools={}, lp_balances=state.lp_balances, perps=perps_mid)

    res_mid = apply_perp_ops(
        config=cfg,
        state=mid,
        operations={"5": [_op(market_id, version="1.0", params={"maintenance_margin_bps": 700})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_mid.ok is False
    assert res_mid.error == "cannot update market params mid-epoch"


def test_set_market_params_clearinghouse_3p_updates_state_when_settled() -> None:
    market_id = "perp:ch3p:params"
    quote_asset = "0x" + "22" * 32
    operator = "00" * 48

    state_dict = _ch3p_init_state_dict()
    market = PerpClearinghouse3pTransferMarketState(
        quote_asset=quote_asset,
        account_a_pubkey="aa" * 48,
        account_b_pubkey="bb" * 48,
        account_c_pubkey="cc" * 48,
        state=dict(state_dict),
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION_V5, markets={market_id: market}),
    )
    cfg = PerpEngineConfig(operator_pubkey=operator)

    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, version="1.1", params={"maintenance_margin_bps": 700})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error
    assert res.state is not None and res.state.perps is not None
    m2 = res.state.perps.markets[market_id]
    assert isinstance(m2, PerpClearinghouse3pTransferMarketState)
    assert int(m2.state["maintenance_margin_bps"]) == 700


def test_set_market_params_clearinghouse_rejects_unfunded_liquidation_cone() -> None:
    market_id = "perp:ch2p:params"
    quote_asset = "0x" + "33" * 32
    operator = "00" * 48

    state_dict = _ch2p_init_state_dict()
    assert int(state_dict["maintenance_margin_bps"]) == 600
    assert int(state_dict["max_oracle_move_bps"]) == 500
    market = PerpClearinghouse2pMarketState(
        quote_asset=quote_asset,
        account_a_pubkey="aa" * 48,
        account_b_pubkey="bb" * 48,
        state=dict(state_dict),
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION_V5, markets={market_id: market}),
    )
    cfg = PerpEngineConfig(operator_pubkey=operator)

    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, version="1.0", params={"liquidation_penalty_bps": 100})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == (
        "invalid params: require funded liquidation "
        "liquidation_penalty_bps * (10000 + max_oracle_move_bps) <= "
        "10000 * (maintenance_margin_bps - max_oracle_move_bps)"
    )
