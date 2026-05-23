from __future__ import annotations

from dataclasses import replace

from src.agents.policy_compiler import compile_policy_candidate
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.zenograph_autotrader_adapter import (
    build_zenograph_autotrader_advisory_observation,
)
from src.integration.zenograph_ranking_stage import (
    build_zenograph_autotrader_ranking_stage_observation,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _strategy():
    return compile_policy_candidate(
        {
            "strategy_id": "zenograph.stage.test.1",
            "owner_pubkey": "owner.pubkey.1",
            "policy_backend": "local",
            "template": "dca",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": 100,
                "per_window_max": 500,
                "lifetime_max": 1_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": 0,
            },
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": 3,
            },
            "template_params": {
                "fixed_order_size": 100,
                "cadence_epochs": 4,
                "asset_in": "A",
                "asset_out": "B",
            },
        }
    ).strategy


def _advisory():
    strategy = _strategy()
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(
        pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100
    )
    assert quote is not None
    receipt = make_route_quote_receipt(
        kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5
    )
    advisory = build_zenograph_autotrader_advisory_observation(
        strategy=strategy,
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        chain_id="tau-net-alpha",
        include_krr=False,
    )
    return strategy, advisory


def test_zenograph_ranking_stage_blocks_when_gate_blocks() -> None:
    strategy, advisory = _advisory()
    stage = build_zenograph_autotrader_ranking_stage_observation(
        strategy=strategy,
        advisory=advisory,
        gate_report={
            "gate": {
                "ranking_influence_allowed": False,
                "block_reason": "submit_vs_block_disagreement",
                "unmet_criteria": ["submit_vs_block_zero"],
            }
        },
    )

    assert stage.stage_tag == "blocked"
    assert stage.effective_ranking_template_id == "dca"
    assert stage.block_reason == "submit_vs_block_disagreement"
    assert stage.unmet_criteria == ("submit_vs_block_zero",)


def test_zenograph_ranking_stage_surfaces_candidate_when_gate_allows() -> None:
    strategy, advisory = _advisory()
    candidate_advisory = replace(
        advisory,
        selected_template_id="rebalance",
        selected_template_rank=1,
    )
    stage = build_zenograph_autotrader_ranking_stage_observation(
        strategy=strategy,
        advisory=candidate_advisory,
        gate_report={
            "gate": {
                "ranking_influence_allowed": True,
                "block_reason": None,
                "unmet_criteria": [],
            }
        },
    )

    assert stage.stage_tag == "candidate"
    assert stage.current_template_id == "dca"
    assert stage.zenograph_selected_template_id == "rebalance"
    assert stage.effective_ranking_template_id == "rebalance"
