from __future__ import annotations

from src.agents.policy_compiler import compile_policy_candidate
from src.agents.zenograph_rules import ZGTrustTier
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.zenograph_autotrader_adapter import (
    ZENOGRAPH_AUTOTRADER_ADVISORY_OBSERVATION_SCHEMA,
    build_zenograph_autotrader_advisory_observation,
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
            "strategy_id": "zenograph.dca.1",
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


def _market() -> tuple[dict[str, PoolState], dict[str, object]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return pools, receipt


def test_zenograph_adapter_builds_positive_dca_advisory_path() -> None:
    pools, receipt = _market()
    observation = build_zenograph_autotrader_advisory_observation(
        strategy=_strategy(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        chain_id="tau-net-alpha",
        source_trust=ZGTrustTier.TRUSTED,
        liquidity_state="deep",
        include_krr=True,
    )

    assert observation.schema == ZENOGRAPH_AUTOTRADER_ADVISORY_OBSERVATION_SCHEMA
    assert observation.strategy_template == "dca"
    assert observation.tactic_evaluation.admissible is True
    assert observation.tactic_evaluation.positive_reasons == ("default_dca_allowed",)
    assert observation.selected_template_id == "dca"
    assert observation.observation_packet.trusted_primary() is True
    assert observation.krr_advice is not None
    assert observation.krr_advice["phase"] == "shadow"
    assert observation.krr_advice["observation_summary"]["primary_trust_tier"] == "verified"


def test_zenograph_adapter_blocks_dca_under_governance_risk() -> None:
    pools, receipt = _market()
    observation = build_zenograph_autotrader_advisory_observation(
        strategy=_strategy(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        chain_id="tau-net-alpha",
        facts={("protocol", "governance_attack_risk"): "elevated"},
        source_trust=ZGTrustTier.TRUSTED,
        liquidity_state="deep",
        include_krr=False,
    )

    assert observation.tactic_evaluation.admissible is False
    assert "governance_risk_elevated" in observation.tactic_evaluation.blocked_reasons
    assert observation.selected_template_id is None
    assert observation.krr_advice is None


def test_zenograph_adapter_drawdown_lock_keeps_dca_selected() -> None:
    pools, receipt = _market()
    observation = build_zenograph_autotrader_advisory_observation(
        strategy=_strategy(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        chain_id="tau-net-alpha",
        user_state={"drawdown_lock": True},
        source_trust=ZGTrustTier.TRUSTED,
        liquidity_state="deep",
        include_krr=False,
    )

    assert "UserPolicy" in observation.active_microtheories
    assert observation.tactic_evaluation.admissible is True
    assert observation.selected_template_id == "dca"
