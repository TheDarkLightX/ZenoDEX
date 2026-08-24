"""Fail-closed ZenoOracle runtime configuration helpers."""

from __future__ import annotations

from dataclasses import replace
from typing import Any

from .dex_engine import DexEngineConfig
from .lp_position_age_gate import LPDurationRiskPolicy
from .perp_engine import OracleAdapterBridgeVerifier, PerpEngineConfig

ZENO_ORACLE_FAIL_CLOSED_ENV: dict[str, str] = {
    "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED": "1",
    "ZUSD_ORACLE_ADAPTER_REQUIRED": "1",
    "ZUSD_ORACLE_AUTHORIZATION_REQUIRED": "1",
}

ZENO_ORACLE_MIN_LP_POSITION_AGE_SECONDS = 300
ZENO_ORACLE_LP_DURATION_RISK_POLICY = LPDurationRiskPolicy(
    base_age_seconds=300,
    max_age_seconds=3600,
    churn_window_seconds=86_400,
    decay_seconds=86_400,
    multiplier=2,
    max_churn_tier=5,
)


def zeno_oracle_fail_closed_env() -> dict[str, str]:
    """Return API environment variables that require Oracle adapter/auth gates."""

    return dict(ZENO_ORACLE_FAIL_CLOSED_ENV)


def zeno_oracle_fail_closed_dex_config(**overrides: Any) -> DexEngineConfig:
    """Build a DEX config with critical Oracle authorization gates forced on."""

    cfg = DexEngineConfig(**overrides)
    dex_config = replace(
        cfg.dex_config,
        settlement_validation="strong_proof_carrying",
        allow_snapshot_bound_quote_bindings=False,
    )
    return replace(
        cfg,
        allow_missing_settlement=False,
        require_settlement_match=True,
        require_intent_signatures=True,
        allow_external_tools=False,
        consensus_mode=True,
        dex_config=dex_config,
        require_oracle_authorization_for_protected_swaps=True,
        require_oracle_authorization_for_critical_settlements=True,
        min_lp_position_age_seconds=max(
            int(cfg.min_lp_position_age_seconds),
            ZENO_ORACLE_MIN_LP_POSITION_AGE_SECONDS,
        ),
        lp_duration_risk_policy=cfg.lp_duration_risk_policy or ZENO_ORACLE_LP_DURATION_RISK_POLICY,
    )


def zeno_oracle_fail_closed_perp_config(
    *,
    oracle_adapter_bridge_verifier: OracleAdapterBridgeVerifier | None = None,
    **overrides: Any,
) -> PerpEngineConfig:
    """Build a perps config with all critical Oracle adapter/auth gates forced on."""

    cfg = PerpEngineConfig(**overrides)
    verifier = cfg.oracle_adapter_bridge_verifier
    if oracle_adapter_bridge_verifier is not None:
        verifier = oracle_adapter_bridge_verifier
    return replace(
        cfg,
        oracle_adapter_bridge_verifier=verifier,
        require_oracle_adapter_for_isolated_settle_epoch=True,
        require_oracle_adapter_for_isolated_partial_liquidate=True,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_isolated_settle=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
    )
