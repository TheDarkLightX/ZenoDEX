from __future__ import annotations

from src.integration.zeno_oracle_fail_closed_config import (
    ZENO_ORACLE_LP_DURATION_RISK_POLICY,
    ZENO_ORACLE_MIN_LP_POSITION_AGE_SECONDS,
    zeno_oracle_fail_closed_dex_config,
    zeno_oracle_fail_closed_env,
    zeno_oracle_fail_closed_perp_config,
)


def test_fail_closed_env_requires_api_oracle_gates() -> None:
    assert zeno_oracle_fail_closed_env() == {
        "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED": "1",
        "ZUSD_ORACLE_ADAPTER_REQUIRED": "1",
        "ZUSD_ORACLE_AUTHORIZATION_REQUIRED": "1",
    }


def test_fail_closed_dex_config_forces_critical_oracle_authorization() -> None:
    cfg = zeno_oracle_fail_closed_dex_config(
        require_oracle_authorization_for_protected_swaps=False,
        require_oracle_authorization_for_critical_settlements=False,
        min_lp_position_age_seconds=0,
    )

    assert cfg.require_oracle_authorization_for_protected_swaps is True
    assert cfg.require_oracle_authorization_for_critical_settlements is True
    assert cfg.min_lp_position_age_seconds == ZENO_ORACLE_MIN_LP_POSITION_AGE_SECONDS
    assert cfg.lp_duration_risk_policy == ZENO_ORACLE_LP_DURATION_RISK_POLICY


def test_fail_closed_perp_config_forces_oracle_adapter_and_authorization() -> None:
    cfg = zeno_oracle_fail_closed_perp_config(
        require_oracle_adapter_for_isolated_settle_epoch=False,
        require_oracle_adapter_for_isolated_partial_liquidate=False,
        require_oracle_adapter_for_clearinghouse_settle_epoch=False,
        require_oracle_authorization_for_isolated_settle=False,
        require_oracle_authorization_for_clearinghouse_settle_epoch=False,
        require_oracle_current_dispute_status_for_isolated_settle=False,
        require_oracle_current_dispute_status_for_clearinghouse_settle_epoch=False,
    )

    assert cfg.require_oracle_adapter_for_isolated_settle_epoch is True
    assert cfg.require_oracle_adapter_for_isolated_partial_liquidate is True
    assert cfg.require_oracle_adapter_for_clearinghouse_settle_epoch is True
    assert cfg.require_oracle_authorization_for_isolated_settle is True
    assert cfg.require_oracle_authorization_for_clearinghouse_settle_epoch is True
    assert cfg.require_oracle_current_dispute_status_for_isolated_settle is True
    assert cfg.require_oracle_current_dispute_status_for_clearinghouse_settle_epoch is True
    assert cfg.oracle_authorization_receipt_graph_root is None
    assert cfg.oracle_current_dispute_status_root is None
