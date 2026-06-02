from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.dex import DexConfig
from src.integration.deployment_profiles import (
    DEPLOYMENT_PROFILE_LOCAL,
    DEPLOYMENT_PROFILE_PRODUCTION_STRICT,
    DEPLOYMENT_PROFILE_PUBLIC_TESTNET,
    deployment_profile_ids,
    deployment_profile_violations,
    make_dex_engine_config_for_deployment_profile,
    validate_deployment_profile,
)
from src.integration.dex_engine import DexEngineConfig, DexFaultInjectionConfig


def test_deployment_profile_ids_are_stable() -> None:
    assert deployment_profile_ids() == (
        DEPLOYMENT_PROFILE_LOCAL,
        DEPLOYMENT_PROFILE_PUBLIC_TESTNET,
        DEPLOYMENT_PROFILE_PRODUCTION_STRICT,
    )


@pytest.mark.parametrize(
    "profile_id",
    (
        DEPLOYMENT_PROFILE_LOCAL,
        DEPLOYMENT_PROFILE_PUBLIC_TESTNET,
        DEPLOYMENT_PROFILE_PRODUCTION_STRICT,
    ),
)
def test_profile_factories_validate(profile_id: str) -> None:
    cfg = make_dex_engine_config_for_deployment_profile(profile_id)  # type: ignore[arg-type]

    ok, err = validate_deployment_profile(profile_id, cfg)  # type: ignore[arg-type]
    assert ok is True
    assert err is None


def test_public_testnet_profile_rejects_unsafe_boundary_switches() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET),
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_unsigned_intents_if_tx_sender_matches=True,
        dex_config=DexConfig(
            settlement_validation="legacy",
            allow_snapshot_bound_quote_bindings=True,
            reject_settlements_with_rejected_intents=False,
        ),
    )

    reasons = deployment_profile_violations(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg)
    assert "allow_missing_settlement must be false" in reasons
    assert "require_settlement_match must be true" in reasons
    assert "require_intent_signatures must be true" in reasons
    assert "dex_config.settlement_validation must be strong_proof_carrying" in reasons
    assert "dex_config.allow_snapshot_bound_quote_bindings must be false" in reasons
    assert "dex_config.reject_settlements_with_rejected_intents must be true" in reasons
    assert "allow_unsigned_intents_if_tx_sender_matches must be false" in reasons


def test_production_strict_profile_requires_upba_and_oracle_posture() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PRODUCTION_STRICT),
        allow_uniform_batch_certificate=False,
        require_uniform_batch_certificate_for_supported_swaps=False,
        require_uniform_batch_optimality_certificate=False,
        require_uniform_batch_v2_bounded_grid_optimality=False,
        require_uniform_batch_v3_exact_out_grid_optimality=False,
        require_oracle_authorization_for_protected_swaps=False,
        require_oracle_authorization_for_critical_settlements=False,
    )

    reasons = deployment_profile_violations(DEPLOYMENT_PROFILE_PRODUCTION_STRICT, cfg)
    assert "allow_uniform_batch_certificate must be true" in reasons
    assert "require_uniform_batch_certificate_for_supported_swaps must be true" in reasons
    assert "require_uniform_batch_optimality_certificate must be true" in reasons
    assert "require_uniform_batch_v2_bounded_grid_optimality must be true" in reasons
    assert "require_uniform_batch_v3_exact_out_grid_optimality must be true" in reasons
    assert "protected swaps require oracle authorization" in reasons
    assert "critical settlements require oracle authorization" in reasons


def test_profile_rejects_external_tools() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET),
        allow_external_tools=True,
    )

    ok, err = validate_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg)
    assert ok is False
    assert err is not None
    assert "allow_external_tools must be false" in err


def test_profile_rejects_required_proof_without_enabled_verifier() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET),
        require_proof_when_present=True,
    )

    ok, err = validate_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg)
    assert ok is False
    assert err is not None
    assert "require_proof_when_present requires an enabled proof verifier" in err


def test_local_profile_still_rejects_fault_injection() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_LOCAL),
        enable_test_fault_injection=True,
        fault_injection=DexFaultInjectionConfig(fail_at_stage="after_raw_validation"),
    )

    ok, err = validate_deployment_profile(DEPLOYMENT_PROFILE_LOCAL, cfg)
    assert ok is False
    assert err is not None
    assert "test fault injection must be disabled" in err


def test_profile_rejects_wrong_chain_id() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET),
        chain_id="other-chain",
    )

    reasons = deployment_profile_violations(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg)
    assert "chain_id must be 'zenodex-public-testnet' for public-testnet" in reasons


def test_unknown_profile_is_rejected() -> None:
    with pytest.raises(ValueError, match="unknown deployment profile"):
        make_dex_engine_config_for_deployment_profile("unknown")  # type: ignore[arg-type]


def test_malformed_profile_ids_are_rejected() -> None:
    with pytest.raises(TypeError, match="deployment profile id must be a string"):
        make_dex_engine_config_for_deployment_profile(123)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="deployment profile id must be non-empty"):
        make_dex_engine_config_for_deployment_profile(" public-testnet")  # type: ignore[arg-type]


def test_profile_factory_sanitizes_unsafe_base() -> None:
    unsafe = DexEngineConfig(
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_external_tools=True,
        consensus_mode=False,
        dex_config=DexConfig(
            settlement_validation="legacy",
            allow_snapshot_bound_quote_bindings=True,
            reject_settlements_with_rejected_intents=False,
        ),
        enable_test_fault_injection=True,
        fault_injection=DexFaultInjectionConfig(fail_at_stage="after_raw_validation"),
    )

    cfg = make_dex_engine_config_for_deployment_profile(
        DEPLOYMENT_PROFILE_PUBLIC_TESTNET,
        base=unsafe,
    )
    assert validate_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg) == (True, None)
    assert cfg.dex_config.settlement_validation == "strong_proof_carrying"
    assert cfg.dex_config.allow_snapshot_bound_quote_bindings is False
    assert cfg.dex_config.reject_settlements_with_rejected_intents is True
