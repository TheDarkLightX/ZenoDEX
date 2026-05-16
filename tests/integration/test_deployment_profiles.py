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
        dex_config=DexConfig(require_all_nonces=False, settlement_validation="legacy"),
    )

    reasons = deployment_profile_violations(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg)
    assert "allow_missing_settlement must be false" in reasons
    assert "require_settlement_match must be true" in reasons
    assert "require_intent_signatures must be true" in reasons
    assert "dex_config.require_all_nonces must be true" in reasons
    assert "dex_config.settlement_validation must not be legacy" in reasons
    assert "allow_unsigned_intents_if_tx_sender_matches must be false" in reasons


def test_production_strict_profile_requires_upba_and_oracle_posture() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PRODUCTION_STRICT),
        allow_uniform_batch_certificate=False,
        require_uniform_batch_certificate=False,
        require_uniform_batch_price_grid_evidence=False,
        require_oracle_authorization_for_protected_swaps=False,
        require_oracle_authorization_for_critical_settlements=False,
    )

    reasons = deployment_profile_violations(DEPLOYMENT_PROFILE_PRODUCTION_STRICT, cfg)
    assert "strict UPBA production requires allow_uniform_batch_certificate" in reasons
    assert "strict UPBA production requires require_uniform_batch_certificate" in reasons
    assert "strict UPBA production requires require_uniform_batch_price_grid_evidence" in reasons
    assert "protected swaps require oracle authorization" in reasons
    assert "critical settlements require oracle authorization" in reasons


def test_profile_rejects_proof_required_without_enabled_verifier() -> None:
    cfg = replace(
        make_dex_engine_config_for_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET),
        require_proof_when_present=True,
    )

    ok, err = validate_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg)
    assert ok is False
    assert err is not None
    assert "require_proof_when_present requires proof_config.enabled" in err


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


def test_profile_factory_sanitizes_unsafe_base() -> None:
    unsafe = DexEngineConfig(
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_external_tools=True,
        consensus_mode=False,
        dex_config=DexConfig(require_all_nonces=False, settlement_validation="legacy"),
        enable_test_fault_injection=True,
        fault_injection=DexFaultInjectionConfig(fail_at_stage="after_raw_validation"),
    )

    cfg = make_dex_engine_config_for_deployment_profile(
        DEPLOYMENT_PROFILE_PUBLIC_TESTNET,
        base=unsafe,
    )
    assert validate_deployment_profile(DEPLOYMENT_PROFILE_PUBLIC_TESTNET, cfg) == (True, None)
