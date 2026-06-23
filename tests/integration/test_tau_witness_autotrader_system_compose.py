from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_SYSTEM_COMPOSE_V1,
    build_autotrader_system_compose_v1_step,
)


def test_build_autotrader_system_compose_v1_step() -> None:
    step = build_autotrader_system_compose_v1_step(
        emit_requested=1,
        policy_artifact_ok=1,
        tau_policy_bundle_ok=1,
        signer_binding_ok=1,
        compile_ok=1,
        source_registry_ok=1,
        signal_provenance_ok=1,
        route_economic_sanity_ok=1,
        execution_ok=1,
        oracle_freshness_ok=1,
        budget_ok=1,
        candidate_set_ok=1,
        decision_ok=1,
        kill_switch_ok=1,
        tx_envelope_ok=1,
        session_state_ok=1,
        session_capability_binding_ok=1,
        wallet_capability_ok=1,
        nonce_ok=1,
    )
    assert AUTOTRADER_SYSTEM_COMPOSE_V1.spec_id == "autotrader_system_compose_v1"
    assert step["i11"] == 1
    assert step["i19"] == 1


def test_build_autotrader_system_compose_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="emit_requested must be 0 or 1"):
        build_autotrader_system_compose_v1_step(
            emit_requested=2,
            policy_artifact_ok=1,
            tau_policy_bundle_ok=1,
            signer_binding_ok=1,
            compile_ok=1,
            source_registry_ok=1,
            signal_provenance_ok=1,
            route_economic_sanity_ok=1,
            execution_ok=1,
            oracle_freshness_ok=1,
            budget_ok=1,
            candidate_set_ok=1,
            decision_ok=1,
            kill_switch_ok=1,
            tx_envelope_ok=1,
            session_state_ok=1,
            session_capability_binding_ok=1,
            wallet_capability_ok=1,
            nonce_ok=1,
        )
