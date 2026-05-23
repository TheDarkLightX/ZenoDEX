from __future__ import annotations

import pytest

from src.kernels.python.strategy_system_compose_v1_adapter import check_strategy_system_compose


def test_strategy_system_compose_accepts_non_emitting_and_fully_green_emit() -> None:
    non_emit = check_strategy_system_compose(
        emit_requested=False,
        policy_artifact_ok=False,
        tau_policy_bundle_ok=False,
        signer_binding_ok=False,
        compile_ok=False,
        source_registry_ok=False,
        signal_provenance_ok=False,
        route_economic_sanity_ok=False,
        execution_ok=False,
        oracle_freshness_ok=False,
        budget_ok=False,
        candidate_set_ok=False,
        decision_ok=False,
        kill_switch_ok=False,
        tx_envelope_ok=False,
        session_state_ok=False,
        session_capability_binding_ok=False,
        wallet_capability_ok=False,
        nonce_ok=False,
    )
    assert non_emit.ok is True
    assert non_emit.emit_allowed is False
    assert non_emit.error is None

    green = check_strategy_system_compose(
        emit_requested=True,
        policy_artifact_ok=True,
        tau_policy_bundle_ok=True,
        signer_binding_ok=True,
        compile_ok=True,
        source_registry_ok=True,
        signal_provenance_ok=True,
        route_economic_sanity_ok=True,
        execution_ok=True,
        oracle_freshness_ok=True,
        budget_ok=True,
        candidate_set_ok=True,
        decision_ok=True,
        kill_switch_ok=True,
        tx_envelope_ok=True,
        session_state_ok=True,
        session_capability_binding_ok=True,
        wallet_capability_ok=True,
        nonce_ok=True,
    )
    assert green.ok is True
    assert green.emit_allowed is True
    assert green.error is None


@pytest.mark.parametrize(
    ("field", "error"),
    [
        ("policy_artifact_ok", "policy_artifact_rejected"),
        ("tau_policy_bundle_ok", "tau_policy_bundle_rejected"),
        ("signer_binding_ok", "signer_binding_rejected"),
        ("compile_ok", "compile_contract_rejected"),
        ("source_registry_ok", "source_registry_rejected"),
        ("signal_provenance_ok", "signal_provenance_rejected"),
        ("route_economic_sanity_ok", "route_economic_sanity_rejected"),
        ("execution_ok", "execution_rejected"),
        ("oracle_freshness_ok", "oracle_freshness_rejected"),
        ("budget_ok", "budget_rejected"),
        ("candidate_set_ok", "candidate_set_rejected"),
        ("decision_ok", "decision_rejected"),
        ("kill_switch_ok", "kill_switch_rejected"),
        ("tx_envelope_ok", "tx_envelope_rejected"),
        ("session_state_ok", "session_state_rejected"),
        ("session_capability_binding_ok", "session_capability_binding_rejected"),
        ("wallet_capability_ok", "wallet_capability_rejected"),
        ("nonce_ok", "nonce_rejected"),
    ],
)
def test_strategy_system_compose_rejects_each_required_guard(field: str, error: str) -> None:
    kwargs = {
        "emit_requested": True,
        "policy_artifact_ok": True,
        "tau_policy_bundle_ok": True,
        "signer_binding_ok": True,
        "compile_ok": True,
        "source_registry_ok": True,
        "signal_provenance_ok": True,
        "route_economic_sanity_ok": True,
        "execution_ok": True,
        "oracle_freshness_ok": True,
        "budget_ok": True,
        "candidate_set_ok": True,
        "decision_ok": True,
        "kill_switch_ok": True,
        "tx_envelope_ok": True,
        "session_state_ok": True,
        "session_capability_binding_ok": True,
        "wallet_capability_ok": True,
        "nonce_ok": True,
    }
    kwargs[field] = False
    result = check_strategy_system_compose(**kwargs)
    assert result.ok is False
    assert result.emit_allowed is False
    assert result.error == error


def test_strategy_system_compose_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="emit_requested must be a bool"):
        check_strategy_system_compose(
            emit_requested=1,
            policy_artifact_ok=True,
            tau_policy_bundle_ok=True,
            signer_binding_ok=True,
            compile_ok=True,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            candidate_set_ok=True,
            decision_ok=True,
            kill_switch_ok=True,
            tx_envelope_ok=True,
            session_state_ok=True,
            session_capability_binding_ok=True,
            wallet_capability_ok=True,
            nonce_ok=True,
        )
