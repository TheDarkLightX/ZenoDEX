from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class StrategySystemComposeResult:
    ok: bool
    emit_allowed: bool
    policy_artifact_ok: bool
    tau_policy_bundle_ok: bool
    signer_binding_ok: bool
    compile_ok: bool
    source_registry_ok: bool
    signal_provenance_ok: bool
    route_economic_sanity_ok: bool
    execution_ok: bool
    oracle_freshness_ok: bool
    budget_ok: bool
    candidate_set_ok: bool
    decision_ok: bool
    kill_switch_ok: bool
    tx_envelope_ok: bool
    session_state_ok: bool
    session_capability_binding_ok: bool
    wallet_capability_ok: bool
    nonce_ok: bool
    error: str | None = None


def check_strategy_system_compose(
    *,
    emit_requested: bool,
    policy_artifact_ok: bool,
    tau_policy_bundle_ok: bool,
    signer_binding_ok: bool,
    compile_ok: bool,
    source_registry_ok: bool,
    signal_provenance_ok: bool,
    route_economic_sanity_ok: bool,
    execution_ok: bool,
    oracle_freshness_ok: bool,
    budget_ok: bool,
    candidate_set_ok: bool,
    decision_ok: bool,
    kill_switch_ok: bool,
    tx_envelope_ok: bool,
    session_state_ok: bool,
    session_capability_binding_ok: bool,
    wallet_capability_ok: bool,
    nonce_ok: bool,
) -> StrategySystemComposeResult:
    emit_requested = _require_bool("emit_requested", emit_requested)
    policy_artifact_ok = _require_bool("policy_artifact_ok", policy_artifact_ok)
    tau_policy_bundle_ok = _require_bool("tau_policy_bundle_ok", tau_policy_bundle_ok)
    signer_binding_ok = _require_bool("signer_binding_ok", signer_binding_ok)
    compile_ok = _require_bool("compile_ok", compile_ok)
    source_registry_ok = _require_bool("source_registry_ok", source_registry_ok)
    signal_provenance_ok = _require_bool("signal_provenance_ok", signal_provenance_ok)
    route_economic_sanity_ok = _require_bool("route_economic_sanity_ok", route_economic_sanity_ok)
    execution_ok = _require_bool("execution_ok", execution_ok)
    oracle_freshness_ok = _require_bool("oracle_freshness_ok", oracle_freshness_ok)
    budget_ok = _require_bool("budget_ok", budget_ok)
    candidate_set_ok = _require_bool("candidate_set_ok", candidate_set_ok)
    decision_ok = _require_bool("decision_ok", decision_ok)
    kill_switch_ok = _require_bool("kill_switch_ok", kill_switch_ok)
    tx_envelope_ok = _require_bool("tx_envelope_ok", tx_envelope_ok)
    session_state_ok = _require_bool("session_state_ok", session_state_ok)
    session_capability_binding_ok = _require_bool(
        "session_capability_binding_ok", session_capability_binding_ok
    )
    wallet_capability_ok = _require_bool("wallet_capability_ok", wallet_capability_ok)
    nonce_ok = _require_bool("nonce_ok", nonce_ok)

    guard_bundle_ok = all(
        (
            policy_artifact_ok,
            tau_policy_bundle_ok,
            signer_binding_ok,
            compile_ok,
            source_registry_ok,
            signal_provenance_ok,
            route_economic_sanity_ok,
            execution_ok,
            oracle_freshness_ok,
            budget_ok,
            candidate_set_ok,
            decision_ok,
            kill_switch_ok,
            tx_envelope_ok,
            session_state_ok,
            session_capability_binding_ok,
            wallet_capability_ok,
            nonce_ok,
        )
    )
    emit_allowed = emit_requested and guard_bundle_ok
    if not emit_requested:
        return StrategySystemComposeResult(
            ok=True,
            emit_allowed=False,
            policy_artifact_ok=policy_artifact_ok,
            tau_policy_bundle_ok=tau_policy_bundle_ok,
            signer_binding_ok=signer_binding_ok,
            compile_ok=compile_ok,
            source_registry_ok=source_registry_ok,
            signal_provenance_ok=signal_provenance_ok,
            route_economic_sanity_ok=route_economic_sanity_ok,
            execution_ok=execution_ok,
            oracle_freshness_ok=oracle_freshness_ok,
            budget_ok=budget_ok,
            candidate_set_ok=candidate_set_ok,
            decision_ok=decision_ok,
            kill_switch_ok=kill_switch_ok,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
        )
    if not policy_artifact_ok:
        error = "policy_artifact_rejected"
    elif not tau_policy_bundle_ok:
        error = "tau_policy_bundle_rejected"
    elif not signer_binding_ok:
        error = "signer_binding_rejected"
    elif not compile_ok:
        error = "compile_contract_rejected"
    elif not source_registry_ok:
        error = "source_registry_rejected"
    elif not signal_provenance_ok:
        error = "signal_provenance_rejected"
    elif not route_economic_sanity_ok:
        error = "route_economic_sanity_rejected"
    elif not execution_ok:
        error = "execution_rejected"
    elif not oracle_freshness_ok:
        error = "oracle_freshness_rejected"
    elif not budget_ok:
        error = "budget_rejected"
    elif not candidate_set_ok:
        error = "candidate_set_rejected"
    elif not decision_ok:
        error = "decision_rejected"
    elif not kill_switch_ok:
        error = "kill_switch_rejected"
    elif not tx_envelope_ok:
        error = "tx_envelope_rejected"
    elif not session_state_ok:
        error = "session_state_rejected"
    elif not session_capability_binding_ok:
        error = "session_capability_binding_rejected"
    elif not wallet_capability_ok:
        error = "wallet_capability_rejected"
    elif not nonce_ok:
        error = "nonce_rejected"
    else:
        error = None
    return StrategySystemComposeResult(
        ok=guard_bundle_ok,
        emit_allowed=emit_allowed,
        policy_artifact_ok=policy_artifact_ok,
        tau_policy_bundle_ok=tau_policy_bundle_ok,
        signer_binding_ok=signer_binding_ok,
        compile_ok=compile_ok,
        source_registry_ok=source_registry_ok,
        signal_provenance_ok=signal_provenance_ok,
        route_economic_sanity_ok=route_economic_sanity_ok,
        execution_ok=execution_ok,
        oracle_freshness_ok=oracle_freshness_ok,
        budget_ok=budget_ok,
        candidate_set_ok=candidate_set_ok,
        decision_ok=decision_ok,
        kill_switch_ok=kill_switch_ok,
        tx_envelope_ok=tx_envelope_ok,
        session_state_ok=session_state_ok,
        session_capability_binding_ok=session_capability_binding_ok,
        wallet_capability_ok=wallet_capability_ok,
        nonce_ok=nonce_ok,
        error=error,
    )
