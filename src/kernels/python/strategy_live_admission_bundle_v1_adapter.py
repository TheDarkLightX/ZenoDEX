from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class StrategyLiveAdmissionBundleResult:
    ok: bool
    source_registry_ok: bool
    signal_provenance_ok: bool
    route_economic_sanity_ok: bool
    execution_ok: bool
    oracle_freshness_ok: bool
    budget_ok: bool
    tx_envelope_ok: bool
    session_state_ok: bool
    session_capability_binding_ok: bool
    wallet_capability_ok: bool
    nonce_ok: bool
    error: str | None = None


def check_strategy_live_admission_bundle(
    *,
    source_registry_ok: bool,
    signal_provenance_ok: bool,
    route_economic_sanity_ok: bool,
    execution_ok: bool,
    oracle_freshness_ok: bool,
    budget_ok: bool,
    tx_envelope_ok: bool,
    session_state_ok: bool,
    session_capability_binding_ok: bool,
    wallet_capability_ok: bool,
    nonce_ok: bool,
) -> StrategyLiveAdmissionBundleResult:
    source_registry_ok = _require_bool("source_registry_ok", source_registry_ok)
    signal_provenance_ok = _require_bool("signal_provenance_ok", signal_provenance_ok)
    route_economic_sanity_ok = _require_bool("route_economic_sanity_ok", route_economic_sanity_ok)
    execution_ok = _require_bool("execution_ok", execution_ok)
    oracle_freshness_ok = _require_bool("oracle_freshness_ok", oracle_freshness_ok)
    budget_ok = _require_bool("budget_ok", budget_ok)
    tx_envelope_ok = _require_bool("tx_envelope_ok", tx_envelope_ok)
    session_state_ok = _require_bool("session_state_ok", session_state_ok)
    session_capability_binding_ok = _require_bool(
        "session_capability_binding_ok", session_capability_binding_ok
    )
    wallet_capability_ok = _require_bool("wallet_capability_ok", wallet_capability_ok)
    nonce_ok = _require_bool("nonce_ok", nonce_ok)

    if not source_registry_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=False,
            signal_provenance_ok=signal_provenance_ok,
            route_economic_sanity_ok=route_economic_sanity_ok,
            execution_ok=execution_ok,
            oracle_freshness_ok=oracle_freshness_ok,
            budget_ok=budget_ok,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="source_registry_rejected",
        )
    if not signal_provenance_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=False,
            route_economic_sanity_ok=route_economic_sanity_ok,
            execution_ok=execution_ok,
            oracle_freshness_ok=oracle_freshness_ok,
            budget_ok=budget_ok,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="signal_provenance_rejected",
        )
    if not route_economic_sanity_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=False,
            execution_ok=execution_ok,
            oracle_freshness_ok=oracle_freshness_ok,
            budget_ok=budget_ok,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="route_economic_sanity_rejected",
        )
    if not execution_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=False,
            oracle_freshness_ok=oracle_freshness_ok,
            budget_ok=budget_ok,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="execution_rejected",
        )
    if not oracle_freshness_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=False,
            budget_ok=budget_ok,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="oracle_freshness_rejected",
        )
    if not budget_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=False,
            tx_envelope_ok=tx_envelope_ok,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="budget_rejected",
        )
    if not tx_envelope_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            tx_envelope_ok=False,
            session_state_ok=session_state_ok,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="tx_envelope_rejected",
        )
    if not session_state_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            tx_envelope_ok=True,
            session_state_ok=False,
            session_capability_binding_ok=session_capability_binding_ok,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="session_state_rejected",
        )
    if not session_capability_binding_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            tx_envelope_ok=True,
            session_state_ok=True,
            session_capability_binding_ok=False,
            wallet_capability_ok=wallet_capability_ok,
            nonce_ok=nonce_ok,
            error="session_capability_binding_rejected",
        )
    if not wallet_capability_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            tx_envelope_ok=True,
            session_state_ok=True,
            session_capability_binding_ok=True,
            wallet_capability_ok=False,
            nonce_ok=nonce_ok,
            error="wallet_capability_rejected",
        )
    if not nonce_ok:
        return StrategyLiveAdmissionBundleResult(
            ok=False,
            source_registry_ok=True,
            signal_provenance_ok=True,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            tx_envelope_ok=True,
            session_state_ok=True,
            session_capability_binding_ok=True,
            wallet_capability_ok=True,
            nonce_ok=False,
            error="nonce_rejected",
        )
    return StrategyLiveAdmissionBundleResult(
        ok=True,
        source_registry_ok=True,
        signal_provenance_ok=True,
        route_economic_sanity_ok=True,
        execution_ok=True,
        oracle_freshness_ok=True,
        budget_ok=True,
        tx_envelope_ok=True,
        session_state_ok=True,
        session_capability_binding_ok=True,
        wallet_capability_ok=True,
        nonce_ok=True,
    )
