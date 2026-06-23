from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..integration.autotrader_signal_registry import ExternalSignalSourceRegistry
from ..integration.autotrader_signals import (
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    QuoteReceiptSignalPacket,
)
from ..integration.tau_witness import (
    AUTOTRADER_BUDGET_GUARD_V1,
    AUTOTRADER_COMPILATION_WITNESS_V1,
    AUTOTRADER_COMPILE_CONTRACT_V1,
    AUTOTRADER_EXECUTION_GUARD_V1,
    AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1,
    AUTOTRADER_NONCE_GUARD_V1,
    AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1,
    AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1,
    AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1,
    AUTOTRADER_SESSION_STATE_GUARD_V1,
    AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1,
    AUTOTRADER_WALLET_CAPABILITY_GUARD_V1,
    build_autotrader_budget_guard_v1_step,
    build_autotrader_compilation_witness_v1_step,
    build_autotrader_compile_contract_v1_step,
    build_autotrader_execution_guard_v1_step,
    build_autotrader_external_signal_source_registry_guard_v1_step,
    build_autotrader_nonce_guard_v1_step,
    build_autotrader_oracle_freshness_guard_v1_step,
    build_autotrader_route_economic_sanity_guard_v1_step,
    build_autotrader_session_capability_binding_guard_v1_step,
    build_autotrader_session_state_guard_v1_step,
    build_autotrader_signal_provenance_guard_v1_step,
    build_autotrader_wallet_capability_guard_v1_step,
)
from ..kernels.python.strategy_budget_guard_v1_adapter import (
    MAX_U32,
    StrategyBudgetState,
    consume_order,
)
from ..kernels.python.strategy_compilation_witness_v1_adapter import (
    check_strategy_compilation_witness,
)
from ..kernels.python.strategy_compile_contract_v1_adapter import (
    check_strategy_compile_contract,
)
from ..kernels.python.strategy_execution_guard_v1_adapter import check_order_execution
from ..kernels.python.strategy_external_signal_source_registry_guard_v1_adapter import (
    check_strategy_external_signal_source_registry_guard,
)
from ..kernels.python.strategy_nonce_guard_v1_adapter import check_strategy_nonce
from ..kernels.python.strategy_oracle_freshness_guard_v1_adapter import check_oracle_freshness
from ..kernels.python.strategy_route_economic_sanity_guard_v1_adapter import (
    StrategyRouteEconomicSanityInputs,
    check_strategy_route_economic_sanity,
)
from ..kernels.python.strategy_session_capability_binding_guard_v1_adapter import (
    check_strategy_session_capability_binding,
)
from ..kernels.python.strategy_session_state_guard_v1_adapter import check_strategy_session_state
from ..kernels.python.strategy_signal_provenance_guard_v1_adapter import (
    check_signal_provenance,
    signal_source_kind_code,
    signal_trust_tier_code,
)
from ..kernels.python.strategy_wallet_capability_guard_v1_adapter import check_wallet_capability
from .policy_artifacts import StrategySourceArtifact
from .route_economic_sanity import ROUTE_ECONOMIC_SANITY_POLICY, RouteEconomicSanitySnapshot
from .strategy_ir import PolicyBackend, StrategyAction, StrategyIR

TAU_POLICY_RECEIPT_SCHEMA = "zenodex/tau-policy-receipt/v1"


@dataclass(frozen=True)
class TauPolicyReceipt:
    strategy_id: str
    strategy_hash: str
    spec_id: str
    gate_output: str
    steps: tuple[dict[str, int], ...]
    expected_ok: bool

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": TAU_POLICY_RECEIPT_SCHEMA,
            "strategy_id": self.strategy_id,
            "strategy_hash": self.strategy_hash,
            "spec_id": self.spec_id,
            "gate_output": self.gate_output,
            "steps": [dict(step) for step in self.steps],
            "expected_ok": bool(self.expected_ok),
        }


def _require_tau_policy_binding(*, strategy: StrategyIR, spec_id: str) -> None:
    if strategy.policy_backend is PolicyBackend.TAU and spec_id not in strategy.tau_policy_specs:
        got = ", ".join(strategy.tau_policy_specs) or "<none>"
        raise ValueError(f"tau strategy must bind {spec_id}, got {got}")


def build_budget_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    state: StrategyBudgetState,
    order_amount: int,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(state, StrategyBudgetState):
        raise TypeError("state must be a StrategyBudgetState")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_BUDGET_GUARD_V1.spec_id)

    local_result = consume_order(
        state=state,
        order_amount=order_amount,
        per_order_limit=strategy.notional_caps.per_order_max,
        window_budget=strategy.notional_caps.per_window_max,
    )
    spent_after = state.spent_in_window + int(order_amount)
    if spent_after > MAX_U32:
        raise ValueError("tau budget witness overflow")
    if local_result.ok:
        spent_after = local_result.state.spent_in_window

    step = build_autotrader_budget_guard_v1_step(
        spent_before=state.spent_in_window,
        order_amount=int(order_amount),
        per_order_limit=strategy.notional_caps.per_order_max,
        window_budget=strategy.notional_caps.per_window_max,
        spent_after=int(spent_after),
        kill_switch_active=1 if state.kill_switch_on else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_BUDGET_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_BUDGET_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_compile_contract_tau_policy_receipt(*, strategy: StrategyIR) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")

    local_result = check_strategy_compile_contract(strategy)
    step = build_autotrader_compile_contract_v1_step(
        backend_ok=1 if local_result.backend_ok else 0,
        template_ok=1 if local_result.template_ok else 0,
        strategy_id_ok=1 if local_result.strategy_id_ok else 0,
        owner_binding_ok=1 if local_result.owner_binding_ok else 0,
        asset_scope_ok=1 if local_result.asset_scope_ok else 0,
        required_params_ok=1 if local_result.required_params_ok else 0,
        action_scope_ok=1 if local_result.action_scope_ok else 0,
        notional_chain_ok=1 if local_result.notional_chain_ok else 0,
        slippage_ok=1 if local_result.slippage_ok else 0,
        oracle_window_ok=1 if local_result.oracle_window_ok else 0,
        strategy_window_ok=1 if local_result.strategy_window_ok else 0,
        controls_ok=1 if local_result.controls_ok else 0,
        tau_bundle_ok=1 if local_result.tau_bundle_ok else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_COMPILE_CONTRACT_V1.spec_id,
        gate_output=AUTOTRADER_COMPILE_CONTRACT_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_compilation_witness_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    source_artifact: StrategySourceArtifact,
    compile_contract_tau_receipt: Mapping[str, Any],
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(source_artifact, StrategySourceArtifact):
        raise TypeError("source_artifact must be a StrategySourceArtifact")
    if not isinstance(compile_contract_tau_receipt, Mapping):
        raise TypeError("compile_contract_tau_receipt must be an object")
    compile_contract_tau_receipt = dict(compile_contract_tau_receipt)

    compile_contract_ok = bool(compile_contract_tau_receipt.get("expected_ok")) and (
        compile_contract_tau_receipt.get("spec_id") == AUTOTRADER_COMPILE_CONTRACT_V1.spec_id
    )
    local_result = check_strategy_compilation_witness(
        source_artifact=source_artifact,
        strategy=strategy,
        compile_contract_ok=compile_contract_ok,
    )
    step = build_autotrader_compilation_witness_v1_step(
        source_form_ok=1 if local_result.source_form_ok else 0,
        strategy_hash_match=1 if local_result.strategy_hash_match else 0,
        owner_match=1 if local_result.owner_match else 0,
        backend_match=1 if local_result.backend_match else 0,
        template_match=1 if local_result.template_match else 0,
        asset_universe_match=1 if local_result.asset_universe_match else 0,
        allowed_actions_match=1 if local_result.allowed_actions_match else 0,
        notional_caps_match=1 if local_result.notional_caps_match else 0,
        risk_limits_match=1 if local_result.risk_limits_match else 0,
        strategy_window_match=1 if local_result.strategy_window_match else 0,
        controls_match=1 if local_result.controls_match else 0,
        template_params_match=1 if local_result.template_params_match else 0,
        tau_policy_specs_match=1 if local_result.tau_policy_specs_match else 0,
        compile_contract_ok=1 if local_result.compile_contract_ok else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_COMPILATION_WITNESS_V1.spec_id,
        gate_output=AUTOTRADER_COMPILATION_WITNESS_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_execution_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    current_epoch: int,
    last_action_epoch: int | None,
    projected_live_orders: int,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_EXECUTION_GUARD_V1.spec_id)

    local_result = check_order_execution(
        current_epoch=current_epoch,
        valid_from_epoch=strategy.strategy_window.valid_from_epoch,
        valid_until_epoch=strategy.strategy_window.valid_until_epoch,
        last_action_epoch=last_action_epoch,
        cadence_epochs=int(strategy.template_params["cadence_epochs"]),
        min_order_spacing_epochs=strategy.strategy_window.min_order_spacing_epochs,
        projected_live_orders=projected_live_orders,
        max_live_orders=strategy.controls.max_live_orders,
    )
    step = build_autotrader_execution_guard_v1_step(
        current_epoch=int(current_epoch),
        valid_from_epoch=strategy.strategy_window.valid_from_epoch,
        valid_until_epoch=strategy.strategy_window.valid_until_epoch,
        last_action_known=0 if last_action_epoch is None else 1,
        last_action_epoch=0 if last_action_epoch is None else int(last_action_epoch),
        cadence_epochs=int(strategy.template_params["cadence_epochs"]),
        min_order_spacing_epochs=strategy.strategy_window.min_order_spacing_epochs,
        projected_live_orders=int(projected_live_orders),
        max_live_orders=strategy.controls.max_live_orders,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_EXECUTION_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_EXECUTION_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_oracle_freshness_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    current_epoch: int,
    quote_epoch: int,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.spec_id)

    local_result = check_oracle_freshness(
        current_epoch=current_epoch,
        quote_epoch=quote_epoch,
        max_oracle_staleness_epochs=strategy.risk_limits.max_oracle_staleness_epochs,
    )
    step = build_autotrader_oracle_freshness_guard_v1_step(
        current_epoch=int(current_epoch),
        quote_epoch=int(quote_epoch),
        max_oracle_staleness_epochs=strategy.risk_limits.max_oracle_staleness_epochs,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_route_economic_sanity_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    snapshot: RouteEconomicSanitySnapshot,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(snapshot, RouteEconomicSanitySnapshot):
        raise TypeError("snapshot must be a RouteEconomicSanitySnapshot")
    _require_tau_policy_binding(
        strategy=strategy,
        spec_id=AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.spec_id,
    )

    local_result = check_strategy_route_economic_sanity(
        inputs=StrategyRouteEconomicSanityInputs(
            receipt_verified=bool(snapshot.receipt_verified),
            route_kind_supported=bool(snapshot.route_kind_supported),
            body_pair_valid=bool(snapshot.body_pair_valid),
            legs_present=bool(snapshot.legs_present),
            all_legs_single_hop=bool(snapshot.all_legs_single_hop),
            all_legs_match_body_pair=bool(snapshot.all_legs_match_body_pair),
            multi_hop_present=bool(snapshot.multi_hop_present),
            max_hop_input_vs_reserve_bps=int(snapshot.max_hop_input_vs_reserve_bps),
            max_hop_output_vs_reserve_bps=int(snapshot.max_hop_output_vs_reserve_bps),
            max_hop_price_impact_bps=int(snapshot.max_hop_price_impact_bps),
        ),
        policy=ROUTE_ECONOMIC_SANITY_POLICY,
    )
    step = build_autotrader_route_economic_sanity_guard_v1_step(
        receipt_verified=1 if snapshot.receipt_verified else 0,
        route_kind_supported=1 if snapshot.route_kind_supported else 0,
        body_pair_valid=1 if snapshot.body_pair_valid else 0,
        legs_present=1 if snapshot.legs_present else 0,
        all_legs_single_hop=1 if snapshot.all_legs_single_hop else 0,
        all_legs_match_body_pair=1 if snapshot.all_legs_match_body_pair else 0,
        multi_hop_present=1 if snapshot.multi_hop_present else 0,
        max_hop_input_vs_reserve_bps=int(snapshot.max_hop_input_vs_reserve_bps),
        max_hop_output_vs_reserve_bps=int(snapshot.max_hop_output_vs_reserve_bps),
        max_hop_price_impact_bps=int(snapshot.max_hop_price_impact_bps),
        input_stress_extreme_bps=ROUTE_ECONOMIC_SANITY_POLICY.input_stress_extreme_bps,
        output_depletion_extreme_bps=ROUTE_ECONOMIC_SANITY_POLICY.output_depletion_extreme_bps,
        price_impact_extreme_bps=ROUTE_ECONOMIC_SANITY_POLICY.price_impact_extreme_bps,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_signal_provenance_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    packet: QuoteReceiptSignalPacket,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(packet, QuoteReceiptSignalPacket):
        raise TypeError("packet must be a QuoteReceiptSignalPacket")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.spec_id)

    local_result = check_signal_provenance(
        packet=packet,
        require_quote_receipts=strategy.risk_limits.require_quote_receipts,
    )
    step = build_autotrader_signal_provenance_guard_v1_step(
        source_kind_code=signal_source_kind_code(packet.source_kind),
        trust_tier_code=signal_trust_tier_code(packet.trust_tier),
        quote_receipt_present=1 if packet.quote_receipt_present else 0,
        quote_receipt_verified=1 if packet.quote_receipt_verified else 0,
        quote_epoch_present=1 if packet.quote_epoch_present else 0,
        binding_ok=1 if packet.binding_ok else 0,
        auth_ok=1 if packet.auth_ok else 0,
        source_available=1 if packet.source_available else 0,
        require_quote_receipts=1 if strategy.risk_limits.require_quote_receipts else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_external_signal_source_registry_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    signal: ExternalSignalObservation,
    registry: ExternalSignalSourceRegistry | None,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(signal, ExternalSignalObservation):
        raise TypeError("signal must be an ExternalSignalObservation")
    if registry is not None and not isinstance(registry, ExternalSignalSourceRegistry):
        raise TypeError("registry must be an ExternalSignalSourceRegistry or None")
    _require_tau_policy_binding(
        strategy=strategy,
        spec_id=AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1.spec_id,
    )

    entry = None if registry is None else registry.get(signal.source_id)
    if entry is None:
        local_result = check_strategy_external_signal_source_registry_guard(
            registry_entry_present=False,
            registry_entry_enabled=False,
            observed_source_kind_code=signal_source_kind_code(signal.source_kind),
            observed_trust_tier_code=signal_trust_tier_code(signal.trust_tier),
            advisory_only=bool(signal.advisory_only),
            auth_ok=bool(signal.auth_ok),
            freshness_ok=bool(signal.freshness_ok),
            registered_source_kind_code=0,
            allow_advisory=False,
            allow_attested=False,
            allow_verified=False,
            allow_protocol=False,
            require_advisory_only=False,
            require_auth=False,
            require_freshness=False,
        )
        registered_source_kind_code = 0
        allow_advisory = False
        allow_attested = False
        allow_verified = False
        allow_protocol = False
        require_advisory_only = False
        require_auth = False
        require_freshness = False
        registry_entry_enabled = False
    else:
        local_result = entry.validate(signal)
        registered_source_kind_code = signal_source_kind_code(entry.source_kind)
        allow_advisory = bool(entry.allow_advisory)
        allow_attested = bool(entry.allow_attested)
        allow_verified = bool(entry.allow_verified)
        allow_protocol = bool(entry.allow_protocol)
        require_advisory_only = bool(entry.require_advisory_only)
        require_auth = bool(entry.require_auth)
        require_freshness = bool(entry.require_freshness)
        registry_entry_enabled = bool(entry.enabled)

    step = build_autotrader_external_signal_source_registry_guard_v1_step(
        registry_entry_present=0 if entry is None else 1,
        registry_entry_enabled=1 if registry_entry_enabled else 0,
        observed_source_kind_code=signal_source_kind_code(signal.source_kind),
        observed_trust_tier_code=signal_trust_tier_code(signal.trust_tier),
        advisory_only=1 if signal.advisory_only else 0,
        auth_ok=1 if signal.auth_ok else 0,
        freshness_ok=1 if signal.freshness_ok else 0,
        registered_source_kind_code=registered_source_kind_code,
        allow_advisory=1 if allow_advisory else 0,
        allow_attested=1 if allow_attested else 0,
        allow_verified=1 if allow_verified else 0,
        allow_protocol=1 if allow_protocol else 0,
        require_advisory_only=1 if require_advisory_only else 0,
        require_auth=1 if require_auth else 0,
        require_freshness=1 if require_freshness else 0,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_wallet_capability_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    capability: AutoTraderWalletCapability,
    signer_pubkey: str,
    chain_id: str,
    current_epoch: int,
    asset_in: str,
    asset_out: str,
    order_amount: int,
    action: StrategyAction,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    if not isinstance(action, StrategyAction):
        raise TypeError("action must be a StrategyAction")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.spec_id)

    local_result = check_wallet_capability(
        capability=capability,
        signer_pubkey=signer_pubkey,
        chain_id=chain_id,
        current_epoch=current_epoch,
        asset_in=asset_in,
        asset_out=asset_out,
        order_amount=order_amount,
        action=action,
    )
    step = build_autotrader_wallet_capability_guard_v1_step(
        enabled=1 if capability.enabled else 0,
        signer_ok=1 if signer_pubkey == capability.owner_pubkey else 0,
        asset_in_allowed=1 if asset_in in capability.allowed_assets else 0,
        asset_out_allowed=1 if asset_out in capability.allowed_assets else 0,
        action_allowed=1 if action in capability.allowed_actions else 0,
        chain_id_ok=1 if chain_id == capability.chain_id else 0,
        current_epoch=int(current_epoch),
        valid_from_epoch=capability.valid_from_epoch,
        valid_until_epoch=capability.valid_until_epoch,
        order_amount=int(order_amount),
        notional_remaining=capability.notional_remaining,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_session_capability_binding_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    capability: AutoTraderWalletCapability,
    chain_id: str,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    _require_tau_policy_binding(
        strategy=strategy,
        spec_id=AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1.spec_id,
    )

    local_result = check_strategy_session_capability_binding(
        strategy=strategy,
        capability=capability,
        chain_id=chain_id,
    )
    step = build_autotrader_session_capability_binding_guard_v1_step(
        session_present=1 if capability.session_id.strip() else 0,
        owner_binding_ok=1 if capability.owner_pubkey == strategy.owner_pubkey else 0,
        chain_binding_ok=1 if capability.chain_id == chain_id else 0,
        asset_scope_ok=1
        if set(capability.allowed_assets).issubset(set(strategy.asset_universe))
        else 0,
        action_scope_ok=1
        if set(capability.allowed_actions).issubset(set(strategy.allowed_actions))
        else 0,
        capability_valid_from_epoch=capability.valid_from_epoch,
        capability_valid_until_epoch=capability.valid_until_epoch,
        strategy_valid_from_epoch=strategy.strategy_window.valid_from_epoch,
        strategy_valid_until_epoch=strategy.strategy_window.valid_until_epoch,
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_session_state_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    session_state: AutoTraderSessionState,
    capability: AutoTraderWalletCapability,
    chain_id: str,
    current_epoch: int,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(session_state, AutoTraderSessionState):
        raise TypeError("session_state must be an AutoTraderSessionState")
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_SESSION_STATE_GUARD_V1.spec_id)

    local_result = check_strategy_session_state(
        session_state=session_state,
        capability=capability,
        chain_id=chain_id,
        current_epoch=int(current_epoch),
    )
    step = build_autotrader_session_state_guard_v1_step(
        enabled=1 if session_state.enabled else 0,
        session_binding_ok=1 if session_state.session_id == capability.session_id else 0,
        owner_binding_ok=1 if session_state.owner_pubkey == capability.owner_pubkey else 0,
        chain_binding_ok=1 if session_state.chain_id == capability.chain_id == chain_id else 0,
        revocation_epoch_present=1 if session_state.revoked_at_epoch is not None else 0,
        current_epoch=int(current_epoch),
        revoked_at_epoch=int(session_state.revoked_at_epoch or 0),
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_SESSION_STATE_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_SESSION_STATE_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )


def build_nonce_guard_tau_policy_receipt(
    *,
    strategy: StrategyIR,
    intent_nonce: int,
    last_used_nonce: int,
    expected_nonce: int,
) -> TauPolicyReceipt:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    _require_tau_policy_binding(strategy=strategy, spec_id=AUTOTRADER_NONCE_GUARD_V1.spec_id)

    local_result = check_strategy_nonce(
        intent_nonce=int(intent_nonce),
        last_used_nonce=int(last_used_nonce),
        expected_nonce=int(expected_nonce),
    )
    step = build_autotrader_nonce_guard_v1_step(
        intent_nonce=int(intent_nonce),
        last_used_nonce=int(last_used_nonce),
        expected_nonce=int(expected_nonce),
    )
    return TauPolicyReceipt(
        strategy_id=strategy.strategy_id,
        strategy_hash=strategy.strategy_hash_hex(),
        spec_id=AUTOTRADER_NONCE_GUARD_V1.spec_id,
        gate_output=AUTOTRADER_NONCE_GUARD_V1.gate_output,
        steps=(step,),
        expected_ok=bool(local_result.ok),
    )
