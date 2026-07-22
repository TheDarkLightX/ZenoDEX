"""
Policy-constrained auto-trader controller (imperative shell).

This module evaluates a bounded StrategyIR against a verified quote receipt and
returns deterministic intent-emission decisions. It does not sign or submit
transactions, and it does not mutate functional-core state.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field, replace
from enum import Enum
from typing import Mapping

from ..agents.intent_signer import create_swap_intents_from_quote_receipt
from ..agents.route_economic_sanity import build_route_economic_sanity_snapshot
from ..agents.strategy_ir import (
    PolicyBackend,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    strategy_budget_window_id,
)
from ..agents.tau_policy_adapter import (
    TauPolicyReceipt,
    build_budget_guard_tau_policy_receipt,
    build_execution_guard_tau_policy_receipt,
    build_oracle_freshness_guard_tau_policy_receipt,
    build_route_economic_sanity_guard_tau_policy_receipt,
    build_signal_provenance_guard_tau_policy_receipt,
)
from ..kernels.python.strategy_budget_guard_v1_adapter import (
    MAX_U32,
    StrategyBudgetResult,
    StrategyBudgetState,
    consume_order,
    init_state,
    roll_window,
)
from ..kernels.python.strategy_execution_guard_v1_adapter import check_order_execution
from ..kernels.python.strategy_oracle_freshness_guard_v1_adapter import check_oracle_freshness
from ..kernels.python.strategy_signal_provenance_guard_v1_adapter import check_signal_provenance
from ..state.immutable_json import snapshot_json_mapping
from ..state.intents import Intent
from ..state.pools import PoolState
from .autotrader_signals import build_quote_receipt_signal_packet
from .tau_runner import TauRunError, find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    AUTOTRADER_BUDGET_GUARD_V1,
    AUTOTRADER_EXECUTION_GUARD_V1,
    AUTOTRADER_NONCE_GUARD_V1,
    AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1,
    AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1,
    AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1,
    AUTOTRADER_WALLET_CAPABILITY_GUARD_V1,
)

_SIGNAL_PACKET_BUILD_ERRORS = (TypeError, ValueError)
_INTENT_CONSTRUCTION_ERRORS = (TypeError, ValueError)
_TAU_POLICY_RUNNER_ERRORS = (TauRunError, RuntimeError, ValueError, OSError)


class AutoTraderDecisionTag(Enum):
    SUBMIT = "submit"
    SKIP = "skip"
    REJECT = "reject"


@dataclass(frozen=True)
class AutoTraderTauConfig:
    enabled: bool = False
    timeout_s: float = 2.0
    tau_bin: str | None = None
    allow_path_lookup: bool = False


@dataclass(frozen=True)
class AutoTraderControllerState:
    budget_state: StrategyBudgetState = field(default_factory=init_state)
    last_action_epoch: int | None = None
    lifetime_spent: int = 0
    live_orders: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.budget_state, StrategyBudgetState):
            raise TypeError("budget_state must be a StrategyBudgetState")
        if self.last_action_epoch is not None:
            _require_u32_int("last_action_epoch", self.last_action_epoch)
        _require_u32_int("lifetime_spent", self.lifetime_spent, minimum=0)
        _require_u32_int("live_orders", self.live_orders, minimum=0)


@dataclass(frozen=True)
class AutoTraderGuardState:
    signal_provenance_ok: bool = False
    route_economic_sanity_ok: bool = False
    execution_ok: bool = False
    oracle_freshness_ok: bool = False
    budget_ok: bool = False


_DEFAULT_GUARD_STATE = AutoTraderGuardState()


@dataclass(frozen=True)
class AutoTraderDecision:
    tag: AutoTraderDecisionTag
    reason: str
    explain: tuple[str, ...]
    state: AutoTraderControllerState
    guard_state: AutoTraderGuardState = field(default_factory=AutoTraderGuardState)
    intents: tuple[Intent, ...] = ()
    tau_policy_receipt: TauPolicyReceipt | None = None

    @property
    def should_submit(self) -> bool:
        return self.tag is AutoTraderDecisionTag.SUBMIT


def _require_u32_int(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > MAX_U32:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def _require_safe_receipt_body(receipt: Mapping[str, object]) -> dict[str, object]:
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        raise ValueError("missing receipt.body")
    return dict(body)


def _require_receipt_int(body: Mapping[str, object], key: str) -> int:
    value = body.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"receipt body field must be an int: {key}")
    return int(value)


def _require_template_int(strategy: StrategyIR, key: str, *, minimum: int = 1) -> int:
    value = strategy.template_params.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"strategy template param must be an int: {key}")
    out = int(value)
    if out < minimum or out > MAX_U32:
        raise ValueError(f"strategy template param out of range: {key}={out}")
    return out


def _require_template_token(strategy: StrategyIR, key: str) -> str:
    value = strategy.template_params.get(key)
    if not isinstance(value, str):
        raise ValueError(f"strategy template param must be a string: {key}")
    text = value.strip()
    if not text:
        raise ValueError(f"strategy template param must be non-empty: {key}")
    return text


def _reject(
    *,
    state: AutoTraderControllerState,
    reason: str,
    explain: tuple[str, ...],
    guard_state: AutoTraderGuardState = _DEFAULT_GUARD_STATE,
    tau_policy_receipt: TauPolicyReceipt | None = None,
) -> AutoTraderDecision:
    return AutoTraderDecision(
        tag=AutoTraderDecisionTag.REJECT,
        reason=reason,
        explain=explain,
        state=state,
        guard_state=guard_state,
        tau_policy_receipt=tau_policy_receipt,
    )


def _skip(
    *,
    state: AutoTraderControllerState,
    reason: str,
    explain: tuple[str, ...],
    guard_state: AutoTraderGuardState = _DEFAULT_GUARD_STATE,
) -> AutoTraderDecision:
    return AutoTraderDecision(
        tag=AutoTraderDecisionTag.SKIP,
        reason=reason,
        explain=explain,
        state=state,
        guard_state=guard_state,
    )


def _submit(
    *,
    state: AutoTraderControllerState,
    reason: str,
    explain: tuple[str, ...],
    guard_state: AutoTraderGuardState = _DEFAULT_GUARD_STATE,
    intents: tuple[Intent, ...],
    tau_policy_receipt: TauPolicyReceipt | None = None,
) -> AutoTraderDecision:
    return AutoTraderDecision(
        tag=AutoTraderDecisionTag.SUBMIT,
        reason=reason,
        explain=explain,
        state=state,
        guard_state=guard_state,
        intents=intents,
        tau_policy_receipt=tau_policy_receipt,
    )


def _resolve_tau_bin(config: AutoTraderTauConfig) -> tuple[bool, str | None, str | None]:
    if config.tau_bin:
        tau_bin = str(config.tau_bin)
        if not config.allow_path_lookup:
            if not os.path.isabs(tau_bin):
                return False, None, "tau_bin must be an absolute path when allow_path_lookup=False"
            if not (os.path.isfile(tau_bin) and os.access(tau_bin, os.X_OK)):
                return False, None, f"tau_bin is not an executable file: {tau_bin}"
        return True, tau_bin, None
    if config.allow_path_lookup:
        tau_bin = find_tau_bin()
        if tau_bin:
            return True, tau_bin, None
        return False, None, "tau binary not found (fail-closed)"
    return False, None, "tau_bin not configured (set AutoTraderTauConfig.tau_bin)"


def _budget_failure_tag(result: StrategyBudgetResult) -> AutoTraderDecisionTag:
    if result.error in {"kill_switch_active", "window_budget_exceeded"}:
        return AutoTraderDecisionTag.SKIP
    return AutoTraderDecisionTag.REJECT


def _execution_failure_tag(error: str | None) -> AutoTraderDecisionTag:
    if error is None:
        return AutoTraderDecisionTag.REJECT
    if error.startswith(
        (
            "strategy_window_not_open:",
            "strategy_window_expired:",
            "cadence_not_elapsed:",
            "max_live_orders_reached:",
        )
    ):
        return AutoTraderDecisionTag.SKIP
    return AutoTraderDecisionTag.REJECT


def _oracle_failure_tag(error: str | None) -> AutoTraderDecisionTag:
    if error is None:
        return AutoTraderDecisionTag.REJECT
    if error.startswith("quote_receipt_stale:"):
        return AutoTraderDecisionTag.SKIP
    return AutoTraderDecisionTag.REJECT


def _route_economic_sanity_failure_tag(error: str | None) -> AutoTraderDecisionTag:
    if error is None:
        return AutoTraderDecisionTag.REJECT
    if error.startswith(
        (
            "route_extreme_input_stress:",
            "route_extreme_output_depletion:",
            "route_extreme_price_impact:",
        )
    ):
        return AutoTraderDecisionTag.SKIP
    return AutoTraderDecisionTag.REJECT


def _verify_tau_policy_receipt(
    *,
    tau_bin: str,
    config: AutoTraderTauConfig,
    receipt: TauPolicyReceipt,
) -> str | None:
    try:
        if receipt.spec_id == AUTOTRADER_BUDGET_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_BUDGET_GUARD_V1.path
        elif receipt.spec_id == AUTOTRADER_EXECUTION_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_EXECUTION_GUARD_V1.path
        elif receipt.spec_id == AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.path
        elif receipt.spec_id == AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.path
        elif receipt.spec_id == AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.path
        elif receipt.spec_id == AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.path
        elif receipt.spec_id == AUTOTRADER_NONCE_GUARD_V1.spec_id:
            spec_path = AUTOTRADER_NONCE_GUARD_V1.path
        else:
            return f"tau_policy_unknown_spec:{receipt.spec_id}"
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=list(receipt.steps),
            timeout_s=config.timeout_s,
        )
    except _TAU_POLICY_RUNNER_ERRORS as exc:
        return f"tau_policy_runner_error:{type(exc).__name__}:{exc}"
    tau_gate_value = outputs.get(0, {}).get(receipt.gate_output)
    if tau_gate_value is None:
        return f"tau_policy_missing_output:{receipt.gate_output}"
    tau_ok = int(tau_gate_value) == 1
    if tau_ok != receipt.expected_ok:
        return (
            "tau_policy_mismatch:"
            f"local={int(receipt.expected_ok)},tau={int(tau_ok)},expected={int(receipt.expected_ok)}"
        )
    return None


def evaluate_autotrader_quote_receipt(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    intent_deadline: int,
    slippage_bps: int | None = None,
    nonce_start: int | None = None,
    tau_config: AutoTraderTauConfig | None = None,
) -> AutoTraderDecision:
    """
    Evaluate one quote receipt against a compiled strategy.

    Phase 2 scope:
    - DCA only
    - exact-in route receipts only
    - emits swap intents in dry-run/shadow style, never signs or submits
    """

    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(controller_state, AutoTraderControllerState):
        raise TypeError("controller_state must be an AutoTraderControllerState")
    if not isinstance(receipt, Mapping):
        raise TypeError("receipt must be a mapping")
    if not isinstance(pools_by_id, Mapping):
        raise TypeError("pools_by_id must be a mapping")
    receipt_snapshot = snapshot_json_mapping(receipt, name="receipt")

    current_epoch = _require_u32_int("current_epoch", current_epoch)
    intent_deadline = _require_u32_int("intent_deadline", intent_deadline, minimum=1)

    explain: list[str] = [
        f"strategy_id={strategy.strategy_id}",
        f"backend={strategy.policy_backend.value}",
        f"template={strategy.template.value}",
        f"epoch={current_epoch}",
    ]
    guard_state = AutoTraderGuardState()

    if strategy.template is not StrategyTemplate.DCA:
        return _reject(
            state=controller_state,
            reason=f"unsupported_strategy_template:{strategy.template.value}",
            explain=tuple(explain),
        )

    if StrategyAction.PLACE_SWAP_EXACT_IN not in strategy.allowed_actions:
        return _reject(
            state=controller_state,
            reason="strategy_action_not_allowed:place_swap_exact_in",
            explain=tuple(explain),
        )

    fixed_order_size = _require_template_int(strategy, "fixed_order_size", minimum=1)
    cadence_epochs = _require_template_int(strategy, "cadence_epochs", minimum=1)
    asset_in = _require_template_token(strategy, "asset_in")
    asset_out = _require_template_token(strategy, "asset_out")
    explain.extend(
        [
            f"fixed_order_size={fixed_order_size}",
            f"cadence_epochs={cadence_epochs}",
            f"asset_pair={asset_in}/{asset_out}",
            f"max_oracle_staleness_epochs={strategy.risk_limits.max_oracle_staleness_epochs}",
        ]
    )

    if asset_in not in strategy.asset_universe or asset_out not in strategy.asset_universe:
        return _reject(
            state=controller_state,
            reason="strategy_assets_outside_universe",
            explain=tuple(explain),
        )

    effective_slippage_bps = strategy.risk_limits.max_slippage_bps if slippage_bps is None else slippage_bps
    effective_slippage_bps = _require_u32_int("slippage_bps", effective_slippage_bps)
    if effective_slippage_bps > strategy.risk_limits.max_slippage_bps:
        return _reject(
            state=controller_state,
            reason=(
                "slippage_limit_exceeded:"
                f"{effective_slippage_bps}>{strategy.risk_limits.max_slippage_bps}"
            ),
            explain=tuple(explain),
        )
    explain.append(f"slippage_bps={effective_slippage_bps}")

    body = _require_safe_receipt_body(receipt_snapshot)
    receipt_kind = str(body.get("kind", "")).strip().lower()
    receipt_asset_in = str(body.get("asset_in", "")).strip()
    receipt_asset_out = str(body.get("asset_out", "")).strip()
    receipt_amount_in = _require_receipt_int(body, "amount_in")
    quote_epoch_raw = body.get("quote_epoch")
    explain.extend(
        [
            f"receipt_kind={receipt_kind}",
            f"receipt_asset_pair={receipt_asset_in}/{receipt_asset_out}",
            f"receipt_amount_in={receipt_amount_in}",
        ]
    )

    if receipt_kind != "exact_in":
        return _reject(
            state=controller_state,
            reason=f"unsupported_receipt_kind:{receipt_kind or 'missing'}",
            explain=tuple(explain),
        )
    if receipt_asset_in != asset_in or receipt_asset_out != asset_out:
        return _reject(
            state=controller_state,
            reason=(
                "receipt_asset_mismatch:"
                f"want={asset_in}/{asset_out},got={receipt_asset_in}/{receipt_asset_out}"
            ),
            explain=tuple(explain),
        )
    if receipt_amount_in != fixed_order_size:
        return _reject(
            state=controller_state,
            reason=f"receipt_amount_mismatch:want={fixed_order_size},got={receipt_amount_in}",
            explain=tuple(explain),
        )
    if quote_epoch_raw is None:
        return _reject(
            state=controller_state,
            reason="receipt_missing_quote_epoch",
            explain=tuple(explain),
        )
    if not isinstance(quote_epoch_raw, int) or isinstance(quote_epoch_raw, bool):
        return _reject(
            state=controller_state,
            reason="receipt_invalid_quote_epoch",
            explain=tuple(explain),
        )
    try:
        quote_epoch = _require_u32_int("quote_epoch", quote_epoch_raw)
    except (TypeError, ValueError):
        return _reject(
            state=controller_state,
            reason="receipt_invalid_quote_epoch",
            explain=tuple(explain),
        )
    try:
        signal_packet = build_quote_receipt_signal_packet(
            receipt=receipt_snapshot,
            pools_by_id=pools_by_id,
            current_epoch=current_epoch,
        )
    except _SIGNAL_PACKET_BUILD_ERRORS as exc:
        return _reject(
            state=controller_state,
            reason=f"signal_packet_build_failed:{type(exc).__name__}:{exc}",
            explain=tuple(explain),
        )
    if signal_packet.quote_epoch != quote_epoch:
        return _reject(
            state=controller_state,
            reason=f"signal_quote_epoch_mismatch:{signal_packet.quote_epoch}!={quote_epoch}",
            explain=tuple(explain),
        )
    explain.extend(
        [
            f"quote_epoch={signal_packet.quote_epoch}",
            f"signal_source_kind={signal_packet.source_kind.value}",
            f"signal_trust_tier={signal_packet.trust_tier.value}",
        ]
    )
    if signal_packet.verify_error is not None:
        explain.append(f"signal_verify_error={signal_packet.verify_error}")
    provenance_result = check_signal_provenance(
        packet=signal_packet,
        require_quote_receipts=strategy.risk_limits.require_quote_receipts,
    )
    if controller_state.lifetime_spent + receipt_amount_in > strategy.notional_caps.lifetime_max:
        return _reject(
            state=controller_state,
            reason=(
                "lifetime_cap_exceeded:"
                f"{controller_state.lifetime_spent + receipt_amount_in}>{strategy.notional_caps.lifetime_max}"
            ),
            explain=tuple(explain),
        )

    tau_bin: str | None = None
    resolved_tau_config = tau_config or AutoTraderTauConfig()
    if strategy.policy_backend is PolicyBackend.TAU:
        if not resolved_tau_config.enabled:
            return _reject(
                state=controller_state,
                reason="tau_policy_backend_requires_enabled_tau_config",
                explain=tuple(explain),
            )
        ok, tau_bin, err = _resolve_tau_bin(resolved_tau_config)
        if not ok or not tau_bin:
            return _reject(
                state=controller_state,
                reason=f"tau_tool_unavailable:{err}",
                explain=tuple(explain),
            )

    provenance_tau_receipt: TauPolicyReceipt | None = None
    if strategy.policy_backend is PolicyBackend.TAU and tau_bin is not None:
        provenance_tau_receipt = build_signal_provenance_guard_tau_policy_receipt(
            strategy=strategy,
            packet=signal_packet,
        )
        tau_error = _verify_tau_policy_receipt(
            tau_bin=tau_bin,
            config=resolved_tau_config,
            receipt=provenance_tau_receipt,
        )
        if tau_error is not None:
            return _reject(
                state=controller_state,
                reason=tau_error,
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=provenance_tau_receipt,
            )
    if not provenance_result.ok:
        return _reject(
            state=controller_state,
            reason=f"signal_provenance_rejected:{provenance_result.error}",
            explain=tuple(explain),
            guard_state=guard_state,
            tau_policy_receipt=provenance_tau_receipt,
        )
    guard_state = replace(guard_state, signal_provenance_ok=True)

    route_snapshot = build_route_economic_sanity_snapshot(
        quote_receipt=receipt_snapshot,
        pools_by_id=pools_by_id,
    )
    if route_snapshot is None:
        return _reject(
            state=controller_state,
            reason="route_economic_sanity_unavailable",
            explain=tuple(explain),
            guard_state=guard_state,
        )
    explain.extend(
        [
            f"route_leg_count={route_snapshot.leg_count}",
            f"route_hop_count={route_snapshot.hop_count}",
            f"route_max_input_vs_reserve_bps={route_snapshot.max_hop_input_vs_reserve_bps}",
            f"route_max_output_vs_reserve_bps={route_snapshot.max_hop_output_vs_reserve_bps}",
            f"route_max_price_impact_bps={route_snapshot.max_hop_price_impact_bps}",
        ]
    )
    route_tau_receipt: TauPolicyReceipt | None = None
    if strategy.policy_backend is PolicyBackend.TAU and tau_bin is not None:
        route_tau_receipt = build_route_economic_sanity_guard_tau_policy_receipt(
            strategy=strategy,
            snapshot=route_snapshot,
        )
        tau_error = _verify_tau_policy_receipt(
            tau_bin=tau_bin,
            config=resolved_tau_config,
            receipt=route_tau_receipt,
        )
        if tau_error is not None:
            return _reject(
                state=controller_state,
                reason=tau_error,
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=route_tau_receipt,
            )
    if not route_snapshot.route_economic_sanity_ok:
        route_error = route_snapshot.classification_error or "route_economic_sanity_unknown"
        explain = explain + [f"route_sanity_error={route_error}"]
        tag = _route_economic_sanity_failure_tag(route_error)
        if tag is AutoTraderDecisionTag.SKIP:
            return _skip(
                state=controller_state,
                reason=f"route_economic_sanity_rejected:{route_error}",
                explain=tuple(explain),
                guard_state=guard_state,
            )
        return _reject(
            state=controller_state,
            reason=f"route_economic_sanity_rejected:{route_error}",
            explain=tuple(explain),
            guard_state=guard_state,
            tau_policy_receipt=route_tau_receipt,
        )
    guard_state = replace(guard_state, route_economic_sanity_ok=True)

    try:
        built_intents = create_swap_intents_from_quote_receipt(
            receipt=receipt_snapshot,
            pools_by_id=dict(pools_by_id),
            sender_pubkey=strategy.owner_pubkey,
            deadline=intent_deadline,
            slippage_bps=effective_slippage_bps,
            nonce_start=nonce_start,
        )
    except _INTENT_CONSTRUCTION_ERRORS as exc:
        return _reject(
            state=controller_state,
            reason=f"intent_construction_failed:{type(exc).__name__}:{exc}",
            explain=tuple(explain),
        )

    intents = tuple(built_intents)
    if not intents:
        return _reject(
            state=controller_state,
            reason="intent_construction_failed:empty_intent_list",
            explain=tuple(explain),
        )

    total_intent_amount_in = 0
    for idx, intent in enumerate(intents):
        raw_amount = intent.get_field("amount_in")
        if not isinstance(raw_amount, int) or isinstance(raw_amount, bool):
            return _reject(
                state=controller_state,
                reason=f"intent_amount_missing_or_invalid:index={idx}",
                explain=tuple(explain),
            )
        total_intent_amount_in += int(raw_amount)
    if total_intent_amount_in != receipt_amount_in:
        return _reject(
            state=controller_state,
            reason=f"intent_amount_mismatch:sum={total_intent_amount_in},receipt={receipt_amount_in}",
            explain=tuple(explain),
        )

    intent_count = len(intents)
    if intent_count > strategy.controls.max_intents_per_order:
        return _skip(
            state=controller_state,
            reason=f"max_intents_per_order_exceeded:{intent_count}>{strategy.controls.max_intents_per_order}",
            explain=tuple(explain),
            guard_state=guard_state,
        )

    projected_live_orders = controller_state.live_orders + 1
    explain.append(f"intent_count={intent_count}")
    explain.append(f"projected_live_orders={projected_live_orders}")

    execution_result = check_order_execution(
        current_epoch=current_epoch,
        valid_from_epoch=strategy.strategy_window.valid_from_epoch,
        valid_until_epoch=strategy.strategy_window.valid_until_epoch,
        last_action_epoch=controller_state.last_action_epoch,
        cadence_epochs=cadence_epochs,
        min_order_spacing_epochs=strategy.strategy_window.min_order_spacing_epochs,
        projected_live_orders=projected_live_orders,
        max_live_orders=strategy.controls.max_live_orders,
    )
    execution_tau_receipt: TauPolicyReceipt | None = None
    if strategy.policy_backend is PolicyBackend.TAU and tau_bin is not None:
        execution_tau_receipt = build_execution_guard_tau_policy_receipt(
            strategy=strategy,
            current_epoch=current_epoch,
            last_action_epoch=controller_state.last_action_epoch,
            projected_live_orders=projected_live_orders,
        )
        tau_error = _verify_tau_policy_receipt(
            tau_bin=tau_bin,
            config=resolved_tau_config,
            receipt=execution_tau_receipt,
        )
        if tau_error is not None:
            return _reject(
                state=controller_state,
                reason=tau_error,
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=execution_tau_receipt,
            )
    if not execution_result.ok:
        tag = _execution_failure_tag(execution_result.error)
        if tag is AutoTraderDecisionTag.SKIP:
            return _skip(
                state=controller_state,
                reason=str(execution_result.error),
                explain=tuple(explain),
                guard_state=guard_state,
            )
        return _reject(
            state=controller_state,
            reason=str(execution_result.error),
            explain=tuple(explain),
            guard_state=guard_state,
            tau_policy_receipt=execution_tau_receipt,
        )
    guard_state = replace(guard_state, execution_ok=True)

    oracle_result = check_oracle_freshness(
        current_epoch=current_epoch,
        quote_epoch=signal_packet.quote_epoch,
        max_oracle_staleness_epochs=strategy.risk_limits.max_oracle_staleness_epochs,
    )
    if oracle_result.age_epochs is not None:
        explain.append(f"quote_age_epochs={oracle_result.age_epochs}")
    oracle_tau_receipt: TauPolicyReceipt | None = None
    if strategy.policy_backend is PolicyBackend.TAU and tau_bin is not None:
        oracle_tau_receipt = build_oracle_freshness_guard_tau_policy_receipt(
            strategy=strategy,
            current_epoch=current_epoch,
            quote_epoch=signal_packet.quote_epoch,
        )
        tau_error = _verify_tau_policy_receipt(
            tau_bin=tau_bin,
            config=resolved_tau_config,
            receipt=oracle_tau_receipt,
        )
        if tau_error is not None:
            return _reject(
                state=controller_state,
                reason=tau_error,
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=oracle_tau_receipt,
            )
    if not oracle_result.ok:
        tag = _oracle_failure_tag(oracle_result.error)
        if tag is AutoTraderDecisionTag.SKIP:
            return _skip(
                state=controller_state,
                reason=str(oracle_result.error),
                explain=tuple(explain),
                guard_state=guard_state,
            )
        return _reject(
            state=controller_state,
            reason=str(oracle_result.error),
            explain=tuple(explain),
            guard_state=guard_state,
            tau_policy_receipt=oracle_tau_receipt,
        )
    guard_state = replace(guard_state, oracle_freshness_ok=True)

    target_budget_window_id = strategy_budget_window_id(strategy.strategy_window, current_epoch)
    explain.append(f"budget_window_id={target_budget_window_id}")
    working_budget_state = controller_state.budget_state
    if target_budget_window_id > working_budget_state.window_id:
        rolled = roll_window(state=working_budget_state, new_window_id=target_budget_window_id)
        if not rolled.ok:
            return _reject(
                state=controller_state,
                reason=f"budget_window_roll_failed:{rolled.error}",
                explain=tuple(explain),
            )
        working_budget_state = rolled.state
    elif target_budget_window_id < working_budget_state.window_id:
        return _reject(
            state=controller_state,
            reason=f"budget_window_regression:{target_budget_window_id}<{working_budget_state.window_id}",
            explain=tuple(explain),
        )

    budget_result = consume_order(
        state=working_budget_state,
        order_amount=receipt_amount_in,
        per_order_limit=strategy.notional_caps.per_order_max,
        window_budget=strategy.notional_caps.per_window_max,
    )
    tau_receipt: TauPolicyReceipt | None = None
    if strategy.policy_backend is PolicyBackend.TAU and tau_bin is not None:
        tau_receipt = build_budget_guard_tau_policy_receipt(
            strategy=strategy,
            state=working_budget_state,
            order_amount=receipt_amount_in,
        )
        tau_error = _verify_tau_policy_receipt(
            tau_bin=tau_bin,
            config=resolved_tau_config,
            receipt=tau_receipt,
        )
        if tau_error is not None:
            return _reject(
                state=controller_state,
                reason=tau_error,
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=tau_receipt,
            )

    if not budget_result.ok:
        tag = _budget_failure_tag(budget_result)
        if tag is AutoTraderDecisionTag.SKIP:
            return _skip(
                state=controller_state,
                reason=f"budget_guard_rejected:{budget_result.error}",
                explain=tuple(explain),
                guard_state=guard_state,
            )
        return _reject(
            state=controller_state,
            reason=f"budget_guard_rejected:{budget_result.error}",
            explain=tuple(explain),
            guard_state=guard_state,
            tau_policy_receipt=tau_receipt,
        )
    guard_state = replace(guard_state, budget_ok=True)

    next_state = AutoTraderControllerState(
        budget_state=budget_result.state,
        last_action_epoch=current_epoch,
        lifetime_spent=controller_state.lifetime_spent + receipt_amount_in,
        live_orders=projected_live_orders,
    )
    explain.extend(
        [
            f"budget_spent_after={budget_result.state.spent_in_window}",
            f"lifetime_spent_after={next_state.lifetime_spent}",
            f"live_orders_after={next_state.live_orders}",
        ]
    )
    return _submit(
        state=next_state,
        reason="policy_guard_passed",
        explain=tuple(explain),
        guard_state=guard_state,
        intents=intents,
        tau_policy_receipt=tau_receipt,
    )
