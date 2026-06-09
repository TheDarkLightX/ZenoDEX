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
from typing import Callable, Mapping

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
from ..kernels.python.strategy_signal_provenance_guard_v1_adapter import (
    StrategySignalProvenanceResult,
    check_signal_provenance,
)
from ..state.intents import Intent
from ..state.pools import PoolState
from .autotrader_signals import QuoteReceiptSignalPacket, build_quote_receipt_signal_packet
from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    AUTOTRADER_BUDGET_GUARD_V1,
    AUTOTRADER_EXECUTION_GUARD_V1,
    AUTOTRADER_NONCE_GUARD_V1,
    AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1,
    AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1,
    AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1,
    AUTOTRADER_WALLET_CAPABILITY_GUARD_V1,
)


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
    if not isinstance(body, dict):
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
    except Exception as exc:
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


@dataclass(frozen=True)
class _DcaOrderParams:
    """DCA template parameters resolved once and threaded through the stages."""

    fixed_order_size: int
    cadence_epochs: int
    asset_in: str
    asset_out: str


@dataclass(frozen=True)
class _ParsedReceiptBody:
    """Receipt body fields read once and threaded through the stages."""

    receipt_kind: str
    receipt_asset_in: str
    receipt_asset_out: str
    receipt_amount_in: int
    quote_epoch: int


def _validate_evaluator_inputs(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    intent_deadline: int,
) -> tuple[int, int]:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(controller_state, AutoTraderControllerState):
        raise TypeError("controller_state must be an AutoTraderControllerState")
    if not isinstance(receipt, Mapping):
        raise TypeError("receipt must be a mapping")
    if not isinstance(pools_by_id, Mapping):
        raise TypeError("pools_by_id must be a mapping")
    current_epoch = _require_u32_int("current_epoch", current_epoch)
    intent_deadline = _require_u32_int("intent_deadline", intent_deadline, minimum=1)
    return current_epoch, intent_deadline


def _unsupported_strategy_decision(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> AutoTraderDecision | None:
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
    return None


def _resolve_dca_order_params(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> tuple[AutoTraderDecision | None, _DcaOrderParams | None]:
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
        return (
            _reject(
                state=controller_state,
                reason="strategy_assets_outside_universe",
                explain=tuple(explain),
            ),
            None,
        )
    return None, _DcaOrderParams(
        fixed_order_size=fixed_order_size,
        cadence_epochs=cadence_epochs,
        asset_in=asset_in,
        asset_out=asset_out,
    )


def _resolve_effective_slippage(
    *,
    strategy: StrategyIR,
    slippage_bps: int | None,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> tuple[AutoTraderDecision | None, int | None]:
    effective_slippage_bps = strategy.risk_limits.max_slippage_bps if slippage_bps is None else slippage_bps
    effective_slippage_bps = _require_u32_int("slippage_bps", effective_slippage_bps)
    if effective_slippage_bps > strategy.risk_limits.max_slippage_bps:
        return (
            _reject(
                state=controller_state,
                reason=(
                    "slippage_limit_exceeded:"
                    f"{effective_slippage_bps}>{strategy.risk_limits.max_slippage_bps}"
                ),
                explain=tuple(explain),
            ),
            None,
        )
    explain.append(f"slippage_bps={effective_slippage_bps}")
    return None, effective_slippage_bps


def _parse_receipt_body_fields(
    *,
    receipt: Mapping[str, object],
    params: _DcaOrderParams,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> tuple[AutoTraderDecision | None, _ParsedReceiptBody | None]:
    body = _require_safe_receipt_body(receipt)
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
        return (
            _reject(
                state=controller_state,
                reason=f"unsupported_receipt_kind:{receipt_kind or 'missing'}",
                explain=tuple(explain),
            ),
            None,
        )
    if receipt_asset_in != params.asset_in or receipt_asset_out != params.asset_out:
        return (
            _reject(
                state=controller_state,
                reason=(
                    "receipt_asset_mismatch:"
                    f"want={params.asset_in}/{params.asset_out},got={receipt_asset_in}/{receipt_asset_out}"
                ),
                explain=tuple(explain),
            ),
            None,
        )
    if receipt_amount_in != params.fixed_order_size:
        return (
            _reject(
                state=controller_state,
                reason=f"receipt_amount_mismatch:want={params.fixed_order_size},got={receipt_amount_in}",
                explain=tuple(explain),
            ),
            None,
        )
    if quote_epoch_raw is None:
        return (
            _reject(
                state=controller_state,
                reason="receipt_missing_quote_epoch",
                explain=tuple(explain),
            ),
            None,
        )
    if not isinstance(quote_epoch_raw, int) or isinstance(quote_epoch_raw, bool):
        return (
            _reject(
                state=controller_state,
                reason="receipt_invalid_quote_epoch",
                explain=tuple(explain),
            ),
            None,
        )
    try:
        quote_epoch = _require_u32_int("quote_epoch", quote_epoch_raw)
    except (TypeError, ValueError):
        return (
            _reject(
                state=controller_state,
                reason="receipt_invalid_quote_epoch",
                explain=tuple(explain),
            ),
            None,
        )
    return None, _ParsedReceiptBody(
        receipt_kind=receipt_kind,
        receipt_asset_in=receipt_asset_in,
        receipt_asset_out=receipt_asset_out,
        receipt_amount_in=receipt_amount_in,
        quote_epoch=quote_epoch,
    )


def _build_signal_packet_decision(
    *,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    quote_epoch: int,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> tuple[AutoTraderDecision | None, QuoteReceiptSignalPacket | None]:
    try:
        signal_packet = build_quote_receipt_signal_packet(
            receipt=receipt,
            pools_by_id=pools_by_id,
            current_epoch=current_epoch,
        )
    except Exception as exc:
        return (
            _reject(
                state=controller_state,
                reason=f"signal_packet_build_failed:{type(exc).__name__}:{exc}",
                explain=tuple(explain),
            ),
            None,
        )
    if signal_packet.quote_epoch != quote_epoch:
        return (
            _reject(
                state=controller_state,
                reason=f"signal_quote_epoch_mismatch:{signal_packet.quote_epoch}!={quote_epoch}",
                explain=tuple(explain),
            ),
            None,
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
    return None, signal_packet


def _resolve_tau_backend_decision(
    *,
    strategy: StrategyIR,
    tau_config: AutoTraderTauConfig | None,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> tuple[AutoTraderDecision | None, str | None, AutoTraderTauConfig]:
    tau_bin: str | None = None
    resolved_tau_config = tau_config or AutoTraderTauConfig()
    if strategy.policy_backend is PolicyBackend.TAU:
        if not resolved_tau_config.enabled:
            return (
                _reject(
                    state=controller_state,
                    reason="tau_policy_backend_requires_enabled_tau_config",
                    explain=tuple(explain),
                ),
                None,
                resolved_tau_config,
            )
        ok, tau_bin, err = _resolve_tau_bin(resolved_tau_config)
        if not ok or not tau_bin:
            return (
                _reject(
                    state=controller_state,
                    reason=f"tau_tool_unavailable:{err}",
                    explain=tuple(explain),
                ),
                None,
                resolved_tau_config,
            )
    return None, tau_bin, resolved_tau_config


def _tau_policy_stage_decision(
    *,
    strategy: StrategyIR,
    tau_bin: str | None,
    resolved_tau_config: AutoTraderTauConfig,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
    build_receipt: Callable[[], TauPolicyReceipt],
) -> tuple[AutoTraderDecision | None, TauPolicyReceipt | None]:
    """Build and verify one stage's Tau policy receipt (TAU backend only).

    ``build_receipt`` is invoked lazily so the stage receipt builders keep
    their original only-under-TAU call pattern and late module-global binding.
    """
    if strategy.policy_backend is not PolicyBackend.TAU or tau_bin is None:
        return None, None
    stage_receipt = build_receipt()
    tau_error = _verify_tau_policy_receipt(
        tau_bin=tau_bin,
        config=resolved_tau_config,
        receipt=stage_receipt,
    )
    if tau_error is not None:
        return (
            _reject(
                state=controller_state,
                reason=tau_error,
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=stage_receipt,
            ),
            stage_receipt,
        )
    return None, stage_receipt


def _signal_provenance_stage_decision(
    *,
    strategy: StrategyIR,
    signal_packet: QuoteReceiptSignalPacket,
    provenance_result: StrategySignalProvenanceResult,
    tau_bin: str | None,
    resolved_tau_config: AutoTraderTauConfig,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
) -> tuple[AutoTraderDecision | None, TauPolicyReceipt | None]:
    decision, provenance_tau_receipt = _tau_policy_stage_decision(
        strategy=strategy,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
        build_receipt=lambda: build_signal_provenance_guard_tau_policy_receipt(
            strategy=strategy,
            packet=signal_packet,
        ),
    )
    if decision is not None:
        return decision, provenance_tau_receipt
    if not provenance_result.ok:
        return (
            _reject(
                state=controller_state,
                reason=f"signal_provenance_rejected:{provenance_result.error}",
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=provenance_tau_receipt,
            ),
            provenance_tau_receipt,
        )
    return None, provenance_tau_receipt


def _route_economic_sanity_stage_decision(
    *,
    strategy: StrategyIR,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    tau_bin: str | None,
    resolved_tau_config: AutoTraderTauConfig,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
) -> AutoTraderDecision | None:
    route_snapshot = build_route_economic_sanity_snapshot(
        quote_receipt=receipt,
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
    decision, route_tau_receipt = _tau_policy_stage_decision(
        strategy=strategy,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
        build_receipt=lambda: build_route_economic_sanity_guard_tau_policy_receipt(
            strategy=strategy,
            snapshot=route_snapshot,
        ),
    )
    if decision is not None:
        return decision
    if not route_snapshot.route_economic_sanity_ok:
        route_error = route_snapshot.classification_error or "route_economic_sanity_unknown"
        failure_explain = explain + [f"route_sanity_error={route_error}"]
        tag = _route_economic_sanity_failure_tag(route_error)
        if tag is AutoTraderDecisionTag.SKIP:
            return _skip(
                state=controller_state,
                reason=f"route_economic_sanity_rejected:{route_error}",
                explain=tuple(failure_explain),
                guard_state=guard_state,
            )
        return _reject(
            state=controller_state,
            reason=f"route_economic_sanity_rejected:{route_error}",
            explain=tuple(failure_explain),
            guard_state=guard_state,
            tau_policy_receipt=route_tau_receipt,
        )
    return None


def _build_intents_stage(
    *,
    strategy: StrategyIR,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    intent_deadline: int,
    effective_slippage_bps: int,
    nonce_start: int | None,
    receipt_amount_in: int,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
) -> tuple[AutoTraderDecision | None, tuple[Intent, ...] | None]:
    try:
        built_intents = create_swap_intents_from_quote_receipt(
            receipt=dict(receipt),
            pools_by_id=dict(pools_by_id),
            sender_pubkey=strategy.owner_pubkey,
            deadline=intent_deadline,
            slippage_bps=effective_slippage_bps,
            nonce_start=nonce_start,
        )
    except Exception as exc:
        return (
            _reject(
                state=controller_state,
                reason=f"intent_construction_failed:{type(exc).__name__}:{exc}",
                explain=tuple(explain),
            ),
            None,
        )

    intents = tuple(built_intents)
    if not intents:
        return (
            _reject(
                state=controller_state,
                reason="intent_construction_failed:empty_intent_list",
                explain=tuple(explain),
            ),
            None,
        )

    total_intent_amount_in = 0
    for idx, intent in enumerate(intents):
        raw_amount = intent.get_field("amount_in")
        if not isinstance(raw_amount, int) or isinstance(raw_amount, bool):
            return (
                _reject(
                    state=controller_state,
                    reason=f"intent_amount_missing_or_invalid:index={idx}",
                    explain=tuple(explain),
                ),
                None,
            )
        total_intent_amount_in += int(raw_amount)
    if total_intent_amount_in != receipt_amount_in:
        return (
            _reject(
                state=controller_state,
                reason=f"intent_amount_mismatch:sum={total_intent_amount_in},receipt={receipt_amount_in}",
                explain=tuple(explain),
            ),
            None,
        )

    intent_count = len(intents)
    if intent_count > strategy.controls.max_intents_per_order:
        return (
            _skip(
                state=controller_state,
                reason=f"max_intents_per_order_exceeded:{intent_count}>{strategy.controls.max_intents_per_order}",
                explain=tuple(explain),
                guard_state=guard_state,
            ),
            None,
        )
    return None, intents


def _execution_stage_decision(
    *,
    strategy: StrategyIR,
    current_epoch: int,
    cadence_epochs: int,
    projected_live_orders: int,
    tau_bin: str | None,
    resolved_tau_config: AutoTraderTauConfig,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
) -> AutoTraderDecision | None:
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
    decision, execution_tau_receipt = _tau_policy_stage_decision(
        strategy=strategy,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
        build_receipt=lambda: build_execution_guard_tau_policy_receipt(
            strategy=strategy,
            current_epoch=current_epoch,
            last_action_epoch=controller_state.last_action_epoch,
            projected_live_orders=projected_live_orders,
        ),
    )
    if decision is not None:
        return decision
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
    return None


def _oracle_stage_decision(
    *,
    strategy: StrategyIR,
    current_epoch: int,
    signal_packet: QuoteReceiptSignalPacket,
    tau_bin: str | None,
    resolved_tau_config: AutoTraderTauConfig,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
) -> AutoTraderDecision | None:
    oracle_result = check_oracle_freshness(
        current_epoch=current_epoch,
        quote_epoch=signal_packet.quote_epoch,
        max_oracle_staleness_epochs=strategy.risk_limits.max_oracle_staleness_epochs,
    )
    if oracle_result.age_epochs is not None:
        explain.append(f"quote_age_epochs={oracle_result.age_epochs}")
    decision, oracle_tau_receipt = _tau_policy_stage_decision(
        strategy=strategy,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
        build_receipt=lambda: build_oracle_freshness_guard_tau_policy_receipt(
            strategy=strategy,
            current_epoch=current_epoch,
            quote_epoch=signal_packet.quote_epoch,
        ),
    )
    if decision is not None:
        return decision
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
    return None


def _budget_window_stage_decision(
    *,
    strategy: StrategyIR,
    current_epoch: int,
    controller_state: AutoTraderControllerState,
    explain: list[str],
) -> tuple[AutoTraderDecision | None, StrategyBudgetState | None]:
    target_budget_window_id = strategy_budget_window_id(strategy.strategy_window, current_epoch)
    explain.append(f"budget_window_id={target_budget_window_id}")
    working_budget_state = controller_state.budget_state
    if target_budget_window_id > working_budget_state.window_id:
        rolled = roll_window(state=working_budget_state, new_window_id=target_budget_window_id)
        if not rolled.ok:
            return (
                _reject(
                    state=controller_state,
                    reason=f"budget_window_roll_failed:{rolled.error}",
                    explain=tuple(explain),
                ),
                None,
            )
        working_budget_state = rolled.state
    elif target_budget_window_id < working_budget_state.window_id:
        return (
            _reject(
                state=controller_state,
                reason=f"budget_window_regression:{target_budget_window_id}<{working_budget_state.window_id}",
                explain=tuple(explain),
            ),
            None,
        )
    return None, working_budget_state


def _budget_consume_stage_decision(
    *,
    strategy: StrategyIR,
    working_budget_state: StrategyBudgetState,
    receipt_amount_in: int,
    tau_bin: str | None,
    resolved_tau_config: AutoTraderTauConfig,
    controller_state: AutoTraderControllerState,
    explain: list[str],
    guard_state: AutoTraderGuardState,
) -> tuple[AutoTraderDecision | None, StrategyBudgetResult | None, TauPolicyReceipt | None]:
    budget_result = consume_order(
        state=working_budget_state,
        order_amount=receipt_amount_in,
        per_order_limit=strategy.notional_caps.per_order_max,
        window_budget=strategy.notional_caps.per_window_max,
    )
    decision, tau_receipt = _tau_policy_stage_decision(
        strategy=strategy,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
        build_receipt=lambda: build_budget_guard_tau_policy_receipt(
            strategy=strategy,
            state=working_budget_state,
            order_amount=receipt_amount_in,
        ),
    )
    if decision is not None:
        return decision, None, None
    if not budget_result.ok:
        tag = _budget_failure_tag(budget_result)
        if tag is AutoTraderDecisionTag.SKIP:
            return (
                _skip(
                    state=controller_state,
                    reason=f"budget_guard_rejected:{budget_result.error}",
                    explain=tuple(explain),
                    guard_state=guard_state,
                ),
                None,
                None,
            )
        return (
            _reject(
                state=controller_state,
                reason=f"budget_guard_rejected:{budget_result.error}",
                explain=tuple(explain),
                guard_state=guard_state,
                tau_policy_receipt=tau_receipt,
            ),
            None,
            None,
        )
    return None, budget_result, tau_receipt


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

    First-failure-wins: every stage either passes or returns the terminal
    decision for its first failing guard, in the fixed stage order below.
    """

    current_epoch, intent_deadline = _validate_evaluator_inputs(
        strategy=strategy,
        controller_state=controller_state,
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=current_epoch,
        intent_deadline=intent_deadline,
    )

    explain: list[str] = [
        f"strategy_id={strategy.strategy_id}",
        f"backend={strategy.policy_backend.value}",
        f"template={strategy.template.value}",
        f"epoch={current_epoch}",
    ]
    guard_state = AutoTraderGuardState()

    decision = _unsupported_strategy_decision(
        strategy=strategy,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    decision, params = _resolve_dca_order_params(
        strategy=strategy,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    decision, effective_slippage_bps = _resolve_effective_slippage(
        strategy=strategy,
        slippage_bps=slippage_bps,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    decision, parsed = _parse_receipt_body_fields(
        receipt=receipt,
        params=params,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    decision, signal_packet = _build_signal_packet_decision(
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=current_epoch,
        quote_epoch=parsed.quote_epoch,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    provenance_result = check_signal_provenance(
        packet=signal_packet,
        require_quote_receipts=strategy.risk_limits.require_quote_receipts,
    )
    if controller_state.lifetime_spent + parsed.receipt_amount_in > strategy.notional_caps.lifetime_max:
        return _reject(
            state=controller_state,
            reason=(
                "lifetime_cap_exceeded:"
                f"{controller_state.lifetime_spent + parsed.receipt_amount_in}>{strategy.notional_caps.lifetime_max}"
            ),
            explain=tuple(explain),
        )

    decision, tau_bin, resolved_tau_config = _resolve_tau_backend_decision(
        strategy=strategy,
        tau_config=tau_config,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    decision, _provenance_tau_receipt = _signal_provenance_stage_decision(
        strategy=strategy,
        signal_packet=signal_packet,
        provenance_result=provenance_result,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
    )
    if decision is not None:
        return decision
    guard_state = replace(guard_state, signal_provenance_ok=True)

    decision = _route_economic_sanity_stage_decision(
        strategy=strategy,
        receipt=receipt,
        pools_by_id=pools_by_id,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
    )
    if decision is not None:
        return decision
    guard_state = replace(guard_state, route_economic_sanity_ok=True)

    decision, intents = _build_intents_stage(
        strategy=strategy,
        receipt=receipt,
        pools_by_id=pools_by_id,
        intent_deadline=intent_deadline,
        effective_slippage_bps=effective_slippage_bps,
        nonce_start=nonce_start,
        receipt_amount_in=parsed.receipt_amount_in,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
    )
    if decision is not None:
        return decision

    projected_live_orders = controller_state.live_orders + 1
    explain.append(f"intent_count={len(intents)}")
    explain.append(f"projected_live_orders={projected_live_orders}")

    decision = _execution_stage_decision(
        strategy=strategy,
        current_epoch=current_epoch,
        cadence_epochs=params.cadence_epochs,
        projected_live_orders=projected_live_orders,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
    )
    if decision is not None:
        return decision
    guard_state = replace(guard_state, execution_ok=True)

    decision = _oracle_stage_decision(
        strategy=strategy,
        current_epoch=current_epoch,
        signal_packet=signal_packet,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
    )
    if decision is not None:
        return decision
    guard_state = replace(guard_state, oracle_freshness_ok=True)

    decision, working_budget_state = _budget_window_stage_decision(
        strategy=strategy,
        current_epoch=current_epoch,
        controller_state=controller_state,
        explain=explain,
    )
    if decision is not None:
        return decision

    decision, budget_result, tau_receipt = _budget_consume_stage_decision(
        strategy=strategy,
        working_budget_state=working_budget_state,
        receipt_amount_in=parsed.receipt_amount_in,
        tau_bin=tau_bin,
        resolved_tau_config=resolved_tau_config,
        controller_state=controller_state,
        explain=explain,
        guard_state=guard_state,
    )
    if decision is not None:
        return decision
    guard_state = replace(guard_state, budget_ok=True)

    next_state = AutoTraderControllerState(
        budget_state=budget_result.state,
        last_action_epoch=current_epoch,
        lifetime_spent=controller_state.lifetime_spent + parsed.receipt_amount_in,
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
