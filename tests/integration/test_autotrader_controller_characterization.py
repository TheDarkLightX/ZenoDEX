"""Characterization corpus for ``evaluate_autotrader_quote_receipt``.

This locks the EXACT observable behavior (full decision payloads and raised
exceptions) of the fail-closed auto-trader quote evaluator in
``src/integration/autotrader_controller.py`` before/after refactoring.

Semantics under test: FIRST-FAILURE-WINS. The evaluator returns on the first
failing guard; nothing is accumulated. Multi-fault probes therefore pin the
reject/skip PRECEDENCE order, not an error list.

Corpus:
- ``tests/integration/fixtures/autotrader_controller_characterization_corpus.json``
- Regenerate (byte-reproducible) with:
    python3 tests/integration/test_autotrader_controller_characterization.py --regen
- Verify without writing:
    python3 tests/integration/test_autotrader_controller_characterization.py --check

Codes that are UNREACHABLE through ``evaluate_autotrader_quote_receipt`` and
therefore intentionally not in this corpus (locked elsewhere by direct unit
tests in tests/integration/test_autotrader_controller.py):
- ``tau_policy_unknown_spec:`` (receipts are built internally with known spec ids)
- ``_execution_failure_tag(None)`` / ``_oracle_failure_tag(None)`` /
  ``_route_economic_sanity_failure_tag(None)`` REJECT fallbacks (the kernel
  adapters always set ``error`` when ``ok`` is False)
- ``route_economic_sanity_unknown`` is likewise unreachable with the real
  snapshot builder; this corpus reaches the evaluator's own fallback line via
  a patched snapshot (case ``route_unknown_error``).
"""

from __future__ import annotations

import collections.abc
import json
import sys
from contextlib import contextmanager
from dataclasses import replace as dc_replace
from pathlib import Path
from typing import Any, Callable, Iterator, Mapping

import pytest

import src.integration.autotrader_controller as autotrader_controller
from src.agents.intent_signer import create_swap_intent
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, StrategyAction, StrategyIR
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_controller import (
    AutoTraderControllerState,
    AutoTraderDecision,
    AutoTraderTauConfig,
    evaluate_autotrader_quote_receipt,
)
from src.integration.autotrader_signals import (
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)
from src.integration.tau_witness import (
    AUTOTRADER_BUDGET_GUARD_V1,
    AUTOTRADER_EXECUTION_GUARD_V1,
    AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1,
    AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1,
    AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1,
)
from src.kernels.python.strategy_budget_guard_v1_adapter import (
    StrategyBudgetResult,
    StrategyBudgetState,
)
from src.state.pools import PoolState, PoolStatus

CORPUS_PATH = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "autotrader_controller_characterization_corpus.json"
)
CORPUS_SCHEMA = "zenodex/autotrader-controller-characterization-corpus/v1"
BASE_COMMIT = "ad96b74d"

OWNER_PUBKEY = "owner.pubkey.1"


# ---------------------------------------------------------------------------
# Fixture recipes (mirrors tests/integration/test_autotrader_controller.py)
# ---------------------------------------------------------------------------


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _compiled_strategy(
    *,
    backend: str = "local",
    max_live_orders: int = 3,
    max_intents_per_order: int = 16,
    per_order_max: int = 100,
    per_window_max: int = 500,
    lifetime_max: int = 1_000,
    fixed_order_size: int = 100,
    cadence_epochs: int = 4,
    budget_window_epochs: int = 0,
    min_order_spacing_epochs: int = 0,
) -> StrategyIR:
    return compile_policy_candidate(
        {
            "strategy_id": f"dca.{backend}.1",
            "owner_pubkey": OWNER_PUBKEY,
            "policy_backend": backend,
            "template": "dca",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": per_order_max,
                "per_window_max": per_window_max,
                "lifetime_max": lifetime_max,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": min_order_spacing_epochs,
                "budget_window_epochs": budget_window_epochs,
            },
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": max_live_orders,
                "max_intents_per_order": max_intents_per_order,
            },
            "template_params": {
                "fixed_order_size": fixed_order_size,
                "cadence_epochs": cadence_epochs,
                "asset_in": "A",
                "asset_out": "B",
            },
            "tau_policy_specs": list(AUTOTRADER_TAU_POLICY_SPECS) if backend == "tau" else [],
        }
    ).strategy


def _limit_ladder_strategy() -> StrategyIR:
    return compile_policy_candidate(
        {
            "strategy_id": "limit.local.1",
            "owner_pubkey": OWNER_PUBKEY,
            "policy_backend": "local",
            "template": "limit_ladder",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": 100,
                "per_window_max": 500,
                "lifetime_max": 1_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
            },
            "template_params": {
                "ladder_levels": 2,
                "per_level_size": 50,
                "asset_in": "A",
                "asset_out": "B",
            },
        }
    ).strategy


def _receipt_pools(recipe: str, *, amount_in: int, quote_epoch: int) -> tuple[dict[str, PoolState], dict[str, object]]:
    if recipe == "single_hop":
        pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
        asset_in, asset_out, kind = "A", "B", "exact_in"
    elif recipe == "split":
        pools = {
            "p1": _pool("p1", "A", "B", 1_000, 1_000, 0),
            "p2": _pool("p2", "A", "B", 1_000, 1_000, 0),
        }
        asset_in, asset_out, kind = "A", "B", "exact_in"
    elif recipe == "multi_hop":
        pools = {
            "p_ac": _pool("p_ac", "A", "C", 1_000, 1_000, 0),
            "p_cb": _pool("p_cb", "C", "B", 1_000, 1_000, 0),
        }
        asset_in, asset_out, kind = "A", "B", "exact_in"
    elif recipe == "extreme":
        pools = {"p_ab": _pool("p_ab", "A", "B", 50, 1_000, 0)}
        asset_in, asset_out, kind = "A", "B", "exact_in"
    elif recipe == "reversed_pair":
        pools = {"p_ba": _pool("p_ba", "B", "A", 1_000, 2_000, 10)}
        asset_in, asset_out, kind = "B", "A", "exact_in"
    elif recipe == "exact_out":
        pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
        asset_in, asset_out, kind = "A", "B", "exact_out"
    elif recipe == "exact_out_reversed":
        pools = {"p_ba": _pool("p_ba", "B", "A", 1_000, 2_000, 10)}
        asset_in, asset_out, kind = "B", "A", "exact_out"
    elif recipe == "no_body":
        return {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}, {"receipt_hash": "x"}
    else:
        raise RuntimeError(f"unknown receipt recipe: {recipe}")
    quote = best_route_exact_in_2hop(
        pools_by_id=pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
    )
    if quote is None:
        raise RuntimeError(f"receipt recipe produced no quote: {recipe}")
    receipt = make_route_quote_receipt(
        kind=kind,
        quote=quote,
        pools_by_id=pools,
        quote_epoch=quote_epoch,
    )
    return pools, receipt


def _tau_ok_output(spec_name: str) -> dict[int, dict[str, int]]:
    if spec_name == "autotrader_signal_provenance_guard_v1.tau":
        return {0: {AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.gate_output: 1}}
    if spec_name == "autotrader_route_economic_sanity_guard_v1.tau":
        return {0: {AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1.gate_output: 1}}
    if spec_name == "autotrader_execution_guard_v1.tau":
        return {0: {AUTOTRADER_EXECUTION_GUARD_V1.gate_output: 1}}
    if spec_name == "autotrader_oracle_freshness_guard_v1.tau":
        return {0: {AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1.gate_output: 1}}
    return {0: {AUTOTRADER_BUDGET_GUARD_V1.gate_output: 1}}


def _tau_gate0_output(spec_name: str) -> dict[int, dict[str, int]]:
    out = _tau_ok_output(spec_name)
    gate_key = next(iter(out[0]))
    return {0: {gate_key: 0}}


def _tau_fail_only(fail_spec_name: str) -> Callable[..., dict[int, dict[str, int]]]:
    def _runner(**kwargs: Any) -> dict[int, dict[str, int]]:
        spec_name = kwargs["spec_path"].name
        if spec_name == fail_spec_name:
            return _tau_gate0_output(spec_name)
        return _tau_ok_output(spec_name)

    return _runner


def _bad_amount_intent() -> Any:
    intent = create_swap_intent(
        pool_id="p_ab",
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=150,
        deadline=99,
        sender_pubkey=OWNER_PUBKEY,
    )
    intent.set_field("amount_in", "bad")
    return intent


def _amount_99_intent() -> Any:
    return create_swap_intent(
        pool_id="p_ab",
        asset_in="A",
        asset_out="B",
        amount_in=99,
        min_amount_out=150,
        deadline=99,
        sender_pubkey=OWNER_PUBKEY,
    )


def _mismatched_signal_packet(**_: object) -> QuoteReceiptSignalPacket:
    return QuoteReceiptSignalPacket(
        current_epoch=5,
        quote_epoch=4,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        amount_out=180,
        receipt_hash="receipt.hash.1",
        source_kind=SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        trust_tier=SignalTrustTier.VERIFIED,
        quote_receipt_present=True,
        quote_receipt_verified=True,
        quote_epoch_present=True,
        source_available=True,
        auth_ok=True,
        binding_ok=True,
    )


def _patched_snapshot_builder(
    *,
    classification_error: str | None,
) -> Callable[..., Any]:
    real_builder = autotrader_controller.build_route_economic_sanity_snapshot

    def _builder(**kwargs: Any) -> Any:
        snapshot = real_builder(**kwargs)
        if snapshot is None:
            raise RuntimeError("patched snapshot builder expected a real snapshot")
        return dc_replace(
            snapshot,
            route_economic_sanity_ok=False,
            classification_error=classification_error,
        )

    return _builder


def _bad_roll_window(*, state: StrategyBudgetState, new_window_id: int) -> StrategyBudgetResult:
    return StrategyBudgetResult(
        ok=False,
        state=state,
        budget_ok=False,
        kill_switch_active=False,
        order_applied=False,
        error="window_roll_broken",
    )


def _raise_value_error(**_: object) -> Any:
    raise ValueError("broken packet")


def _raise_runtime_error_intents(**_: object) -> Any:
    raise RuntimeError("quote builder exploded")


def _raise_tau_crash(*args: Any, **kwargs: Any) -> Any:
    raise RuntimeError("tau crashed")


PATCHES: dict[str, Callable[[], tuple[str, Any]]] = {
    "signal_packet_raises": lambda: ("build_quote_receipt_signal_packet", _raise_value_error),
    "signal_packet_epoch_mismatch": lambda: (
        "build_quote_receipt_signal_packet",
        _mismatched_signal_packet,
    ),
    "route_snapshot_none": lambda: (
        "build_route_economic_sanity_snapshot",
        lambda **kwargs: None,
    ),
    "route_snapshot_output_depletion": lambda: (
        "build_route_economic_sanity_snapshot",
        _patched_snapshot_builder(
            classification_error="route_extreme_output_depletion:max=9100,threshold=9000"
        ),
    ),
    "route_snapshot_price_impact": lambda: (
        "build_route_economic_sanity_snapshot",
        _patched_snapshot_builder(
            classification_error="route_extreme_price_impact:max=5100,threshold=5000"
        ),
    ),
    "route_snapshot_error_none": lambda: (
        "build_route_economic_sanity_snapshot",
        _patched_snapshot_builder(classification_error=None),
    ),
    "intents_raise": lambda: (
        "create_swap_intents_from_quote_receipt",
        _raise_runtime_error_intents,
    ),
    "intents_empty": lambda: (
        "create_swap_intents_from_quote_receipt",
        lambda **kwargs: [],
    ),
    "intents_bad_amount_type": lambda: (
        "create_swap_intents_from_quote_receipt",
        lambda **kwargs: [_bad_amount_intent()],
    ),
    "intents_amount_99": lambda: (
        "create_swap_intents_from_quote_receipt",
        lambda **kwargs: [_amount_99_intent()],
    ),
    "roll_window_fails": lambda: ("roll_window", _bad_roll_window),
    "find_tau_bin_none": lambda: ("find_tau_bin", lambda: None),
    "tau_runner_ok": lambda: (
        "run_tau_spec_steps",
        lambda **kwargs: _tau_ok_output(kwargs["spec_path"].name),
    ),
    "tau_runner_raises": lambda: ("run_tau_spec_steps", _raise_tau_crash),
    "tau_runner_empty": lambda: ("run_tau_spec_steps", lambda **kwargs: {0: {}}),
    "tau_runner_gate0_provenance": lambda: (
        "run_tau_spec_steps",
        _tau_fail_only("autotrader_signal_provenance_guard_v1.tau"),
    ),
    "tau_runner_gate0_route": lambda: (
        "run_tau_spec_steps",
        _tau_fail_only("autotrader_route_economic_sanity_guard_v1.tau"),
    ),
    "tau_runner_gate0_execution": lambda: (
        "run_tau_spec_steps",
        _tau_fail_only("autotrader_execution_guard_v1.tau"),
    ),
    "tau_runner_gate0_oracle": lambda: (
        "run_tau_spec_steps",
        _tau_fail_only("autotrader_oracle_freshness_guard_v1.tau"),
    ),
    "tau_runner_gate0_budget": lambda: (
        "run_tau_spec_steps",
        _tau_fail_only("autotrader_budget_guard_v1.tau"),
    ),
}


@contextmanager
def _apply_patches(names: list[str]) -> Iterator[None]:
    saved: list[tuple[str, Any]] = []
    try:
        for name in names:
            attr, replacement = PATCHES[name]()
            saved.append((attr, getattr(autotrader_controller, attr)))
            setattr(autotrader_controller, attr, replacement)
        yield
    finally:
        for attr, original in reversed(saved):
            setattr(autotrader_controller, attr, original)


# ---------------------------------------------------------------------------
# Scenario interpreter
# ---------------------------------------------------------------------------


def _build_strategy(spec: Mapping[str, Any] | str) -> Any:
    if spec == "invalid":
        return "bad"
    if not isinstance(spec, Mapping):
        raise RuntimeError(f"bad strategy spec: {spec!r}")
    if spec.get("kind") == "limit_ladder":
        return _limit_ladder_strategy()
    kwargs_keys = (
        "backend",
        "max_live_orders",
        "max_intents_per_order",
        "per_order_max",
        "per_window_max",
        "lifetime_max",
        "fixed_order_size",
        "cadence_epochs",
        "budget_window_epochs",
        "min_order_spacing_epochs",
    )
    kwargs = {key: spec[key] for key in kwargs_keys if key in spec}
    strategy = _compiled_strategy(**kwargs)
    for op in spec.get("overrides", []):
        if op[0] == "allowed_actions":
            object.__setattr__(
                strategy,
                "allowed_actions",
                tuple(StrategyAction(value) for value in op[1]),
            )
        elif op[0] == "asset_universe":
            object.__setattr__(strategy, "asset_universe", tuple(op[1]))
        elif op[0] == "template_param":
            strategy.template_params[op[1]] = op[2]
        else:
            raise RuntimeError(f"unknown strategy override: {op!r}")
    return strategy


def _build_controller_state(spec: Mapping[str, Any] | str | None) -> Any:
    if spec == "invalid":
        return "bad"
    if spec is None:
        return AutoTraderControllerState()
    if not isinstance(spec, Mapping):
        raise RuntimeError(f"bad controller_state spec: {spec!r}")
    return AutoTraderControllerState(
        budget_state=StrategyBudgetState(
            window_id=spec.get("window_id", 0),
            spent_in_window=spec.get("spent_in_window", 0),
            kill_switch_on=spec.get("kill_switch_on", False),
        ),
        last_action_epoch=spec.get("last_action_epoch"),
        lifetime_spent=spec.get("lifetime_spent", 0),
        live_orders=spec.get("live_orders", 0),
    )


def _build_receipt_and_pools(spec: Mapping[str, Any]) -> tuple[Any, Any]:
    recipe = spec.get("recipe", "single_hop")
    pools, receipt = _receipt_pools(
        recipe,
        amount_in=spec.get("amount_in", 100),
        quote_epoch=spec.get("quote_epoch", 5),
    )
    body = receipt.get("body")
    for op in spec.get("mutations", []):
        if op[0] == "pop_body":
            if not isinstance(body, dict):
                raise RuntimeError("receipt body is not a dict")
            body.pop(op[1], None)
        elif op[0] == "set_body":
            if not isinstance(body, dict):
                raise RuntimeError("receipt body is not a dict")
            body[op[1]] = op[2]
        elif op[0] == "set_top":
            receipt[op[1]] = op[2]
        else:
            raise RuntimeError(f"unknown receipt mutation: {op!r}")
    if spec.get("receipt_invalid"):
        receipt = "bad"
    if spec.get("pools_invalid"):
        pools = "bad"
    return receipt, pools


def _build_tau_config(spec: Mapping[str, Any] | None) -> AutoTraderTauConfig | None:
    if spec is None:
        return None
    tau_bin = spec.get("tau_bin")
    if tau_bin == "@SYS_EXECUTABLE@":
        tau_bin = sys.executable
    return AutoTraderTauConfig(
        enabled=spec.get("enabled", False),
        timeout_s=spec.get("timeout_s", 2.0),
        tau_bin=tau_bin,
        allow_path_lookup=spec.get("allow_path_lookup", False),
    )


def _intent_to_dict(intent: Any) -> dict[str, Any]:
    return {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": int(intent.deadline),
        "salt": intent.salt,
        "fields": dict(intent.fields or {}),
    }


def _decision_to_dict(decision: AutoTraderDecision) -> dict[str, Any]:
    return {
        "tag": decision.tag.value,
        "reason": decision.reason,
        "explain": list(decision.explain),
        "should_submit": bool(decision.should_submit),
        "state": {
            "budget_state": {
                "window_id": int(decision.state.budget_state.window_id),
                "spent_in_window": int(decision.state.budget_state.spent_in_window),
                "kill_switch_on": bool(decision.state.budget_state.kill_switch_on),
            },
            "last_action_epoch": decision.state.last_action_epoch,
            "lifetime_spent": int(decision.state.lifetime_spent),
            "live_orders": int(decision.state.live_orders),
        },
        "guard_state": {
            "signal_provenance_ok": bool(decision.guard_state.signal_provenance_ok),
            "route_economic_sanity_ok": bool(decision.guard_state.route_economic_sanity_ok),
            "execution_ok": bool(decision.guard_state.execution_ok),
            "oracle_freshness_ok": bool(decision.guard_state.oracle_freshness_ok),
            "budget_ok": bool(decision.guard_state.budget_ok),
        },
        "intents": [_intent_to_dict(intent) for intent in decision.intents],
        "tau_policy_receipt": (
            None
            if decision.tau_policy_receipt is None
            else decision.tau_policy_receipt.to_dict()
        ),
    }


def run_case(spec: Mapping[str, Any]) -> dict[str, Any]:
    """Execute one corpus scenario against the live module and serialize the result."""
    strategy = _build_strategy(spec.get("strategy", {}))
    controller_state = _build_controller_state(spec.get("controller_state"))
    receipt, pools = _build_receipt_and_pools(spec.get("receipt", {}))
    call = spec.get("call", {})
    kwargs: dict[str, Any] = {
        "strategy": strategy,
        "controller_state": controller_state,
        "receipt": receipt,
        "pools_by_id": pools,
        "current_epoch": call.get("current_epoch", 5),
        "intent_deadline": call.get("intent_deadline", 99),
    }
    if "slippage_bps" in call:
        kwargs["slippage_bps"] = call["slippage_bps"]
    if "nonce_start" in call:
        kwargs["nonce_start"] = call["nonce_start"]
    tau_config = _build_tau_config(spec.get("tau_config"))
    if tau_config is not None:
        kwargs["tau_config"] = tau_config
    with _apply_patches(list(spec.get("patches", []))):
        try:
            decision = evaluate_autotrader_quote_receipt(**kwargs)
        except Exception as exc:  # noqa: BLE001 - characterization captures raises
            return {
                "outcome": "exception",
                "exception_type": type(exc).__name__,
                "exception_message": str(exc),
            }
    return {"outcome": "decision", "decision": _decision_to_dict(decision)}


# ---------------------------------------------------------------------------
# Case catalogue
# ---------------------------------------------------------------------------

# Every entry: (case_id, kind, spec). ``kind`` is one of
# valid | exception | single_fault | multi_fault.
CASES: list[tuple[str, str, dict[str, Any]]] = [
    # ---- valid / passing scenarios -------------------------------------
    ("valid_local_submit", "valid", {}),
    (
        "valid_local_submit_split_nonce",
        "valid",
        {
            "strategy": {
                "max_live_orders": 1,
                "per_order_max": 600,
                "per_window_max": 1_000,
                "lifetime_max": 2_000,
                "fixed_order_size": 600,
            },
            "receipt": {"recipe": "split", "amount_in": 600},
            "call": {"nonce_start": 10},
        },
    ),
    (
        "valid_tau_submit",
        "valid",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_ok"],
        },
    ),
    (
        "valid_local_submit_window_roll",
        "valid",
        {
            "strategy": {"budget_window_epochs": 4},
            "controller_state": {
                "window_id": 5,
                "spent_in_window": 100,
                "last_action_epoch": 5,
                "lifetime_spent": 100,
            },
            "receipt": {"quote_epoch": 9},
            "call": {"current_epoch": 9},
        },
    ),
    (
        "valid_local_submit_slippage_at_limit",
        "valid",
        {"call": {"slippage_bps": 50}},
    ),
    # ---- raising input guards ------------------------------------------
    ("raise_strategy_not_ir", "exception", {"strategy": "invalid"}),
    ("raise_controller_state_invalid", "exception", {"controller_state": "invalid"}),
    ("raise_receipt_not_mapping", "exception", {"receipt": {"receipt_invalid": True}}),
    ("raise_pools_not_mapping", "exception", {"receipt": {"pools_invalid": True}}),
    ("raise_current_epoch_bool", "exception", {"call": {"current_epoch": True}}),
    ("raise_current_epoch_negative", "exception", {"call": {"current_epoch": -1}}),
    ("raise_intent_deadline_zero", "exception", {"call": {"intent_deadline": 0}}),
    ("raise_intent_deadline_str", "exception", {"call": {"intent_deadline": "99"}}),
    (
        "raise_fixed_order_size_str",
        "exception",
        {"strategy": {"overrides": [["template_param", "fixed_order_size", "bad"]]}},
    ),
    (
        "raise_fixed_order_size_zero",
        "exception",
        {"strategy": {"overrides": [["template_param", "fixed_order_size", 0]]}},
    ),
    (
        "raise_cadence_zero",
        "exception",
        {"strategy": {"overrides": [["template_param", "cadence_epochs", 0]]}},
    ),
    (
        "raise_asset_in_non_string",
        "exception",
        {"strategy": {"overrides": [["template_param", "asset_in", 1]]}},
    ),
    (
        "raise_asset_in_blank",
        "exception",
        {"strategy": {"overrides": [["template_param", "asset_in", "   "]]}},
    ),
    ("raise_slippage_str", "exception", {"call": {"slippage_bps": "50"}}),
    ("raise_slippage_negative", "exception", {"call": {"slippage_bps": -1}}),
    ("raise_receipt_body_missing", "exception", {"receipt": {"recipe": "no_body"}}),
    (
        "raise_receipt_amount_in_str",
        "exception",
        {"receipt": {"mutations": [["set_body", "amount_in", "100"]]}},
    ),
    (
        "raise_receipt_amount_in_bool",
        "exception",
        {"receipt": {"mutations": [["set_body", "amount_in", True]]}},
    ),
    # ---- single-fault decision probes ----------------------------------
    ("reject_unsupported_template", "single_fault", {"strategy": {"kind": "limit_ladder"}}),
    (
        "reject_action_not_allowed",
        "single_fault",
        {"strategy": {"overrides": [["allowed_actions", ["place_order_intent"]]]}},
    ),
    (
        "reject_assets_outside_universe",
        "single_fault",
        {"strategy": {"overrides": [["asset_universe", ["A", "C"]]]}},
    ),
    ("reject_slippage_limit_exceeded", "single_fault", {"call": {"slippage_bps": 75}}),
    ("reject_receipt_kind_exact_out", "single_fault", {"receipt": {"recipe": "exact_out"}}),
    (
        "reject_receipt_kind_missing",
        "single_fault",
        {"receipt": {"mutations": [["set_body", "kind", ""]]}},
    ),
    ("reject_receipt_asset_mismatch", "single_fault", {"receipt": {"recipe": "reversed_pair"}}),
    ("reject_receipt_amount_mismatch", "single_fault", {"receipt": {"amount_in": 90}}),
    (
        "reject_receipt_missing_quote_epoch",
        "single_fault",
        {"receipt": {"mutations": [["pop_body", "quote_epoch"]]}},
    ),
    (
        "reject_receipt_invalid_quote_epoch_str",
        "single_fault",
        {"receipt": {"mutations": [["set_body", "quote_epoch", "bad"]]}},
    ),
    (
        "reject_receipt_invalid_quote_epoch_bool",
        "single_fault",
        {"receipt": {"mutations": [["set_body", "quote_epoch", True]]}},
    ),
    (
        "reject_receipt_invalid_quote_epoch_range",
        "single_fault",
        {"receipt": {"mutations": [["set_body", "quote_epoch", 4294967296]]}},
    ),
    ("reject_signal_packet_build_failed", "single_fault", {"patches": ["signal_packet_raises"]}),
    (
        "reject_signal_quote_epoch_mismatch",
        "single_fault",
        {"patches": ["signal_packet_epoch_mismatch"]},
    ),
    (
        "reject_lifetime_cap_exceeded",
        "single_fault",
        {
            "controller_state": {
                "window_id": 1,
                "last_action_epoch": 1,
                "lifetime_spent": 950,
            }
        },
    ),
    ("reject_tau_backend_not_enabled", "single_fault", {"strategy": {"backend": "tau"}}),
    (
        "reject_tau_bin_relative",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "tau"},
        },
    ),
    (
        "reject_tau_bin_not_executable",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "/not/an/executable"},
        },
    ),
    (
        "reject_tau_bin_unset",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True},
        },
    ),
    (
        "reject_tau_lookup_fails",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "allow_path_lookup": True},
            "patches": ["find_tau_bin_none"],
        },
    ),
    (
        "reject_tau_runner_error",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_raises"],
        },
    ),
    (
        "reject_tau_missing_output",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_empty"],
        },
    ),
    (
        "reject_tau_mismatch_provenance",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_gate0_provenance"],
        },
    ),
    (
        "reject_signal_provenance_tampered_hash",
        "single_fault",
        {"receipt": {"mutations": [["set_top", "receipt_hash", "receipt.hash.tampered"]]}},
    ),
    ("reject_route_unavailable", "single_fault", {"patches": ["route_snapshot_none"]}),
    (
        "reject_tau_mismatch_route",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_gate0_route"],
        },
    ),
    ("reject_route_mixed_asset_pairs", "single_fault", {"receipt": {"recipe": "multi_hop"}}),
    ("skip_route_extreme_input_stress", "single_fault", {"receipt": {"recipe": "extreme"}}),
    (
        "skip_route_extreme_output_depletion",
        "single_fault",
        {"patches": ["route_snapshot_output_depletion"]},
    ),
    (
        "skip_route_extreme_price_impact",
        "single_fault",
        {"patches": ["route_snapshot_price_impact"]},
    ),
    ("reject_route_unknown_error", "single_fault", {"patches": ["route_snapshot_error_none"]}),
    ("reject_intent_builder_raises", "single_fault", {"patches": ["intents_raise"]}),
    ("reject_intent_list_empty", "single_fault", {"patches": ["intents_empty"]}),
    (
        "reject_intent_amount_invalid_type",
        "single_fault",
        {"patches": ["intents_bad_amount_type"]},
    ),
    ("reject_intent_amount_mismatch", "single_fault", {"patches": ["intents_amount_99"]}),
    (
        "skip_max_intents_per_order",
        "single_fault",
        {
            "strategy": {
                "max_live_orders": 1,
                "max_intents_per_order": 1,
                "per_order_max": 600,
                "per_window_max": 1_000,
                "lifetime_max": 2_000,
                "fixed_order_size": 600,
            },
            "receipt": {"recipe": "split", "amount_in": 600},
            "call": {"nonce_start": 10},
        },
    ),
    (
        "reject_tau_mismatch_execution",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_gate0_execution"],
        },
    ),
    (
        "skip_strategy_window_not_open",
        "single_fault",
        {"receipt": {"quote_epoch": 0}, "call": {"current_epoch": 0}},
    ),
    (
        "skip_strategy_window_expired",
        "single_fault",
        {"call": {"current_epoch": 101}},
    ),
    (
        "reject_non_monotone_epoch",
        "single_fault",
        {
            "controller_state": {
                "window_id": 1,
                "last_action_epoch": 9,
            }
        },
    ),
    (
        "skip_cadence_not_elapsed",
        "single_fault",
        {
            "controller_state": {
                "window_id": 3,
                "spent_in_window": 100,
                "last_action_epoch": 3,
                "lifetime_spent": 100,
            }
        },
    ),
    (
        "skip_min_order_spacing_dominates_cadence",
        "single_fault",
        {
            "strategy": {"min_order_spacing_epochs": 6},
            "controller_state": {
                "window_id": 1,
                "spent_in_window": 100,
                "last_action_epoch": 1,
                "lifetime_spent": 100,
            },
        },
    ),
    (
        "skip_max_live_orders_reached",
        "single_fault",
        {"controller_state": {"live_orders": 3}},
    ),
    (
        "reject_tau_mismatch_oracle",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_gate0_oracle"],
        },
    ),
    (
        "reject_quote_epoch_in_future",
        "single_fault",
        {"receipt": {"quote_epoch": 6}},
    ),
    (
        "skip_quote_receipt_stale",
        "single_fault",
        {"receipt": {"quote_epoch": 1}},
    ),
    ("reject_budget_window_roll_failed", "single_fault", {"patches": ["roll_window_fails"]}),
    (
        "reject_budget_window_regression",
        "single_fault",
        {
            "controller_state": {
                "window_id": 9,
                "last_action_epoch": 1,
            }
        },
    ),
    (
        "reject_tau_mismatch_budget",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "patches": ["tau_runner_gate0_budget"],
        },
    ),
    (
        "skip_budget_window_budget_exceeded",
        "single_fault",
        {
            "controller_state": {
                "window_id": 1,
                "spent_in_window": 450,
                "last_action_epoch": 1,
                "lifetime_spent": 450,
            }
        },
    ),
    (
        "skip_budget_kill_switch_active",
        "single_fault",
        {
            "controller_state": {
                "window_id": 1,
                "kill_switch_on": True,
                "last_action_epoch": 1,
            }
        },
    ),
    (
        "reject_budget_per_order_limit",
        "single_fault",
        {"strategy": {"per_order_max": 50}},
    ),
    (
        "reject_budget_spent_overflow",
        "single_fault",
        {
            "controller_state": {
                "window_id": 1,
                "spent_in_window": 4294967245,
                "last_action_epoch": 1,
            }
        },
    ),
    (
        "reject_tau_mismatch_inverted_expected",
        "single_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "@SYS_EXECUTABLE@"},
            "receipt": {"mutations": [["set_top", "receipt_hash", "receipt.hash.tampered"]]},
            "patches": ["tau_runner_ok"],
        },
    ),
    # ---- multi-fault precedence probes (first-failure-wins order) -------
    (
        "prec_template_beats_action_and_assets",
        "multi_fault",
        {"strategy": {"kind": "limit_ladder"}, "receipt": {"recipe": "reversed_pair"}},
    ),
    (
        "prec_action_beats_universe",
        "multi_fault",
        {
            "strategy": {
                "overrides": [
                    ["allowed_actions", ["place_order_intent"]],
                    ["asset_universe", ["A", "C"]],
                ]
            }
        },
    ),
    (
        "prec_universe_beats_slippage",
        "multi_fault",
        {
            "strategy": {"overrides": [["asset_universe", ["A", "C"]]]},
            "call": {"slippage_bps": 75},
        },
    ),
    (
        "prec_slippage_beats_receipt_kind",
        "multi_fault",
        {"receipt": {"recipe": "exact_out"}, "call": {"slippage_bps": 75}},
    ),
    (
        "prec_kind_beats_asset_and_amount",
        "multi_fault",
        {"receipt": {"recipe": "exact_out_reversed", "amount_in": 90}},
    ),
    (
        "prec_asset_beats_amount",
        "multi_fault",
        {"receipt": {"recipe": "reversed_pair", "amount_in": 90}},
    ),
    (
        "prec_amount_beats_missing_epoch",
        "multi_fault",
        {"receipt": {"amount_in": 90, "mutations": [["pop_body", "quote_epoch"]]}},
    ),
    (
        "prec_missing_epoch_beats_lifetime",
        "multi_fault",
        {
            "receipt": {"mutations": [["pop_body", "quote_epoch"]]},
            "controller_state": {
                "window_id": 1,
                "last_action_epoch": 1,
                "lifetime_spent": 950,
            },
        },
    ),
    (
        "prec_lifetime_beats_provenance",
        "multi_fault",
        {
            "receipt": {"mutations": [["set_top", "receipt_hash", "receipt.hash.tampered"]]},
            "controller_state": {
                "window_id": 1,
                "last_action_epoch": 1,
                "lifetime_spent": 950,
            },
        },
    ),
    (
        "prec_lifetime_beats_window_not_open",
        "multi_fault",
        {
            "receipt": {"quote_epoch": 0},
            "call": {"current_epoch": 0},
            "controller_state": {"lifetime_spent": 950},
        },
    ),
    (
        "prec_provenance_beats_stale",
        "multi_fault",
        {
            "receipt": {
                "quote_epoch": 1,
                "mutations": [["set_top", "receipt_hash", "receipt.hash.tampered"]],
            }
        },
    ),
    (
        "prec_intent_cap_beats_stale",
        "multi_fault",
        {
            "strategy": {
                "max_live_orders": 1,
                "max_intents_per_order": 1,
                "per_order_max": 600,
                "per_window_max": 1_000,
                "lifetime_max": 2_000,
                "fixed_order_size": 600,
            },
            "receipt": {"recipe": "split", "amount_in": 600, "quote_epoch": 1},
        },
    ),
    (
        "prec_window_expired_beats_stale",
        "multi_fault",
        {"call": {"current_epoch": 101}, "receipt": {"quote_epoch": 5}},
    ),
    (
        "prec_stale_beats_window_budget",
        "multi_fault",
        {
            "receipt": {"quote_epoch": 1},
            "controller_state": {
                "window_id": 1,
                "spent_in_window": 450,
                "last_action_epoch": 1,
                "lifetime_spent": 450,
            },
        },
    ),
    (
        "prec_cadence_beats_budget_regression",
        "multi_fault",
        {
            "controller_state": {
                "window_id": 9,
                "spent_in_window": 0,
                "last_action_epoch": 3,
                "lifetime_spent": 100,
            }
        },
    ),
    (
        "prec_tau_unavailable_beats_provenance",
        "multi_fault",
        {
            "strategy": {"backend": "tau"},
            "tau_config": {"enabled": True, "tau_bin": "/not/an/executable"},
            "receipt": {"mutations": [["set_top", "receipt_hash", "receipt.hash.tampered"]]},
        },
    ),
    (
        "prec_fixed_order_size_raise_beats_cadence_raise",
        "multi_fault",
        {
            "strategy": {
                "overrides": [
                    ["template_param", "fixed_order_size", "bad"],
                    ["template_param", "cadence_epochs", 0],
                ]
            }
        },
    ),
    (
        "prec_template_param_raise_beats_missing_body",
        "multi_fault",
        {
            "strategy": {"overrides": [["template_param", "fixed_order_size", "bad"]]},
            "receipt": {"recipe": "no_body"},
        },
    ),
]


# Reason strings (exact, or prefix when marked) that the corpus MUST lock.
# This is the reachable-surface enumeration from reading the evaluator source.
REQUIRED_DECISION_REASONS: list[tuple[str, str]] = [
    # (match_kind, value) with match_kind in {"exact", "prefix"}
    ("prefix", "unsupported_strategy_template:"),
    ("exact", "strategy_action_not_allowed:place_swap_exact_in"),
    ("exact", "strategy_assets_outside_universe"),
    ("prefix", "slippage_limit_exceeded:"),
    ("prefix", "unsupported_receipt_kind:"),
    ("prefix", "receipt_asset_mismatch:"),
    ("prefix", "receipt_amount_mismatch:"),
    ("exact", "receipt_missing_quote_epoch"),
    ("exact", "receipt_invalid_quote_epoch"),
    ("prefix", "signal_packet_build_failed:"),
    ("prefix", "signal_quote_epoch_mismatch:"),
    ("prefix", "lifetime_cap_exceeded:"),
    ("exact", "tau_policy_backend_requires_enabled_tau_config"),
    ("prefix", "tau_tool_unavailable:"),
    ("prefix", "tau_policy_runner_error:"),
    ("prefix", "tau_policy_missing_output:"),
    ("prefix", "tau_policy_mismatch:"),
    ("prefix", "signal_provenance_rejected:"),
    ("exact", "route_economic_sanity_unavailable"),
    ("prefix", "route_economic_sanity_rejected:"),
    ("prefix", "intent_construction_failed:"),
    ("prefix", "intent_amount_missing_or_invalid:"),
    ("prefix", "intent_amount_mismatch:"),
    ("prefix", "max_intents_per_order_exceeded:"),
    ("prefix", "strategy_window_not_open:"),
    ("prefix", "strategy_window_expired:"),
    ("prefix", "non_monotone_epoch:"),
    ("prefix", "cadence_not_elapsed:"),
    ("prefix", "max_live_orders_reached:"),
    ("prefix", "quote_epoch_in_future:"),
    ("prefix", "quote_receipt_stale:"),
    ("prefix", "budget_window_roll_failed:"),
    ("prefix", "budget_window_regression:"),
    ("prefix", "budget_guard_rejected:"),
    ("exact", "policy_guard_passed"),
]

# Budget guard sub-codes that must each be present in a locked reason string.
REQUIRED_BUDGET_SUBCODES = [
    "kill_switch_active",
    "window_budget_exceeded",
    "per_order_limit_exceeded",
    "spent_overflow",
]

# Route sub-codes that must each be present in a locked reason string.
REQUIRED_ROUTE_SUBCODES = [
    "route_mixed_asset_pairs",
    "route_extreme_input_stress:",
    "route_extreme_output_depletion:",
    "route_extreme_price_impact:",
    "route_economic_sanity_unknown",
]

# Exception messages (exact, or prefix when marked) that the corpus MUST lock.
REQUIRED_EXCEPTION_MESSAGES: list[tuple[str, str, str]] = [
    # (exception_type, match_kind, value)
    ("TypeError", "exact", "strategy must be a StrategyIR"),
    ("TypeError", "exact", "controller_state must be an AutoTraderControllerState"),
    ("TypeError", "exact", "receipt must be a mapping"),
    ("TypeError", "exact", "pools_by_id must be a mapping"),
    ("TypeError", "exact", "current_epoch must be an int"),
    ("ValueError", "prefix", "current_epoch out of u32 range:"),
    ("TypeError", "exact", "intent_deadline must be an int"),
    ("ValueError", "prefix", "intent_deadline out of u32 range:"),
    ("TypeError", "exact", "slippage_bps must be an int"),
    ("ValueError", "prefix", "slippage_bps out of u32 range:"),
    ("ValueError", "exact", "strategy template param must be an int: fixed_order_size"),
    ("ValueError", "prefix", "strategy template param out of range: fixed_order_size="),
    ("ValueError", "prefix", "strategy template param out of range: cadence_epochs="),
    ("ValueError", "exact", "strategy template param must be a string: asset_in"),
    ("ValueError", "exact", "strategy template param must be non-empty: asset_in"),
    ("ValueError", "exact", "missing receipt.body"),
    ("ValueError", "exact", "receipt body field must be an int: amount_in"),
]


def _build_corpus() -> dict[str, Any]:
    case_ids = [case_id for case_id, _, _ in CASES]
    if len(set(case_ids)) != len(case_ids):
        raise RuntimeError("duplicate corpus case ids")
    cases = []
    for case_id, kind, spec in CASES:
        cases.append(
            {
                "id": case_id,
                "kind": kind,
                "spec": spec,
                "expected": run_case(spec),
            }
        )
    return {
        "schema": CORPUS_SCHEMA,
        "base_commit": BASE_COMMIT,
        "semantics": "first_failure_wins",
        "target": "src.integration.autotrader_controller.evaluate_autotrader_quote_receipt",
        "cases": cases,
    }


def _corpus_text(corpus: Mapping[str, Any]) -> str:
    return json.dumps(corpus, indent=2, sort_keys=True) + "\n"


def _load_corpus() -> dict[str, Any]:
    if not CORPUS_PATH.is_file():
        pytest.fail(
            f"missing corpus file {CORPUS_PATH}; regenerate with "
            "python3 tests/integration/test_autotrader_controller_characterization.py --regen"
        )
    return json.loads(CORPUS_PATH.read_text(encoding="utf-8"))


_CORPUS = json.loads(CORPUS_PATH.read_text(encoding="utf-8")) if CORPUS_PATH.is_file() else None


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "case",
    (_CORPUS["cases"] if _CORPUS else []),
    ids=(lambda case: case["id"]),
)
def test_corpus_case_reproduces(case: dict[str, Any]) -> None:
    actual = json.loads(json.dumps(run_case(case["spec"])))
    assert actual == case["expected"], (
        f"characterization drift for case {case['id']!r}:\n"
        f"expected: {json.dumps(case['expected'], indent=2, sort_keys=True)}\n"
        f"actual:   {json.dumps(actual, indent=2, sort_keys=True)}"
    )


def test_corpus_exists_and_matches_module_cases() -> None:
    corpus = _load_corpus()
    assert corpus["schema"] == CORPUS_SCHEMA
    assert corpus["semantics"] == "first_failure_wins"
    file_ids = [case["id"] for case in corpus["cases"]]
    module_ids = [case_id for case_id, _, _ in CASES]
    assert file_ids == module_ids, "corpus file cases out of sync with CASES; rerun --regen"


def test_corpus_regen_is_byte_identical() -> None:
    corpus = _load_corpus()
    regenerated = _corpus_text(json.loads(json.dumps(_build_corpus())))
    on_disk = CORPUS_PATH.read_text(encoding="utf-8")
    assert regenerated == on_disk, (
        "regenerated corpus differs from committed corpus; "
        "either behavior drifted or the corpus needs --regen"
    )
    assert _corpus_text(corpus) == on_disk


def test_corpus_covers_all_targeted_codes() -> None:
    corpus = _load_corpus()
    reasons: list[str] = []
    exceptions: list[tuple[str, str]] = []
    for case in corpus["cases"]:
        expected = case["expected"]
        if expected["outcome"] == "decision":
            reasons.append(expected["decision"]["reason"])
        else:
            exceptions.append((expected["exception_type"], expected["exception_message"]))

    for match_kind, value in REQUIRED_DECISION_REASONS:
        if match_kind == "exact":
            assert value in reasons, f"corpus does not lock reason {value!r}"
        else:
            assert any(reason.startswith(value) for reason in reasons), (
                f"corpus does not lock reason prefix {value!r}"
            )
    for subcode in REQUIRED_BUDGET_SUBCODES:
        assert any(
            reason == f"budget_guard_rejected:{subcode}" for reason in reasons
        ), f"corpus does not lock budget sub-code {subcode!r}"
    for subcode in REQUIRED_ROUTE_SUBCODES:
        assert any(
            reason.startswith(f"route_economic_sanity_rejected:{subcode}")
            for reason in reasons
        ), f"corpus does not lock route sub-code {subcode!r}"
    for exc_type, match_kind, value in REQUIRED_EXCEPTION_MESSAGES:
        if match_kind == "exact":
            assert (exc_type, value) in exceptions, (
                f"corpus does not lock exception {exc_type}:{value!r}"
            )
        else:
            assert any(
                etype == exc_type and message.startswith(value)
                for etype, message in exceptions
            ), f"corpus does not lock exception prefix {exc_type}:{value!r}"

    kinds = [case["kind"] for case in corpus["cases"]]
    assert kinds.count("multi_fault") >= 6, "need at least 6 multi-fault precedence probes"
    assert kinds.count("valid") >= 1
    tags = [
        case["expected"]["decision"]["tag"]
        for case in corpus["cases"]
        if case["expected"]["outcome"] == "decision"
    ]
    assert "submit" in tags and "skip" in tags and "reject" in tags


# ---------------------------------------------------------------------------
# Single-read discipline audit (adversarial mapping probe)
# ---------------------------------------------------------------------------


class _RecordingMapping(collections.abc.Mapping):
    """Mapping wrapper that records every read and lets .get diverge from []."""

    def __init__(
        self,
        data: dict[str, Any],
        log: list[tuple[str, str]],
        label: str,
        get_overrides: dict[str, Any] | None = None,
    ) -> None:
        self._data = data
        self._log = log
        self._label = label
        self._get_overrides = get_overrides or {}

    def __getitem__(self, key: str) -> Any:
        self._log.append((f"{self._label}.getitem", key))
        return self._data[key]

    def __iter__(self) -> Any:
        self._log.append((f"{self._label}.iter", ""))
        return iter(self._data)

    def __len__(self) -> int:
        return len(self._data)

    def get(self, key: str, default: Any = None) -> Any:
        self._log.append((f"{self._label}.get", key))
        if key in self._get_overrides:
            return self._get_overrides[key]
        return self._data.get(key, default)


def test_single_read_discipline_with_adversarial_mapping() -> None:
    """Adversarial mapping whose .get('body') diverges from ['body']/iteration.

    The evaluator reads the receipt body exactly once via ``receipt.get("body")``
    (then copies it); dict() pass-throughs into collaborators use
    __iter__/__getitem__. The divergence makes any .get <-> [] swap, or any
    re-read of the body from the original mapping, change the decision.

    Expected values locked from the PRISTINE module at base commit ad96b74d:
    - .get sees the real body (amount_in=100 matches the strategy), so the
      evaluator passes its receipt-shape guards;
    - dict(receipt) sees a tampered body (amount_in=999), so receipt-hash
      verification fails inside the signal packet builder ->
      ``signal_provenance_rejected:signal_auth_invalid``.
    """
    strategy = _compiled_strategy()
    pools, receipt = _receipt_pools("single_hop", amount_in=100, quote_epoch=5)
    log: list[tuple[str, str]] = []
    real_body = receipt["body"]
    assert isinstance(real_body, dict)
    divergent_body = dict(real_body)
    divergent_body["amount_in"] = 999
    wrapped = _RecordingMapping(
        {**dict(receipt), "body": divergent_body},
        log,
        "receipt",
        get_overrides={"body": real_body},
    )

    decision = evaluate_autotrader_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=wrapped,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
    )

    assert decision.tag.value == "reject"
    assert decision.reason == "signal_provenance_rejected:signal_auth_invalid"
    assert "receipt_amount_in=100" in decision.explain

    # The evaluator's own direct read must stay the FIRST access and must be
    # .get("body"); the full .get sequence (evaluator + signal packet builder)
    # is locked, and provenance rejection must stop the receipt reads there.
    get_calls = [entry for entry in log if entry[0] == "receipt.get"]
    assert log[0] == ("receipt.get", "body")
    assert get_calls == [
        ("receipt.get", "body"),
        ("receipt.get", "body"),
        ("receipt.get", "receipt_hash"),
    ], f"receipt .get sequence drifted: {get_calls}"
    iter_calls = [entry for entry in log if entry[0] == "receipt.iter"]
    assert len(iter_calls) == 1, (
        f"receipt dict() materialization count drifted: {len(iter_calls)}"
    )


def test_single_read_full_access_log_stable_on_submit() -> None:
    """Lock the complete receipt access pattern on the full SUBMIT path."""
    strategy = _compiled_strategy()
    pools, receipt = _receipt_pools("single_hop", amount_in=100, quote_epoch=5)
    log: list[tuple[str, str]] = []
    wrapped = _RecordingMapping(dict(receipt), log, "receipt")

    decision = evaluate_autotrader_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=wrapped,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
    )

    assert decision.tag.value == "submit"
    assert decision.reason == "policy_guard_passed"
    # First direct access must be the evaluator's body fetch via .get.
    assert log[0] == ("receipt.get", "body")
    get_calls = [entry for entry in log if entry[0] == "receipt.get"]
    getitem_calls = [entry for entry in log if entry[0] == "receipt.getitem"]
    iter_calls = [entry for entry in log if entry[0] == "receipt.iter"]
    # Locked counts from the pristine module at ad96b74d:
    # - 3 .get("body") (evaluator, signal packet builder, route snapshot)
    # - 1 .get("receipt_hash") (signal packet builder)
    # - 3 full dict() materializations (signal verify, route verify, the
    #   evaluator's dict(receipt) for the intent builder).
    assert get_calls == [
        ("receipt.get", "body"),
        ("receipt.get", "body"),
        ("receipt.get", "receipt_hash"),
        ("receipt.get", "body"),
    ], f"receipt .get sequence drifted: {get_calls}"
    assert len(iter_calls) == 3, (
        f"receipt dict() materialization count drifted: {len(iter_calls)}"
    )
    expected_getitems = sorted(list(dict(receipt).keys()) * 3)
    assert sorted(key for _, key in getitem_calls) == expected_getitems


# ---------------------------------------------------------------------------
# CLI: --regen / --check
# ---------------------------------------------------------------------------


def _main(argv: list[str]) -> int:
    if argv == ["--regen"]:
        corpus = json.loads(json.dumps(_build_corpus()))
        CORPUS_PATH.parent.mkdir(parents=True, exist_ok=True)
        CORPUS_PATH.write_text(_corpus_text(corpus), encoding="utf-8")
        print(f"wrote {CORPUS_PATH} ({len(corpus['cases'])} cases)", file=sys.stderr)
        return 0
    if argv == ["--check"]:
        regenerated = _corpus_text(json.loads(json.dumps(_build_corpus())))
        on_disk = CORPUS_PATH.read_text(encoding="utf-8") if CORPUS_PATH.is_file() else ""
        if regenerated != on_disk:
            print("corpus drift detected", file=sys.stderr)
            return 1
        print("corpus byte-identical", file=sys.stderr)
        return 0
    print(
        "usage: test_autotrader_controller_characterization.py [--regen|--check]",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(_main(sys.argv[1:]))
