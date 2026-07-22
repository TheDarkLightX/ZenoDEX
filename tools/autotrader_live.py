#!/usr/bin/env python3
"""Live-preparation CLI for the policy-constrained auto-trader."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.autotrader_client_policy_bundle import (  # noqa: E402
    AutoTraderClientPolicyBundle,
    load_autotrader_client_policy_bundle_file,
    sign_autotrader_client_policy_bundle,
)
from src.agents.autotrader_user_rule_bundle import (  # noqa: E402
    AutoTraderUserMarket,
    AutoTraderUserRuleBundle,
    AutoTraderUserRuleMode,
    AutoTraderUserRulePreset,
    build_autotrader_client_policy_bundle_from_user_rule_bundle,
    build_autotrader_user_rule_bundle_from_mode,
    build_autotrader_user_rule_bundle_from_preset,
    build_autotrader_user_rule_source_artifact,
    compare_autotrader_user_rule_presets,
    compile_autotrader_user_rule_bundle,
    describe_autotrader_user_rule_preset,
    list_autotrader_user_rule_presets,
    load_autotrader_user_rule_bundle_file,
    recommend_autotrader_user_rule_preset,
)
from src.agents.krr_bundle_artifacts import (  # noqa: E402
    AutoTraderKRRBundle,
    bundle_runtime_artifacts,
    load_autotrader_krr_bundle_file,
)
from src.agents.local_policy import load_local_policy_file  # noqa: E402
from src.agents.policy_artifacts import (  # noqa: E402
    StrategyPolicyArtifact,
    StrategySourceArtifact,
    TauPolicyBundle,
    build_strategy_policy_artifact,
    build_tau_policy_bundle,
    sign_strategy_policy_artifact,
    strategy_policy_artifact_from_dict,
    tau_policy_bundle_from_dict,
)
from src.agents.policy_compiler import compile_policy_candidate  # noqa: E402
from src.agents.policy_text_compiler import compile_policy_text  # noqa: E402
from src.agents.strategy_ir import PolicyBackend, StrategyAction, StrategyIR  # noqa: E402
from src.agents.tau_policy_adapter import build_compile_contract_tau_policy_receipt  # noqa: E402
from src.integration.autotrader_controller import (  # noqa: E402
    AutoTraderControllerState,
    AutoTraderDecision,
    AutoTraderDecisionTag,
    AutoTraderTauConfig,
)
from src.integration.autotrader_live import (  # noqa: E402
    AutoTraderLiveReport,
    prepare_autotrader_live_quote_receipt,
)
from src.integration.autotrader_risk_disclosure import (  # noqa: E402
    build_autotrader_risk_disclosure,
)
from src.integration.autotrader_signal_registry import (  # noqa: E402
    ExternalSignalSourceRegistry,
    external_signal_source_registry_from_object,
    verify_external_signal_source_registry_payload,
)
from src.integration.autotrader_signals import (  # noqa: E402
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    external_signal_observations_from_object,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey  # noqa: E402
from src.kernels.python.strategy_budget_guard_v1_adapter import (  # noqa: E402
    StrategyBudgetState,
)
from src.state.immutable_collections import deep_thaw_json  # noqa: E402
from src.state.intents import Intent  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402

_LIVE_RISK_ACK_FLAG = "--acknowledge-experimental-live-risk"
_LIVE_RISK_ACK_ERROR = (
    "autotrader_live_requires_risk_acknowledgement: "
    "advanced experimental automation can lose everything; "
    f"rerun with {_LIVE_RISK_ACK_FLAG} only if you understand and accept the risk"
)


def _load_json_file(path: str | Path) -> Any:
    p = Path(path).expanduser().resolve()
    return json.loads(p.read_text(encoding="utf-8"))


def _load_receipt_file(
    path: str | Path,
) -> tuple[Mapping[str, object] | None, str | None]:
    try:
        obj = _load_json_file(path)
        if not isinstance(obj, Mapping):
            raise ValueError("receipt file must be an object")
        return obj, None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _require_intish(value: object, *, name: str) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must not be a bool")
    if isinstance(value, (int, str)):
        return int(value)
    raise ValueError(f"{name} must be int-like")


def _require_bool(value: object, *, name: str) -> bool:
    if isinstance(value, bool):
        return value
    raise ValueError(f"{name} must be a bool")


def _pool_status_from_value(value: object) -> PoolStatus:
    if isinstance(value, PoolStatus):
        return value
    if not isinstance(value, str):
        raise ValueError("pool status must be a string")
    return PoolStatus(value.strip().upper())


def _pool_state_from_dict(data: Mapping[str, object]) -> PoolState:
    return PoolState(
        pool_id=str(data["pool_id"]),
        asset0=str(data["asset0"]),
        asset1=str(data["asset1"]),
        reserve0=_require_intish(data["reserve0"], name="reserve0"),
        reserve1=_require_intish(data["reserve1"], name="reserve1"),
        fee_bps=_require_intish(data["fee_bps"], name="fee_bps"),
        lp_supply=_require_intish(data["lp_supply"], name="lp_supply"),
        status=_pool_status_from_value(data["status"]),
        created_at=_require_intish(data["created_at"], name="created_at"),
        curve_tag=str(data.get("curve_tag", "CPMM")),
        curve_params=str(data.get("curve_params", "")),
    )


def _load_pools_file(
    path: str | Path,
) -> tuple[dict[str, PoolState] | None, str | None]:
    try:
        obj = _load_json_file(path)
        if isinstance(obj, dict):
            if "pools" in obj:
                obj = obj["pools"]
            if isinstance(obj, Mapping) and all(isinstance(v, Mapping) for v in obj.values()):
                return {str(key): _pool_state_from_dict(value) for key, value in obj.items()}, None
        if isinstance(obj, list):
            pools: dict[str, PoolState] = {}
            for row in obj:
                if not isinstance(row, Mapping):
                    raise ValueError("pool list entries must be objects")
                pool = _pool_state_from_dict(row)
                pools[pool.pool_id] = pool
            return pools, None
        raise ValueError("pools file must be a map of pool_id -> pool object or a list of pool objects")
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _controller_state_from_dict(data: Mapping[str, object]) -> AutoTraderControllerState:
    if "controller_state" in data:
        nested = data["controller_state"]
        if not isinstance(nested, Mapping):
            raise ValueError("controller_state must be an object")
        data = nested
    budget_raw = data.get("budget_state", {})
    if not isinstance(budget_raw, Mapping):
        raise ValueError("budget_state must be an object")
    budget_state = StrategyBudgetState(
        window_id=int(budget_raw.get("window_id", 0)),
        spent_in_window=int(budget_raw.get("spent_in_window", 0)),
        kill_switch_on=_require_bool(budget_raw.get("kill_switch_on", False), name="budget_state.kill_switch_on"),
    )
    last_action_epoch_raw = data.get("last_action_epoch")
    return AutoTraderControllerState(
        budget_state=budget_state,
        last_action_epoch=(None if last_action_epoch_raw is None else _require_intish(last_action_epoch_raw, name="last_action_epoch")),
        lifetime_spent=_require_intish(data.get("lifetime_spent", 0), name="lifetime_spent"),
        live_orders=_require_intish(data.get("live_orders", 0), name="live_orders"),
    )


def _load_controller_state_file(
    path: str | Path | None,
) -> tuple[AutoTraderControllerState, str | None]:
    if path is None:
        return AutoTraderControllerState(), None
    try:
        obj = _load_json_file(path)
        if not isinstance(obj, Mapping):
            raise ValueError("controller state file must be an object")
        return _controller_state_from_dict(obj), None
    except Exception as exc:
        return AutoTraderControllerState(), f"{type(exc).__name__}: {exc}"


def _wallet_capability_from_dict(data: Mapping[str, object]) -> AutoTraderWalletCapability:
    if "wallet_capability" in data:
        nested = data["wallet_capability"]
        if not isinstance(nested, Mapping):
            raise ValueError("wallet_capability must be an object")
        data = nested
    allowed_assets_raw = data.get("allowed_assets", ())
    allowed_actions_raw = data.get("allowed_actions", ())
    if not isinstance(allowed_assets_raw, (list, tuple)):
        raise ValueError("allowed_assets must be a list")
    if not isinstance(allowed_actions_raw, (list, tuple)):
        raise ValueError("allowed_actions must be a list")
    return AutoTraderWalletCapability(
        session_id=str(data.get("session_id", "")),
        owner_pubkey=str(data.get("owner_pubkey", "")),
        chain_id=str(data.get("chain_id", "")),
        valid_from_epoch=_require_intish(data.get("valid_from_epoch", 0), name="valid_from_epoch"),
        valid_until_epoch=_require_intish(data.get("valid_until_epoch", 0), name="valid_until_epoch"),
        notional_remaining=_require_intish(data.get("notional_remaining", 0), name="notional_remaining"),
        allowed_assets=tuple(str(asset) for asset in allowed_assets_raw),
        allowed_actions=tuple(StrategyAction(str(action)) for action in allowed_actions_raw),
        enabled=_require_bool(data.get("enabled", True), name="enabled"),
    )


def _load_wallet_capability_file(
    path: str | Path | None,
) -> tuple[AutoTraderWalletCapability | None, str | None]:
    if path is None:
        return None, None
    try:
        obj = _load_json_file(path)
        if not isinstance(obj, Mapping):
            raise ValueError("wallet capability file must be an object")
        return _wallet_capability_from_dict(obj), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _session_state_from_dict(data: Mapping[str, object]) -> AutoTraderSessionState:
    if "session_state" in data:
        nested = data["session_state"]
        if not isinstance(nested, Mapping):
            raise ValueError("session_state must be an object")
        data = nested
    return AutoTraderSessionState(
        session_id=str(data.get("session_id", "")),
        owner_pubkey=str(data.get("owner_pubkey", "")),
        chain_id=str(data.get("chain_id", "")),
        enabled=_require_bool(data.get("enabled", True), name="enabled"),
        revoked_at_epoch=(
            None
            if data.get("revoked_at_epoch") is None
            else _require_intish(data.get("revoked_at_epoch"), name="revoked_at_epoch")
        ),
    )


def _load_session_state_file(
    path: str | Path | None,
) -> tuple[AutoTraderSessionState | None, str | None]:
    if path is None:
        return None, None
    try:
        obj = _load_json_file(path)
        if not isinstance(obj, Mapping):
            raise ValueError("session state file must be an object")
        return _session_state_from_dict(obj), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _load_external_signals_file(
    path: str | Path | None,
) -> tuple[tuple[ExternalSignalObservation, ...], str | None]:
    if path is None:
        return (), None
    try:
        obj = _load_json_file(path)
        return tuple(external_signal_observations_from_object(obj)), None
    except Exception as exc:
        return (), f"{type(exc).__name__}: {exc}"


def _load_signal_source_registry_file(
    path: str | Path | None,
) -> tuple[ExternalSignalSourceRegistry | None, str | None]:
    if path is None:
        return None, None
    try:
        obj = _load_json_file(path)
        if isinstance(obj, Mapping) and "schema" in obj:
            ok, error = verify_external_signal_source_registry_payload(obj)
            if not ok:
                raise ValueError(f"signal source registry payload rejected: {error}")
        return external_signal_source_registry_from_object(obj), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _load_krr_bundle_file(
    path: str | Path | None,
) -> tuple[AutoTraderKRRBundle | None, str | None]:
    if path is None:
        return None, None
    try:
        return load_autotrader_krr_bundle_file(path), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _load_policy_artifact_file(
    path: str | Path | None,
) -> tuple[StrategyPolicyArtifact | None, str | None]:
    if path is None:
        return None, None
    try:
        obj = _load_json_file(path)
        if not isinstance(obj, Mapping):
            raise ValueError("policy artifact file must be an object")
        return strategy_policy_artifact_from_dict(obj), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _load_tau_policy_bundle_file(
    path: str | Path | None,
) -> tuple[TauPolicyBundle | None, str | None]:
    if path is None:
        return None, None
    try:
        obj = _load_json_file(path)
        if not isinstance(obj, Mapping):
            raise ValueError("tau policy bundle file must be an object")
        return tau_policy_bundle_from_dict(obj), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _load_client_policy_bundle_file(
    path: str | Path | None,
) -> tuple[AutoTraderClientPolicyBundle | None, str | None]:
    if path is None:
        return None, None
    # Defer signature enforcement to the live admission contract so client-bundle
    # integrity failures land in the structured live report instead of stderr-only
    # process failures.
    try:
        return load_autotrader_client_policy_bundle_file(path, require_signature=False), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _default_user_rule_built_at() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _resolve_authored_owner_pubkey(
    *,
    owner_pubkey: str | None,
    signer_privkey: str,
) -> str:
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(signer_privkey)
    if owner_pubkey is None:
        return signer_pubkey
    resolved = str(owner_pubkey).strip()
    if not resolved:
        raise ValueError("owner_pubkey must be non-empty when provided")
    if resolved != signer_pubkey:
        raise ValueError("authored user rule owner_pubkey must match signer pubkey")
    return resolved


def _load_user_rule_bundle_file(
    path: str | Path,
) -> tuple[AutoTraderUserRuleBundle | None, str | None]:
    try:
        return load_autotrader_user_rule_bundle_file(path), None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def _build_user_rule_bundle_from_mode_args(
    args: argparse.Namespace,
    *,
    owner_pubkey: str,
) -> AutoTraderUserRuleBundle:
    if args.user_rule_mode is None:
        raise ValueError("--user-rule-mode is required")
    mode = AutoTraderUserRuleMode(str(args.user_rule_mode))
    missing: list[str] = []
    for name in (
        "asset_in",
        "asset_out",
        "fixed_order_size",
        "per_window_max",
        "lifetime_max",
        "max_slippage_bps",
        "max_oracle_staleness_epochs",
        "valid_from_epoch",
        "valid_until_epoch",
    ):
        if getattr(args, name) is None:
            missing.append(f"--{name.replace('_', '-')}")
    if mode is AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN:
        if args.cadence_epochs is None:
            missing.append("--cadence-epochs")
        if args.trigger_price is not None:
            raise ValueError("dca_swap_exact_in does not accept --trigger-price")
    elif mode in (
        AutoTraderUserRuleMode.STOP_LOSS_ORDER_INTENT,
        AutoTraderUserRuleMode.TAKE_PROFIT_ORDER_INTENT,
    ):
        if args.trigger_price is None:
            missing.append("--trigger-price")
        if args.cadence_epochs is not None:
            raise ValueError(f"{mode.value} does not accept --cadence-epochs")
    if missing:
        raise ValueError("--user-rule-mode requires " + ", ".join(missing))
    policy_backend = PolicyBackend(str(args.user_rule_policy_backend))
    return build_autotrader_user_rule_bundle_from_mode(
        bundle_name=str(args.user_rule_bundle_name or f"autotrader.{mode.value}.bundle"),
        built_at=str(args.user_rule_built_at or _default_user_rule_built_at()),
        strategy_id=str(args.user_rule_strategy_id or f"autotrader.{mode.value}"),
        owner_pubkey=owner_pubkey,
        policy_backend=policy_backend,
        mode=mode,
        market=AutoTraderUserMarket(
            asset_in=str(args.asset_in),
            asset_out=str(args.asset_out),
        ),
        fixed_order_size=int(args.fixed_order_size),
        per_window_max=int(args.per_window_max),
        lifetime_max=int(args.lifetime_max),
        max_slippage_bps=int(args.max_slippage_bps),
        max_oracle_staleness_epochs=int(args.max_oracle_staleness_epochs),
        valid_from_epoch=int(args.valid_from_epoch),
        valid_until_epoch=int(args.valid_until_epoch),
        min_order_spacing_epochs=int(args.min_order_spacing_epochs or 0),
        max_live_orders=int(args.max_live_orders or 3),
        cadence_epochs=None if args.cadence_epochs is None else int(args.cadence_epochs),
        trigger_price=None if args.trigger_price is None else int(args.trigger_price),
    )


def _build_user_rule_bundle_from_preset_args(
    args: argparse.Namespace,
    *,
    owner_pubkey: str,
) -> AutoTraderUserRuleBundle:
    preset_id = AutoTraderUserRulePreset(str(args.user_rule_preset))
    preset_description = describe_autotrader_user_rule_preset(preset_id)
    if preset_description is None:
        raise ValueError(f"unknown preset: {preset_id.value}")
    preset_mode = str(preset_description.get("mode"))
    missing: list[str] = []
    for name in (
        "asset_in",
        "asset_out",
        "fixed_order_size",
        "valid_from_epoch",
        "valid_until_epoch",
    ):
        if getattr(args, name) is None:
            missing.append(f"--{name.replace('_', '-')}")
    if preset_mode == AutoTraderUserRuleMode.DCA_SWAP_EXACT_IN.value:
        if args.cadence_epochs is None:
            missing.append("--cadence-epochs")
        if args.trigger_price is not None:
            raise ValueError(f"{preset_id.value} does not accept --trigger-price")
    else:
        if args.trigger_price is None:
            missing.append("--trigger-price")
        if args.cadence_epochs is not None:
            raise ValueError(f"{preset_id.value} does not accept --cadence-epochs")
    if missing:
        raise ValueError("--user-rule-preset requires " + ", ".join(missing))
    policy_backend = PolicyBackend(str(args.user_rule_policy_backend))
    return build_autotrader_user_rule_bundle_from_preset(
        bundle_name=str(args.user_rule_bundle_name or f"autotrader.{preset_id.value}.bundle"),
        built_at=str(args.user_rule_built_at or _default_user_rule_built_at()),
        strategy_id=str(args.user_rule_strategy_id or f"autotrader.{preset_id.value}"),
        owner_pubkey=owner_pubkey,
        policy_backend=policy_backend,
        preset_id=preset_id,
        market=AutoTraderUserMarket(
            asset_in=str(args.asset_in),
            asset_out=str(args.asset_out),
        ),
        fixed_order_size=int(args.fixed_order_size),
        cadence_epochs=None if args.cadence_epochs is None else int(args.cadence_epochs),
        trigger_price=None if args.trigger_price is None else int(args.trigger_price),
        valid_from_epoch=int(args.valid_from_epoch),
        valid_until_epoch=int(args.valid_until_epoch),
    )


def _build_authored_runtime_inputs(
    bundle: AutoTraderUserRuleBundle,
    *,
    signer_privkey: str,
) -> tuple[
    StrategyIR,
    StrategySourceArtifact,
    TauPolicyBundle,
    StrategyPolicyArtifact,
    AutoTraderClientPolicyBundle,
]:
    strategy = compile_autotrader_user_rule_bundle(bundle)
    source_artifact = build_autotrader_user_rule_source_artifact(bundle)
    compile_contract_tau_receipt = build_compile_contract_tau_policy_receipt(
        strategy=strategy
    )
    tau_policy_bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=compile_contract_tau_receipt.to_dict(),
        source_artifact=source_artifact,
    )
    policy_artifact = sign_strategy_policy_artifact(
        build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=tau_policy_bundle,
            source_artifact=source_artifact,
        ),
        privkey=signer_privkey,
    )
    client_policy_bundle = sign_autotrader_client_policy_bundle(
        build_autotrader_client_policy_bundle_from_user_rule_bundle(
            bundle,
            tau_policy_bundle=tau_policy_bundle,
            policy_artifact=policy_artifact,
        ),
        privkey=signer_privkey,
    )
    return strategy, source_artifact, tau_policy_bundle, policy_artifact, client_policy_bundle


def _load_strategy(
    *,
    policy_file: str | None,
    candidate_file: str | None,
    policy_text: str | None,
    policy_text_file: str | None,
    owner_pubkey: str | None,
) -> tuple[StrategyIR | None, str | None, str | None]:
    source_kind: str | None = None
    try:
        if policy_file:
            source_kind = "policy_file"
            return load_local_policy_file(policy_file), None, source_kind
        if candidate_file:
            source_kind = "candidate_file"
            obj = _load_json_file(candidate_file)
            if not isinstance(obj, Mapping):
                raise ValueError("candidate file must be an object")
            return compile_policy_candidate(obj, owner_pubkey=owner_pubkey).strategy, None, source_kind
        if policy_text_file:
            source_kind = "policy_text_file"
            policy_text = Path(policy_text_file).expanduser().resolve().read_text(encoding="utf-8")
        if policy_text is not None:
            source_kind = source_kind or "policy_text"
            return compile_policy_text(policy_text, owner_pubkey=owner_pubkey).compiled.strategy, None, source_kind
        raise ValueError(
            "one of --policy-file, --candidate-file, --policy-text, or --policy-text-file is required"
        )
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}", source_kind


def _intent_to_dict(intent: Intent) -> dict[str, object]:
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


def _controller_state_to_dict(state: AutoTraderControllerState) -> dict[str, object]:
    return {
        "schema": "zenodex/autotrader-controller-state/v1",
        "budget_state": {
            "window_id": int(state.budget_state.window_id),
            "spent_in_window": int(state.budget_state.spent_in_window),
            "kill_switch_on": bool(state.budget_state.kill_switch_on),
        },
        "last_action_epoch": state.last_action_epoch,
        "lifetime_spent": int(state.lifetime_spent),
        "live_orders": int(state.live_orders),
    }


def _live_report_to_dict(
    report: AutoTraderLiveReport,
    *,
    krr_bundle: AutoTraderKRRBundle | None = None,
    krr_bundle_requested: bool = False,
    krr_bundle_error: str | None = None,
    history_check_stats_requested: bool = False,
    history_check_stats_error: str | None = None,
    risk_acknowledged: bool = False,
) -> dict[str, Any]:
    return {
        "schema": "zenodex/autotrader-live-report/v1",
        "mode": "live_prepare",
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="live_prepare",
            requires_explicit_acknowledgement=True,
            user_acknowledged=risk_acknowledged,
        ),
        "krr_bundle": None if krr_bundle is None else krr_bundle.to_dict(),
        "krr_bundle_contract": {
            "ok": (None if not krr_bundle_requested else krr_bundle_error is None),
            "error": krr_bundle_error,
        },
        "history_check_stats_contract": {
            "ok": (None if not history_check_stats_requested else history_check_stats_error is None),
            "error": history_check_stats_error,
        },
        "client_policy_bundle": (
            None if report.client_policy_bundle is None else report.client_policy_bundle.to_dict()
        ),
        "client_policy_bundle_hash": (
            None
            if report.client_policy_bundle is None
            else report.client_policy_bundle.client_policy_bundle_hash_hex()
        ),
        "client_policy_surface_hash": (
            None
            if report.client_policy_bundle is None
            else report.client_policy_bundle.client_policy_surface.client_policy_surface_hash_hex()
        ),
        "client_policy_bundle_contract": {
            "ok": None if report.client_policy_bundle_ok is None else bool(report.client_policy_bundle_ok),
            "error": report.client_policy_bundle_error,
            "signature_ok": (
                None
                if report.client_policy_bundle_signature_ok is None
                else bool(report.client_policy_bundle_signature_ok)
            ),
        },
        "signing": {
            "chain_id": report.chain_id,
            "signer_pubkey": report.signer_pubkey,
            "last_used_nonce_before": int(report.last_used_nonce_before),
            "last_used_nonce_after": int(report.last_used_nonce_after),
        },
        "wallet_capability": (
            None if report.wallet_capability is None else report.wallet_capability.to_dict()
        ),
        "local_guard_evaluation": (
            None if report.local_guard_evaluation is None else report.local_guard_evaluation.to_dict()
        ),
        "policy_artifact": None if report.policy_artifact is None else report.policy_artifact.to_dict(),
        "policy_artifact_contract": {
            "ok": None if report.policy_artifact_ok is None else bool(report.policy_artifact_ok),
            "error": report.policy_artifact_error,
        },
        "tau_policy_bundle": None if report.tau_policy_bundle is None else report.tau_policy_bundle.to_dict(),
        "tau_policy_bundle_contract": {
            "ok": None if report.tau_policy_bundle_ok is None else bool(report.tau_policy_bundle_ok),
            "error": report.tau_policy_bundle_error,
        },
        "session_state": (
            None if report.session_state is None else report.session_state.to_dict()
        ),
        "external_signals": [signal.to_dict() for signal in report.external_signals],
        "signal_source_registry": (
            None if report.signal_source_registry is None else report.signal_source_registry.to_dict()
        ),
        "source_registry_ok": None if report.source_registry_ok is None else bool(report.source_registry_ok),
        "observation_packet": (
            None if report.observation_packet is None else report.observation_packet.to_dict()
        ),
        "observation_packet_error": report.observation_packet_error,
        "live_admission": {
            "ok": None if report.live_admission_ok is None else bool(report.live_admission_ok),
            "error": report.live_admission_error,
        },
        "system_compose": {
            "ok": None if report.system_compose_ok is None else bool(report.system_compose_ok),
            "error": report.system_compose_error,
        },
        "candidate_set": None if report.candidate_set is None else report.candidate_set.to_dict(),
        "candidate_set_contract": {
            "ok": None if report.candidate_set_ok is None else bool(report.candidate_set_ok),
            "error": report.candidate_set_error,
        },
        "decision_certificate": (
            None if report.decision_certificate is None else report.decision_certificate.to_dict()
        ),
        "decision_contract": {
            "ok": None if report.decision_ok is None else bool(report.decision_ok),
            "error": report.decision_error,
        },
        "bounded_multiaction_candidate_set": (
            None
            if report.bounded_multiaction_candidate_set is None
            else report.bounded_multiaction_candidate_set.to_dict()
        ),
        "bounded_multiaction_candidate_set_contract": (
            report.bounded_multiaction_candidate_set_contract
        ),
        "bounded_multiaction_decision_certificate": (
            None
            if report.bounded_multiaction_decision_certificate is None
            else report.bounded_multiaction_decision_certificate.to_dict()
        ),
        "bounded_multiaction_decision_witness": (
            None
            if report.bounded_multiaction_decision_witness is None
            else report.bounded_multiaction_decision_witness.to_dict()
        ),
        "bounded_multiaction_decision_contract": report.bounded_multiaction_decision_contract,
        "bounded_multiaction_decision_witness_contract": (
            report.bounded_multiaction_decision_witness_contract
        ),
        "bounded_multiaction_tau_argmax_contract": (
            report.bounded_multiaction_tau_argmax_contract
        ),
        "kill_switch": {
            "ok": None if report.kill_switch_ok is None else bool(report.kill_switch_ok),
            "error": report.kill_switch_error,
        },
        "submit_bundle": {
            "ok": None if report.submit_bundle_ok is None else bool(report.submit_bundle_ok),
            "error": report.submit_bundle_error,
        },
        "emit_finalize": {
            "ok": None if report.emit_finalize_ok is None else bool(report.emit_finalize_ok),
            "error": report.emit_finalize_error,
        },
        "decision": {
            "tag": report.decision.tag.value,
            "reason": report.decision.reason,
            "explain": list(report.decision.explain),
            "controller_state_after": _controller_state_to_dict(report.decision.state),
            "guard_state": {
                "signal_provenance_ok": bool(report.decision.guard_state.signal_provenance_ok),
                "route_economic_sanity_ok": bool(report.decision.guard_state.route_economic_sanity_ok),
                "execution_ok": bool(report.decision.guard_state.execution_ok),
                "oracle_freshness_ok": bool(report.decision.guard_state.oracle_freshness_ok),
                "budget_ok": bool(report.decision.guard_state.budget_ok),
            },
            "intents": [_intent_to_dict(intent) for intent in report.decision.intents],
            "tau_policy_receipt": (
                None
                if report.decision.tau_policy_receipt is None
                else {
                    "strategy_id": report.decision.tau_policy_receipt.strategy_id,
                    "strategy_hash": report.decision.tau_policy_receipt.strategy_hash,
                    "spec_id": report.decision.tau_policy_receipt.spec_id,
                    "gate_output": report.decision.tau_policy_receipt.gate_output,
                    "steps": [dict(step) for step in report.decision.tau_policy_receipt.steps],
                    "expected_ok": bool(report.decision.tau_policy_receipt.expected_ok),
                }
            ),
        },
        "session_capability_tau_receipt": (
            None
            if report.session_capability_tau_receipt is None
            else report.session_capability_tau_receipt.to_dict()
        ),
        "session_state_tau_receipt": (
            None
            if report.session_state_tau_receipt is None
            else report.session_state_tau_receipt.to_dict()
        ),
        "wallet_capability_tau_receipt": (
            None
            if report.wallet_capability_tau_receipt is None
            else report.wallet_capability_tau_receipt.to_dict()
        ),
        "external_signal_source_registry_tau_receipts": [
            {
                "spec_id": receipt.spec_id,
                "gate_output": receipt.gate_output,
                "signal_id": receipt.signal_id,
                "source_id": receipt.source_id,
                "steps": [dict(step) for step in receipt.steps],
                "expected_ok": bool(receipt.expected_ok),
            }
            for receipt in report.external_signal_source_registry_tau_receipts
        ],
        "tx_envelope_tau_receipt": (
            None
            if report.tx_envelope_tau_receipt is None
            else report.tx_envelope_tau_receipt.to_dict()
        ),
        "live_admission_tau_receipt": (
            None
            if report.live_admission_tau_receipt is None
            else report.live_admission_tau_receipt.to_dict()
        ),
        "system_compose_tau_receipt": (
            None
            if report.system_compose_tau_receipt is None
            else report.system_compose_tau_receipt.to_dict()
        ),
        "submit_bundle_tau_receipt": (
            None
            if report.submit_bundle_tau_receipt is None
            else report.submit_bundle_tau_receipt.to_dict()
        ),
        "emit_finalize_tau_receipt": (
            None
            if report.emit_finalize_tau_receipt is None
            else report.emit_finalize_tau_receipt.to_dict()
        ),
        "signed_intents": [
            {
                "intent": _intent_to_dict(env.intent),
                "signature": env.signature,
                "quote_receipt": deep_thaw_json(env.quote_receipt),
            }
            for env in report.signed_intents
        ],
        "krr_advice": report.krr_advice,
        "krr_advice_error": report.krr_advice_error,
        "krr_explanation": report.krr_explanation,
        "user_rule_summary": report.user_rule_summary,
        "actionability_explanation": report.actionability_explanation,
        "actionability_summary": report.actionability_summary,
        "nonce_tau_receipts": [
            {
                "spec_id": receipt.spec_id,
                "gate_output": receipt.gate_output,
                "intent_id": receipt.intent_id,
                "intent_nonce": int(receipt.intent_nonce),
                "last_used_nonce": int(receipt.last_used_nonce),
                "expected_nonce": int(receipt.expected_nonce),
                "steps": [dict(step) for step in receipt.steps],
                "expected_ok": bool(receipt.expected_ok),
            }
            for receipt in report.nonce_tau_receipts
        ],
        "operations": dict(report.operations),
        "tau_tx_payload": report.tau_tx_payload,
        "stage_certificate": (
            None if report.stage_certificate is None else report.stage_certificate.to_dict()
        ),
        "stage_certificate_error": report.stage_certificate_error,
        "live_release_certificate": (
            None
            if report.live_release_certificate is None
            else report.live_release_certificate.to_dict()
        ),
        "live_release_certificate_error": report.live_release_certificate_error,
    }


def _emit_json(data: dict[str, Any], *, pretty: bool) -> None:
    text = json.dumps(data, indent=2 if pretty else None, sort_keys=True)
    print(text)


def _string_list(value: object) -> list[str]:
    if not isinstance(value, list):
        return []
    return [str(item) for item in value if isinstance(item, str) and item.strip()]


def _build_text_summary_lines(data: Mapping[str, Any]) -> list[str]:
    lines: list[str] = []

    decision = data.get("decision")
    if isinstance(decision, Mapping):
        tag = decision.get("tag")
        if isinstance(tag, str) and tag.strip():
            lines.append(f"Decision: {tag}")

    actionability_summary = data.get("actionability_summary")
    if isinstance(actionability_summary, Mapping):
        headline = actionability_summary.get("headline")
        if isinstance(headline, str) and headline.strip():
            lines.append(f"Actionability: {headline}")
        preset_summary = actionability_summary.get("preset_summary")
        if isinstance(preset_summary, str) and preset_summary.strip():
            lines.append(f"Preset: {preset_summary}")
        blocking_summary = actionability_summary.get("blocking_summary")
        if isinstance(blocking_summary, str) and blocking_summary.strip():
            lines.append(f"Blocking: {blocking_summary}")
        trust_summary = actionability_summary.get("trust_summary")
        if isinstance(trust_summary, str) and trust_summary.strip():
            lines.append(f"Trust: {trust_summary}")
        confidence_summary = actionability_summary.get("confidence_summary")
        if isinstance(confidence_summary, str) and confidence_summary.strip():
            lines.append(f"Confidence: {confidence_summary}")

    user_rule_summary = data.get("user_rule_summary")
    if isinstance(user_rule_summary, Mapping):
        intent = user_rule_summary.get("intent")
        if isinstance(intent, Mapping):
            template = intent.get("template")
            asset_pair = intent.get("asset_pair")
            allowed_actions = ", ".join(_string_list(intent.get("allowed_actions")))
            if isinstance(template, str) and template.strip() and isinstance(asset_pair, str) and asset_pair.strip():
                line = f"Intent: {template} on {asset_pair}"
                if allowed_actions:
                    line += f" via {allowed_actions}"
                line += "."
                lines.append(line)
        sizing = user_rule_summary.get("sizing")
        if isinstance(sizing, Mapping):
            fixed_order_size = sizing.get("fixed_order_size")
            cadence_epochs = sizing.get("cadence_epochs")
            per_order_max = sizing.get("per_order_max")
            if fixed_order_size is not None and per_order_max is not None:
                parts = [f"fixed_order_size={fixed_order_size}"]
                if cadence_epochs is not None:
                    parts.append(f"cadence_epochs={cadence_epochs}")
                parts.append(f"per_order_max={per_order_max}")
                lines.append("Sizing: " + ", ".join(parts) + ".")
        trigger = user_rule_summary.get("trigger")
        if isinstance(trigger, Mapping):
            trigger_price = trigger.get("trigger_price")
            if trigger_price is not None:
                lines.append(f"Trigger: trigger_price={trigger_price}.")
        surface_support_matrix = user_rule_summary.get("surface_support_matrix")
        if isinstance(surface_support_matrix, Mapping):
            support_parts: list[str] = []
            for surface_name in ("compile", "shadow", "live"):
                surface_raw = surface_support_matrix.get(surface_name)
                if not isinstance(surface_raw, Mapping):
                    continue
                status = surface_raw.get("status")
                if not isinstance(status, str) or not status.strip():
                    continue
                detail = f"{surface_name}={status}"
                reject_reason = surface_raw.get("reject_reason_when_unsupported")
                if status != "supported" and isinstance(reject_reason, str) and reject_reason.strip():
                    detail += f"({reject_reason})"
                support_parts.append(detail)
            overall_status = user_rule_summary.get("overall_support_status")
            if support_parts:
                line = "Support: "
                if isinstance(overall_status, str) and overall_status.strip():
                    line += f"tier={overall_status}; "
                line += ", ".join(support_parts) + "."
                lines.append(line)

    risk_disclosure = data.get("risk_disclosure")
    if isinstance(risk_disclosure, Mapping):
        acknowledged = bool(risk_disclosure.get("user_acknowledged", False))
        lines.append(
            "Risk acknowledgement: "
            + ("acknowledged." if acknowledged else "missing.")
        )

    return lines


def _emit_text_summary(data: dict[str, Any]) -> None:
    print("\n".join(_build_text_summary_lines(data)))


def _build_preflight_reject_payload(
    *,
    reason: str,
    explain: tuple[str, ...],
    signer_privkey: str | int | bytes | bytearray,
    last_used_nonce: int,
    chain_id: str,
    risk_acknowledged: bool,
    contract_key: str,
    source_kind: str | None,
    load_error: str,
) -> dict[str, Any]:
    report = AutoTraderLiveReport(
        decision=AutoTraderDecision(
            tag=AutoTraderDecisionTag.REJECT,
            reason=reason,
            explain=explain,
            state=AutoTraderControllerState(),
        ),
        signer_pubkey="0x" + bls_pubkey_hex_from_privkey(signer_privkey),
        chain_id=str(chain_id),
        last_used_nonce_before=int(last_used_nonce),
        last_used_nonce_after=int(last_used_nonce),
        live_admission_ok=False,
        live_admission_error=reason,
    )
    payload = _live_report_to_dict(
        report,
        risk_acknowledged=risk_acknowledged,
    )
    source_label = str(source_kind or "unknown")
    payload[contract_key] = {
        "ok": False,
        "error": reason,
        "source_kind": source_label,
        "load_error": load_error,
    }
    payload["actionability_summary"] = {
        "headline": f"Rejected before live preparation because {reason}.",
        "preset_summary": None,
        "blocking_summary": f"Preflight {source_label.replace('_', ' ')} validation failed.",
        "trust_summary": None,
        "confidence_summary": None,
    }
    return payload


def _build_preset_catalog_payload(
    *,
    live_supported_only: bool,
    fail_closed_only: bool,
) -> dict[str, Any]:
    presets = list_autotrader_user_rule_presets(
        live_supported_only=live_supported_only,
        fail_closed_only=fail_closed_only,
    )
    return {
        "ok": True,
        "schema": "zenodex/autotrader-user-rule-preset-catalog/v1",
        "preset_count": len(presets),
        "filters": {
            "live_supported_only": live_supported_only,
            "fail_closed_only": fail_closed_only,
        },
        "presets": list(presets),
    }


def _build_preset_description_payload(preset_id: str) -> dict[str, Any]:
    preset = describe_autotrader_user_rule_preset(preset_id)
    if preset is None:
        raise ValueError(f"unknown preset: {preset_id}")
    return {
        "ok": True,
        "schema": "zenodex/autotrader-user-rule-preset-description/v1",
        "preset": preset,
    }


def _build_preset_comparison_payload(left_preset_id: str, right_preset_id: str) -> dict[str, Any]:
    comparison = compare_autotrader_user_rule_presets(left_preset_id, right_preset_id)
    return {
        "ok": True,
        "schema": "zenodex/autotrader-user-rule-preset-comparison/v1",
        **comparison,
    }


def _build_preset_recommendation_payload(
    *,
    desired_user_rule_mode: str | None,
    desired_optimize_for: str | None,
    desired_max_slippage_bps: int | None,
    desired_max_oracle_staleness_epochs: int | None,
    desired_max_live_orders: int | None,
    require_live_supported: bool,
) -> dict[str, Any]:
    recommendation = recommend_autotrader_user_rule_preset(
        desired_user_rule_mode=desired_user_rule_mode,
        desired_optimize_for=desired_optimize_for,
        desired_max_slippage_bps=desired_max_slippage_bps,
        desired_max_oracle_staleness_epochs=desired_max_oracle_staleness_epochs,
        desired_max_live_orders=desired_max_live_orders,
        require_live_supported=require_live_supported,
    )
    return {
        "ok": True,
        "schema": "zenodex/autotrader-user-rule-preset-recommendation/v1",
        **recommendation,
    }


def _emit_preset_catalog_text(data: Mapping[str, Any]) -> None:
    presets = data.get("presets")
    lines = ["Available autotrader user-rule presets:"]
    if isinstance(presets, list):
        for preset in presets:
            if not isinstance(preset, Mapping):
                continue
            preset_id = preset.get("preset_id")
            label = preset.get("label")
            optimize_for = preset.get("optimize_for")
            summary = preset.get("summary")
            mode = preset.get("mode")
            live_posture = preset.get("live_execution_posture")
            live_text = None
            support_tier = preset.get("overall_support_status")
            support_matrix = preset.get("surface_support_matrix")
            support_text = None
            if isinstance(live_posture, Mapping):
                supported = live_posture.get("supported")
                if isinstance(supported, bool):
                    live_text = "live=supported" if supported else "live=fail_closed"
            if isinstance(support_matrix, Mapping):
                support_parts: list[str] = []
                for surface_name in ("compile", "shadow", "live"):
                    surface_raw = support_matrix.get(surface_name)
                    if not isinstance(surface_raw, Mapping):
                        continue
                    status = surface_raw.get("status")
                    if isinstance(status, str) and status.strip():
                        support_parts.append(f"{surface_name}={status}")
                if support_parts:
                    support_text = "; ".join(support_parts)
            if isinstance(preset_id, str) and isinstance(label, str) and isinstance(optimize_for, str):
                parts = [f"- {preset_id}: {label}"]
                if isinstance(mode, str):
                    parts.append(f"mode={mode}")
                parts.append(f"optimize_for={optimize_for}")
                if live_text is not None:
                    parts.append(live_text)
                if isinstance(support_tier, str) and support_tier.strip():
                    parts.append(f"tier={support_tier}")
                if isinstance(support_text, str) and support_text.strip():
                    parts.append(support_text)
                lines.append(" | ".join(parts))
            if isinstance(summary, str) and summary.strip():
                lines.append(f"  {summary}")
    print("\n".join(lines))


def _emit_preset_description_text(data: Mapping[str, Any]) -> None:
    preset = data.get("preset")
    if not isinstance(preset, Mapping):
        return
    lines: list[str] = []
    preset_id = preset.get("preset_id")
    label = preset.get("label")
    optimize_for = preset.get("optimize_for")
    summary = preset.get("summary")
    tradeoffs = preset.get("tradeoffs")
    mode = preset.get("mode")
    if isinstance(preset_id, str) and isinstance(label, str) and isinstance(optimize_for, str):
        lines.append(f"Preset: {preset_id} ({label})")
        if isinstance(mode, str):
            lines.append(f"Mode: {mode}")
        lines.append(f"Optimize for: {optimize_for}")
    if isinstance(summary, str) and summary.strip():
        lines.append(f"Summary: {summary}")
    if isinstance(tradeoffs, str) and tradeoffs.strip():
        lines.append(f"Tradeoffs: {tradeoffs}")
    authoring_requirements = preset.get("authoring_requirements")
    if isinstance(authoring_requirements, Mapping):
        common = authoring_requirements.get("required_common_parameters")
        if isinstance(common, list):
            common_params = [str(value) for value in common if isinstance(value, str)]
            if common_params:
                lines.append("Required parameters: " + ", ".join(common_params))
        mode_specific: list[str] = []
        if authoring_requirements.get("requires_cadence_epochs") is True:
            mode_specific.append("cadence_epochs")
        if authoring_requirements.get("requires_trigger_price") is True:
            mode_specific.append("trigger_price")
        if mode_specific:
            lines.append("Mode-specific parameters: " + ", ".join(mode_specific))
    support_tier = preset.get("overall_support_status")
    if isinstance(support_tier, str) and support_tier.strip():
        lines.append(f"Support tier: {support_tier}.")
    support_matrix = preset.get("surface_support_matrix")
    if isinstance(support_matrix, Mapping):
        support_parts: list[str] = []
        for surface_name in ("compile", "shadow", "live"):
            surface_raw = support_matrix.get(surface_name)
            if not isinstance(surface_raw, Mapping):
                continue
            status = surface_raw.get("status")
            if not isinstance(status, str) or not status.strip():
                continue
            detail = f"{surface_name}={status}"
            reject_reason = surface_raw.get("reject_reason_when_unsupported")
            if status != "supported" and isinstance(reject_reason, str) and reject_reason.strip():
                detail += f"({reject_reason})"
            support_parts.append(detail)
        if support_parts:
            lines.append("Surface support: " + ", ".join(support_parts) + ".")
    live_posture = preset.get("live_execution_posture")
    if isinstance(live_posture, Mapping):
        supported = live_posture.get("supported")
        reject_reason = live_posture.get("reject_reason_when_unsupported")
        if supported is True:
            lines.append("Live execution: supported by current executor.")
        elif supported is False:
            if isinstance(reject_reason, str) and reject_reason:
                lines.append(f"Live execution: fail-closed via {reject_reason}.")
            else:
                lines.append("Live execution: fail-closed by current executor.")
    operating_profile = preset.get("operating_profile")
    if isinstance(operating_profile, Mapping):
        lines.append(
            "Operating profile: "
            + ", ".join(
                f"{key}={value}" for key, value in operating_profile.items() if isinstance(value, str)
            )
        )
    guard_profile = preset.get("guard_profile")
    if isinstance(guard_profile, Mapping):
        lines.append(
            "Guard profile: "
            + ", ".join(f"{key}={value}" for key, value in guard_profile.items())
        )
    print("\n".join(lines))


def _emit_preset_comparison_text(data: Mapping[str, Any]) -> None:
    left = data.get("left")
    right = data.get("right")
    if not isinstance(left, Mapping) or not isinstance(right, Mapping):
        return
    left_id = left.get("preset_id")
    right_id = right.get("preset_id")
    left_label = left.get("label")
    right_label = right.get("label")
    lines: list[str] = []
    if isinstance(left_id, str) and isinstance(right_id, str):
        lines.append(f"Comparing presets: {left_id} -> {right_id}")
    if isinstance(left_label, str) and isinstance(right_label, str):
        lines.append(f"Labels: {left_label} -> {right_label}")
    for section_name, key in (
        ("Top-level deltas", "top_level_deltas"),
        ("Operating profile deltas", "operating_profile_deltas"),
        ("Guard profile deltas", "guard_profile_deltas"),
    ):
        section = data.get(key)
        if not isinstance(section, Mapping) or not section:
            continue
        lines.append(f"{section_name}:")
        for field_name, values in section.items():
            if not isinstance(values, Mapping):
                continue
            lines.append(
                f"- {field_name}: {values.get('left')} -> {values.get('right')}"
            )
    print("\n".join(lines))


def _emit_preset_recommendation_text(data: Mapping[str, Any]) -> None:
    recommended = data.get("recommended_preset")
    criteria = data.get("criteria")
    ranked_candidates = data.get("ranked_candidates")
    if not isinstance(recommended, Mapping):
        return
    lines: list[str] = []
    preset_id = recommended.get("preset_id")
    label = recommended.get("label")
    optimize_for = recommended.get("optimize_for")
    if isinstance(preset_id, str) and isinstance(label, str):
        lines.append(f"Recommended preset: {preset_id} ({label})")
    mode = recommended.get("mode")
    if isinstance(mode, str):
        lines.append(f"Mode: {mode}")
    if isinstance(optimize_for, str):
        lines.append(f"Optimize for: {optimize_for}")
    if isinstance(criteria, Mapping):
        criteria_text = ", ".join(
            f"{key}={value}"
            for key, value in criteria.items()
            if value is not None and (not isinstance(value, bool) or value)
        )
        if criteria_text:
            lines.append(f"Criteria: {criteria_text}")
    if isinstance(ranked_candidates, list) and ranked_candidates:
        lines.append("Top candidates:")
        for candidate in ranked_candidates[:3]:
            if not isinstance(candidate, Mapping):
                continue
            lines.append(
                f"- {candidate.get('preset_id')}: penalty={candidate.get('total_penalty')}"
            )
    print("\n".join(lines))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "Advanced experimental automation surface. "
            "Do not use unless you understand and accept that you can lose everything."
        ),
    )
    source = parser.add_mutually_exclusive_group(required=False)
    source.add_argument("--policy-file")
    source.add_argument("--candidate-file")
    source.add_argument("--policy-text")
    source.add_argument("--policy-text-file")
    source.add_argument("--user-rule-bundle-file")
    source.add_argument(
        "--user-rule-preset",
        choices=tuple(preset.value for preset in AutoTraderUserRulePreset),
    )
    source.add_argument(
        "--user-rule-mode",
        choices=tuple(mode.value for mode in AutoTraderUserRuleMode),
    )
    parser.add_argument("--owner-pubkey")
    parser.add_argument(
        "--user-rule-policy-backend",
        choices=tuple(backend.value for backend in PolicyBackend),
        default=PolicyBackend.LOCAL.value,
    )
    parser.add_argument("--user-rule-bundle-name")
    parser.add_argument("--user-rule-strategy-id")
    parser.add_argument("--user-rule-built-at")
    parser.add_argument("--asset-in")
    parser.add_argument("--asset-out")
    parser.add_argument("--fixed-order-size", type=int)
    parser.add_argument("--cadence-epochs", type=int)
    parser.add_argument("--trigger-price", type=int)
    parser.add_argument("--per-window-max", type=int)
    parser.add_argument("--lifetime-max", type=int)
    parser.add_argument("--max-slippage-bps", type=int)
    parser.add_argument("--max-oracle-staleness-epochs", type=int)
    parser.add_argument("--min-order-spacing-epochs", type=int)
    parser.add_argument("--max-live-orders", type=int)
    parser.add_argument("--valid-from-epoch", type=int)
    parser.add_argument("--valid-until-epoch", type=int)
    parser.add_argument("--receipt-file")
    parser.add_argument("--pools-file")
    parser.add_argument("--controller-state-file")
    parser.add_argument("--wallet-capability-file")
    parser.add_argument("--session-state-file")
    parser.add_argument("--policy-artifact-file")
    parser.add_argument("--tau-policy-bundle-file")
    parser.add_argument("--client-policy-bundle-file")
    parser.add_argument("--external-signals-file")
    parser.add_argument("--signal-source-registry-file")
    parser.add_argument("--history-check-stats-file", help="Optional KRR history-check-stats JSON")
    parser.add_argument("--krr-bundle-file", help="Optional reviewed signed offline KRR bundle JSON")
    parser.add_argument("--current-epoch", type=int)
    parser.add_argument("--intent-deadline", type=int)
    parser.add_argument("--last-used-nonce", type=int)
    parser.add_argument("--signer-privkey")
    parser.add_argument("--chain-id", default="tau-net-alpha")
    parser.add_argument("--slippage-bps", type=int)
    parser.add_argument("--tau-enabled", action="store_true")
    parser.add_argument("--tau-bin")
    parser.add_argument("--tau-timeout-s", type=float, default=2.0)
    parser.add_argument("--tau-allow-path-lookup", action="store_true")
    parser.add_argument(
        "--krr-backend",
        choices=("off", "python", "auto", "prolog", "souffle"),
        default="python",
        help="Advisory KRR backend. Does not affect execution semantics.",
    )
    parser.add_argument("--krr-kb", help="Path to KRR knowledge base JSON")
    parser.add_argument("--tx-sequence-number", type=int)
    parser.add_argument("--tx-expiration-time", type=int)
    parser.add_argument("--tx-fee-limit", default="0")
    parser.add_argument("--telemetry-out")
    parser.add_argument("--list-user-rule-presets", action="store_true")
    parser.add_argument("--only-live-supported-presets", action="store_true")
    parser.add_argument("--only-fail-closed-presets", action="store_true")
    parser.add_argument(
        "--describe-user-rule-preset",
        choices=tuple(preset.value for preset in AutoTraderUserRulePreset),
    )
    parser.add_argument(
        "--compare-user-rule-presets",
        nargs=2,
        metavar=("LEFT_PRESET", "RIGHT_PRESET"),
        choices=tuple(preset.value for preset in AutoTraderUserRulePreset),
    )
    parser.add_argument("--recommend-user-rule-preset", action="store_true")
    parser.add_argument(
        "--desired-user-rule-mode",
        choices=tuple(mode.value for mode in AutoTraderUserRuleMode),
    )
    parser.add_argument(
        "--desired-optimize-for",
        choices=(
            "capital_preservation",
            "execution_safety",
            "balanced_execution",
            "price_discipline",
            "throughput",
            "downside_protection",
            "profit_realization",
        ),
    )
    parser.add_argument("--desired-max-slippage-bps", type=int)
    parser.add_argument("--desired-max-oracle-staleness-epochs", type=int)
    parser.add_argument("--desired-max-live-orders", type=int)
    parser.add_argument("--require-live-supported", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument(
        "--text-summary",
        action="store_true",
        help="Emit a deterministic human-readable summary instead of JSON on stdout.",
    )
    parser.add_argument(
        _LIVE_RISK_ACK_FLAG,
        action="store_true",
        help=(
            "Required for live-preparation runs. Confirms that this advanced experimental "
            "automation surface is used at your own risk."
        ),
    )
    args = parser.parse_args(argv)

    try:
        if bool(args.only_live_supported_presets) and bool(args.only_fail_closed_presets):
            raise ValueError("--only-live-supported-presets and --only-fail-closed-presets are mutually exclusive")
        readonly_modes = (
            int(bool(args.list_user_rule_presets))
            + int(args.describe_user_rule_preset is not None)
            + int(args.compare_user_rule_presets is not None)
            + int(bool(args.recommend_user_rule_preset))
        )
        if readonly_modes > 1:
            raise ValueError(
                "--list-user-rule-presets, --describe-user-rule-preset, --compare-user-rule-presets, and --recommend-user-rule-preset are mutually exclusive"
            )
        if bool(args.list_user_rule_presets):
            payload = _build_preset_catalog_payload(
                live_supported_only=bool(args.only_live_supported_presets),
                fail_closed_only=bool(args.only_fail_closed_presets),
            )
            if args.text_summary:
                _emit_preset_catalog_text(payload)
            else:
                _emit_json(payload, pretty=bool(args.pretty))
            return 0
        if args.describe_user_rule_preset is not None:
            payload = _build_preset_description_payload(str(args.describe_user_rule_preset))
            if args.text_summary:
                _emit_preset_description_text(payload)
            else:
                _emit_json(payload, pretty=bool(args.pretty))
            return 0
        if args.compare_user_rule_presets is not None:
            left_preset_id, right_preset_id = args.compare_user_rule_presets
            payload = _build_preset_comparison_payload(str(left_preset_id), str(right_preset_id))
            if args.text_summary:
                _emit_preset_comparison_text(payload)
            else:
                _emit_json(payload, pretty=bool(args.pretty))
            return 0
        if bool(args.recommend_user_rule_preset):
            payload = _build_preset_recommendation_payload(
                desired_user_rule_mode=args.desired_user_rule_mode,
                desired_optimize_for=args.desired_optimize_for,
                desired_max_slippage_bps=args.desired_max_slippage_bps,
                desired_max_oracle_staleness_epochs=args.desired_max_oracle_staleness_epochs,
                desired_max_live_orders=args.desired_max_live_orders,
                require_live_supported=bool(args.require_live_supported),
            )
            if args.text_summary:
                _emit_preset_recommendation_text(payload)
            else:
                _emit_json(payload, pretty=bool(args.pretty))
            return 0
        if not bool(args.acknowledge_experimental_live_risk):
            raise ValueError(_LIVE_RISK_ACK_ERROR)
        if not any(
            value is not None
            for value in (
                args.policy_file,
                args.candidate_file,
                args.policy_text,
                args.policy_text_file,
                args.user_rule_bundle_file,
                args.user_rule_preset,
                args.user_rule_mode,
            )
        ):
            raise ValueError("one policy source is required")
        missing_live_args = [
            name
            for name, value in (
                ("receipt-file", args.receipt_file),
                ("pools-file", args.pools_file),
                ("current-epoch", args.current_epoch),
                ("intent-deadline", args.intent_deadline),
                ("last-used-nonce", args.last_used_nonce),
                ("signer-privkey", args.signer_privkey),
            )
            if value is None
        ]
        if missing_live_args:
            raise ValueError(
                "missing required live-preparation arguments: " + ", ".join(missing_live_args)
            )
        authored_rule_source = bool(args.user_rule_bundle_file or args.user_rule_preset or args.user_rule_mode)
        strategy: StrategyIR
        policy_artifact: StrategyPolicyArtifact | None
        tau_policy_bundle: TauPolicyBundle | None
        client_policy_bundle: AutoTraderClientPolicyBundle | None
        if authored_rule_source:
            if any(
                value is not None
                for value in (
                    args.policy_artifact_file,
                    args.tau_policy_bundle_file,
                    args.client_policy_bundle_file,
                )
            ):
                raise ValueError(
                    "authored user-rule inputs auto-build policy artifacts; do not also pass "
                    "--policy-artifact-file, --tau-policy-bundle-file, or --client-policy-bundle-file"
                )
            authored_owner_pubkey = _resolve_authored_owner_pubkey(
                owner_pubkey=args.owner_pubkey,
                signer_privkey=args.signer_privkey,
            )
            if args.user_rule_bundle_file:
                authored_bundle, authored_bundle_load_error = _load_user_rule_bundle_file(
                    args.user_rule_bundle_file
                )
                if authored_bundle_load_error is not None or authored_bundle is None:
                    payload = _build_preflight_reject_payload(
                        reason="user_rule_bundle_load_rejected",
                        explain=(
                            "source_kind=user_rule_bundle_file",
                            f"load_error={authored_bundle_load_error}",
                        ),
                        signer_privkey=args.signer_privkey,
                        last_used_nonce=int(args.last_used_nonce),
                        chain_id=str(args.chain_id),
                        risk_acknowledged=bool(args.acknowledge_experimental_live_risk),
                        contract_key="user_rule_bundle_contract",
                        source_kind="user_rule_bundle_file",
                        load_error=str(authored_bundle_load_error),
                    )
                    if args.telemetry_out:
                        Path(args.telemetry_out).write_text(
                            json.dumps(payload, indent=2, sort_keys=True),
                            encoding="utf-8",
                        )
                    if args.text_summary:
                        _emit_text_summary(payload)
                    else:
                        _emit_json(payload, pretty=bool(args.pretty))
                    return 0
                if authored_bundle.owner_pubkey != authored_owner_pubkey:
                    payload = _build_preflight_reject_payload(
                        reason="user_rule_bundle_load_rejected",
                        explain=(
                            "source_kind=user_rule_bundle_file",
                            "load_error=ValueError: user rule bundle owner_pubkey must match signer pubkey",
                        ),
                        signer_privkey=args.signer_privkey,
                        last_used_nonce=int(args.last_used_nonce),
                        chain_id=str(args.chain_id),
                        risk_acknowledged=bool(args.acknowledge_experimental_live_risk),
                        contract_key="user_rule_bundle_contract",
                        source_kind="user_rule_bundle_file",
                        load_error="ValueError: user rule bundle owner_pubkey must match signer pubkey",
                    )
                    if args.telemetry_out:
                        Path(args.telemetry_out).write_text(
                            json.dumps(payload, indent=2, sort_keys=True),
                            encoding="utf-8",
                        )
                    if args.text_summary:
                        _emit_text_summary(payload)
                    else:
                        _emit_json(payload, pretty=bool(args.pretty))
                    return 0
            elif args.user_rule_preset:
                authored_bundle = _build_user_rule_bundle_from_preset_args(
                    args,
                    owner_pubkey=authored_owner_pubkey,
                )
            else:
                authored_bundle = _build_user_rule_bundle_from_mode_args(
                    args,
                    owner_pubkey=authored_owner_pubkey,
                )
            strategy, _authored_source_artifact, tau_policy_bundle, policy_artifact, client_policy_bundle = (
                _build_authored_runtime_inputs(
                    authored_bundle,
                    signer_privkey=args.signer_privkey,
                )
            )
            policy_artifact_load_error = None
            tau_policy_bundle_load_error = None
            client_policy_bundle_load_error = None
        else:
            loaded_strategy, strategy_load_error, strategy_source_kind = _load_strategy(
                policy_file=args.policy_file,
                candidate_file=args.candidate_file,
                policy_text=args.policy_text,
                policy_text_file=args.policy_text_file,
                owner_pubkey=args.owner_pubkey,
            )
            if strategy_load_error is not None or loaded_strategy is None:
                payload = _build_preflight_reject_payload(
                    reason="strategy_source_load_rejected",
                    explain=(
                        f"source_kind={strategy_source_kind or 'unknown'}",
                        f"load_error={strategy_load_error}",
                    ),
                    signer_privkey=args.signer_privkey,
                    last_used_nonce=int(args.last_used_nonce),
                    chain_id=str(args.chain_id),
                    risk_acknowledged=bool(args.acknowledge_experimental_live_risk),
                    contract_key="strategy_source_contract",
                    source_kind=strategy_source_kind,
                    load_error=str(strategy_load_error),
                )
                if args.telemetry_out:
                    Path(args.telemetry_out).write_text(
                        json.dumps(payload, indent=2, sort_keys=True),
                        encoding="utf-8",
                    )
                if args.text_summary:
                    _emit_text_summary(payload)
                else:
                    _emit_json(payload, pretty=bool(args.pretty))
                return 0
            strategy = loaded_strategy
            policy_artifact, policy_artifact_load_error = _load_policy_artifact_file(
                args.policy_artifact_file
            )
            tau_policy_bundle, tau_policy_bundle_load_error = _load_tau_policy_bundle_file(
                args.tau_policy_bundle_file
            )
            client_policy_bundle, client_policy_bundle_load_error = _load_client_policy_bundle_file(
                args.client_policy_bundle_file
            )
        receipt, receipt_load_error = _load_receipt_file(args.receipt_file)
        pools_by_id, pools_load_error = _load_pools_file(args.pools_file)
        controller_state, controller_state_load_error = _load_controller_state_file(
            args.controller_state_file
        )
        wallet_capability, wallet_capability_load_error = _load_wallet_capability_file(
            args.wallet_capability_file
        )
        session_state, session_state_load_error = _load_session_state_file(
            args.session_state_file
        )
        krr_bundle, krr_bundle_load_error = _load_krr_bundle_file(args.krr_bundle_file)
        if args.krr_bundle_file is not None and any(
            value is not None
            for value in (
                args.external_signals_file,
                args.signal_source_registry_file,
                args.history_check_stats_file,
                args.krr_kb,
            )
        ):
            raise ValueError(
                "--krr-bundle-file cannot be combined with raw KRR KB, signal, registry, or history inputs"
            )
        if krr_bundle is not None:
            bundle_krr_kb, external_signals, signal_source_registry, history_check_stats = (
                bundle_runtime_artifacts(krr_bundle)
            )
            external_signals_load_error = None
            signal_source_registry_load_error = None
            history_check_stats_load_error = None
        elif krr_bundle_load_error is not None:
            bundle_krr_kb = None
            external_signals = ()
            signal_source_registry = None
            external_signals_load_error = None
            signal_source_registry_load_error = None
            history_check_stats = None
            history_check_stats_load_error = None
        else:
            bundle_krr_kb = None
            external_signals, external_signals_load_error = _load_external_signals_file(
                args.external_signals_file
            )
            signal_source_registry, signal_source_registry_load_error = _load_signal_source_registry_file(
                args.signal_source_registry_file
            )
            history_check_stats = None
            history_check_stats_load_error = None
            if args.history_check_stats_file:
                try:
                    history_obj = _load_json_file(args.history_check_stats_file)
                    if not isinstance(history_obj, Mapping):
                        raise ValueError("history-check-stats file must be an object")
                    history_check_stats = history_obj
                except Exception as exc:
                    history_check_stats = None
                    history_check_stats_load_error = f"{type(exc).__name__}: {exc}"
        tau_config = AutoTraderTauConfig(
            enabled=bool(args.tau_enabled),
            timeout_s=float(args.tau_timeout_s),
            tau_bin=(args.tau_bin or None),
            allow_path_lookup=bool(args.tau_allow_path_lookup),
        )
        report = prepare_autotrader_live_quote_receipt(
            strategy=strategy,
            controller_state=controller_state,
            controller_state_load_error=controller_state_load_error,
            receipt=({} if receipt is None else receipt),
            receipt_load_error=receipt_load_error,
            pools_by_id=({} if pools_by_id is None else pools_by_id),
            pools_load_error=pools_load_error,
            current_epoch=int(args.current_epoch),
            intent_deadline=int(args.intent_deadline),
            signer_privkey=args.signer_privkey,
            last_used_nonce=int(args.last_used_nonce),
            chain_id=str(args.chain_id),
            wallet_capability=wallet_capability,
            wallet_capability_load_error=wallet_capability_load_error,
            session_state=session_state,
            session_state_load_error=session_state_load_error,
            policy_artifact=policy_artifact,
            policy_artifact_load_error=policy_artifact_load_error,
            tau_policy_bundle=tau_policy_bundle,
            tau_policy_bundle_load_error=tau_policy_bundle_load_error,
            client_policy_bundle=client_policy_bundle,
            client_policy_bundle_load_error=client_policy_bundle_load_error,
            external_signals=external_signals,
            signal_source_registry=signal_source_registry,
            external_signals_load_error=external_signals_load_error,
            signal_source_registry_load_error=signal_source_registry_load_error,
            slippage_bps=args.slippage_bps,
            tau_config=tau_config,
            krr_backend=("off" if krr_bundle_load_error is not None else str(args.krr_backend)),
            krr_kb_path=args.krr_kb,
            krr_kb=bundle_krr_kb,
            history_check_stats=history_check_stats,
            tx_sequence_number=args.tx_sequence_number,
            tx_expiration_time=args.tx_expiration_time,
            tx_fee_limit=args.tx_fee_limit,
        )
        payload = _live_report_to_dict(
            report,
            krr_bundle=krr_bundle,
            krr_bundle_requested=bool(args.krr_bundle_file),
            krr_bundle_error=krr_bundle_load_error,
            history_check_stats_requested=bool(args.history_check_stats_file),
            history_check_stats_error=history_check_stats_load_error,
            risk_acknowledged=bool(args.acknowledge_experimental_live_risk),
        )
        if args.telemetry_out:
            Path(args.telemetry_out).write_text(
                json.dumps(payload, indent=2, sort_keys=True),
                encoding="utf-8",
            )
        if args.text_summary:
            _emit_text_summary(payload)
        else:
            _emit_json(payload, pretty=bool(args.pretty))
        return 0
    except Exception as exc:
        payload = {
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="live_prepare",
                requires_explicit_acknowledgement=True,
                user_acknowledged=bool(getattr(args, "acknowledge_experimental_live_risk", False)),
            ),
        }
        if args.telemetry_out:
            Path(args.telemetry_out).write_text(
                json.dumps(payload, indent=2, sort_keys=True),
                encoding="utf-8",
            )
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
