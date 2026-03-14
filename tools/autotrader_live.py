#!/usr/bin/env python3
"""Live-preparation CLI for the policy-constrained auto-trader."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import (  # noqa: E402
    AutoTraderKRRBundle,
    bundle_runtime_artifacts,
    load_autotrader_krr_bundle_file,
)
from src.agents.local_policy import load_local_policy_file  # noqa: E402
from src.agents.policy_artifacts import (  # noqa: E402
    strategy_policy_artifact_from_dict,
    tau_policy_bundle_from_dict,
)
from src.agents.policy_compiler import compile_policy_candidate  # noqa: E402
from src.agents.policy_text_compiler import compile_policy_text  # noqa: E402
from src.agents.strategy_ir import StrategyAction, StrategyIR  # noqa: E402
from src.integration.autotrader_controller import (  # noqa: E402
    AutoTraderControllerState,
    AutoTraderTauConfig,
)
from src.integration.autotrader_live import (  # noqa: E402
    AutoTraderLiveReport,
    prepare_autotrader_live_quote_receipt,
)
from src.integration.autotrader_signal_registry import (  # noqa: E402
    ExternalSignalSourceRegistry,
    external_signal_source_registry_from_object,
)
from src.integration.autotrader_signals import (  # noqa: E402
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    external_signal_observations_from_object,
)
from src.kernels.python.strategy_budget_guard_v1_adapter import (  # noqa: E402
    StrategyBudgetState,
)
from src.state.intents import Intent  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


def _load_json_file(path: str | Path) -> Any:
    p = Path(path).expanduser().resolve()
    return json.loads(p.read_text(encoding="utf-8"))


def _require_intish(value: object, *, name: str) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must not be a bool")
    if isinstance(value, (int, str)):
        return int(value)
    raise ValueError(f"{name} must be int-like")


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


def _load_pools_file(path: str | Path) -> dict[str, PoolState]:
    obj = _load_json_file(path)
    if isinstance(obj, dict):
        if "pools" in obj:
            obj = obj["pools"]
        if isinstance(obj, Mapping) and all(isinstance(v, Mapping) for v in obj.values()):
            return {str(key): _pool_state_from_dict(value) for key, value in obj.items()}
    if isinstance(obj, list):
        pools: dict[str, PoolState] = {}
        for row in obj:
            if not isinstance(row, Mapping):
                raise ValueError("pool list entries must be objects")
            pool = _pool_state_from_dict(row)
            pools[pool.pool_id] = pool
        return pools
    raise ValueError("pools file must be a map of pool_id -> pool object or a list of pool objects")


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
        kill_switch_on=bool(budget_raw.get("kill_switch_on", False)),
    )
    last_action_epoch_raw = data.get("last_action_epoch")
    return AutoTraderControllerState(
        budget_state=budget_state,
        last_action_epoch=(None if last_action_epoch_raw is None else _require_intish(last_action_epoch_raw, name="last_action_epoch")),
        lifetime_spent=_require_intish(data.get("lifetime_spent", 0), name="lifetime_spent"),
        live_orders=_require_intish(data.get("live_orders", 0), name="live_orders"),
    )


def _load_controller_state_file(path: str | Path | None) -> AutoTraderControllerState:
    if path is None:
        return AutoTraderControllerState()
    obj = _load_json_file(path)
    if not isinstance(obj, Mapping):
        raise ValueError("controller state file must be an object")
    return _controller_state_from_dict(obj)


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
        enabled=bool(data.get("enabled", True)),
    )


def _load_wallet_capability_file(path: str | Path | None) -> AutoTraderWalletCapability | None:
    if path is None:
        return None
    obj = _load_json_file(path)
    if not isinstance(obj, Mapping):
        raise ValueError("wallet capability file must be an object")
    return _wallet_capability_from_dict(obj)


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
        enabled=bool(data.get("enabled", True)),
        revoked_at_epoch=(
            None
            if data.get("revoked_at_epoch") is None
            else _require_intish(data.get("revoked_at_epoch"), name="revoked_at_epoch")
        ),
    )


def _load_session_state_file(path: str | Path | None) -> AutoTraderSessionState | None:
    if path is None:
        return None
    obj = _load_json_file(path)
    if not isinstance(obj, Mapping):
        raise ValueError("session state file must be an object")
    return _session_state_from_dict(obj)


def _load_external_signals_file(path: str | Path | None) -> tuple[ExternalSignalObservation, ...]:
    if path is None:
        return ()
    obj = _load_json_file(path)
    return tuple(external_signal_observations_from_object(obj))


def _load_signal_source_registry_file(path: str | Path | None) -> ExternalSignalSourceRegistry | None:
    if path is None:
        return None
    obj = _load_json_file(path)
    return external_signal_source_registry_from_object(obj)


def _load_krr_bundle_file(path: str | Path | None) -> AutoTraderKRRBundle | None:
    if path is None:
        return None
    return load_autotrader_krr_bundle_file(path)


def _load_policy_artifact_file(path: str | Path | None):
    if path is None:
        return None
    obj = _load_json_file(path)
    if not isinstance(obj, Mapping):
        raise ValueError("policy artifact file must be an object")
    return strategy_policy_artifact_from_dict(obj)


def _load_tau_policy_bundle_file(path: str | Path | None):
    if path is None:
        return None
    obj = _load_json_file(path)
    if not isinstance(obj, Mapping):
        raise ValueError("tau policy bundle file must be an object")
    return tau_policy_bundle_from_dict(obj)


def _load_strategy(
    *,
    policy_file: str | None,
    candidate_file: str | None,
    policy_text: str | None,
    policy_text_file: str | None,
    owner_pubkey: str | None,
) -> StrategyIR:
    if policy_file:
        return load_local_policy_file(policy_file)
    if candidate_file:
        obj = _load_json_file(candidate_file)
        if not isinstance(obj, Mapping):
            raise ValueError("candidate file must be an object")
        return compile_policy_candidate(obj, owner_pubkey=owner_pubkey).strategy
    if policy_text_file:
        policy_text = Path(policy_text_file).expanduser().resolve().read_text(encoding="utf-8")
    if policy_text is not None:
        return compile_policy_text(policy_text, owner_pubkey=owner_pubkey).compiled.strategy
    raise ValueError(
        "one of --policy-file, --candidate-file, --policy-text, or --policy-text-file is required"
    )


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
) -> dict[str, Any]:
    return {
        "schema": "zenodex/autotrader-live-report/v1",
        "mode": "live_prepare",
        "krr_bundle": None if krr_bundle is None else krr_bundle.to_dict(),
        "signing": {
            "chain_id": report.chain_id,
            "signer_pubkey": report.signer_pubkey,
            "last_used_nonce_before": int(report.last_used_nonce_before),
            "last_used_nonce_after": int(report.last_used_nonce_after),
        },
        "wallet_capability": (
            None if report.wallet_capability is None else report.wallet_capability.to_dict()
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
                "quote_receipt": env.quote_receipt,
            }
            for env in report.signed_intents
        ],
        "krr_advice": report.krr_advice,
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
    }


def _emit_json(data: dict[str, Any], *, pretty: bool) -> None:
    text = json.dumps(data, indent=2 if pretty else None, sort_keys=True)
    print(text)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--policy-file")
    source.add_argument("--candidate-file")
    source.add_argument("--policy-text")
    source.add_argument("--policy-text-file")
    parser.add_argument("--owner-pubkey")
    parser.add_argument("--receipt-file", required=True)
    parser.add_argument("--pools-file", required=True)
    parser.add_argument("--controller-state-file")
    parser.add_argument("--wallet-capability-file")
    parser.add_argument("--session-state-file")
    parser.add_argument("--policy-artifact-file")
    parser.add_argument("--tau-policy-bundle-file")
    parser.add_argument("--external-signals-file")
    parser.add_argument("--signal-source-registry-file")
    parser.add_argument("--history-check-stats-file", help="Optional KRR history-check-stats JSON")
    parser.add_argument("--krr-bundle-file", help="Optional reviewed signed offline KRR bundle JSON")
    parser.add_argument("--current-epoch", required=True, type=int)
    parser.add_argument("--intent-deadline", required=True, type=int)
    parser.add_argument("--last-used-nonce", required=True, type=int)
    parser.add_argument("--signer-privkey", required=True)
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
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        strategy = _load_strategy(
            policy_file=args.policy_file,
            candidate_file=args.candidate_file,
            policy_text=args.policy_text,
            policy_text_file=args.policy_text_file,
            owner_pubkey=args.owner_pubkey,
        )
        receipt = _load_json_file(args.receipt_file)
        if not isinstance(receipt, Mapping):
            raise ValueError("receipt file must be an object")
        pools_by_id = _load_pools_file(args.pools_file)
        controller_state = _load_controller_state_file(args.controller_state_file)
        wallet_capability = _load_wallet_capability_file(args.wallet_capability_file)
        session_state = _load_session_state_file(args.session_state_file)
        policy_artifact = _load_policy_artifact_file(args.policy_artifact_file)
        tau_policy_bundle = _load_tau_policy_bundle_file(args.tau_policy_bundle_file)
        krr_bundle = _load_krr_bundle_file(args.krr_bundle_file)
        if krr_bundle is not None and any(
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
        else:
            bundle_krr_kb = None
            external_signals = _load_external_signals_file(args.external_signals_file)
            signal_source_registry = _load_signal_source_registry_file(
                args.signal_source_registry_file
            )
            history_check_stats = None
            if args.history_check_stats_file:
                history_obj = _load_json_file(args.history_check_stats_file)
                if not isinstance(history_obj, Mapping):
                    raise ValueError("history-check-stats file must be an object")
                history_check_stats = history_obj
        tau_config = AutoTraderTauConfig(
            enabled=bool(args.tau_enabled),
            timeout_s=float(args.tau_timeout_s),
            tau_bin=(args.tau_bin or None),
            allow_path_lookup=bool(args.tau_allow_path_lookup),
        )
        report = prepare_autotrader_live_quote_receipt(
            strategy=strategy,
            controller_state=controller_state,
            receipt=receipt,
            pools_by_id=pools_by_id,
            current_epoch=int(args.current_epoch),
            intent_deadline=int(args.intent_deadline),
            signer_privkey=args.signer_privkey,
            last_used_nonce=int(args.last_used_nonce),
            chain_id=str(args.chain_id),
            wallet_capability=wallet_capability,
            session_state=session_state,
            policy_artifact=policy_artifact,
            tau_policy_bundle=tau_policy_bundle,
            external_signals=external_signals,
            signal_source_registry=signal_source_registry,
            slippage_bps=args.slippage_bps,
            tau_config=tau_config,
            krr_backend=str(args.krr_backend),
            krr_kb_path=args.krr_kb,
            krr_kb=bundle_krr_kb,
            history_check_stats=history_check_stats,
            tx_sequence_number=args.tx_sequence_number,
            tx_expiration_time=args.tx_expiration_time,
            tx_fee_limit=args.tx_fee_limit,
        )
        payload = _live_report_to_dict(report, krr_bundle=krr_bundle)
        if args.telemetry_out:
            Path(args.telemetry_out).write_text(
                json.dumps(payload, indent=2, sort_keys=True),
                encoding="utf-8",
            )
        _emit_json(payload, pretty=bool(args.pretty))
        return 0
    except Exception as exc:
        payload = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        if args.telemetry_out:
            Path(args.telemetry_out).write_text(
                json.dumps(payload, indent=2, sort_keys=True),
                encoding="utf-8",
            )
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
