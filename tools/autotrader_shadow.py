#!/usr/bin/env python3
"""Shadow-mode CLI for the policy-constrained auto-trader."""

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
    load_autotrader_krr_bundle_file,
)
from src.agents.krr_policy_advisor import advise_autotrader_krr  # noqa: E402
from src.agents.local_policy import load_local_policy_file  # noqa: E402
from src.agents.policy_artifacts import (  # noqa: E402
    build_strategy_policy_artifact,
    build_tau_policy_bundle,
)
from src.agents.policy_compiler import compile_policy_candidate  # noqa: E402
from src.agents.policy_text_compiler import compile_policy_text  # noqa: E402
from src.agents.strategy_ir import StrategyIR  # noqa: E402
from src.agents.tau_policy_adapter import build_compile_contract_tau_policy_receipt  # noqa: E402
from src.agents.zenograph_fact_pack import (  # noqa: E402
    load_zenograph_fact_pack_file,
    zenograph_runtime_facts,
)
from src.agents.zenograph_rules import ZGTrustTier  # noqa: E402
from src.integration.autotrader_controller import (  # noqa: E402
    AutoTraderControllerState,
    AutoTraderTauConfig,
    _resolve_tau_bin,
    evaluate_autotrader_quote_receipt,
)
from src.integration.autotrader_decision import (  # noqa: E402
    build_strategy_candidate_set,
    build_strategy_decision_certificate,
)
from src.integration.autotrader_multiaction_decision import (  # noqa: E402
    build_bounded_multi_action_candidate_set,
    build_bounded_multi_action_decision_certificate,
    check_bounded_multi_action_decision_tau_argmax_contract,
    verify_bounded_multi_action_decision_certificate,
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
    AutoTraderObservationPacket,
    ExternalSignalObservation,
    build_autotrader_observation_packet,
    build_quote_receipt_signal_packet,
    external_signal_observations_from_object,
)
from src.integration.decision_witness import (  # noqa: E402
    build_decision_witness_from_autotrader_binary_decision,
    build_decision_witness_from_autotrader_multiaction_decision,
    verify_decision_witness_against_autotrader_binary_decision,
    verify_decision_witness_against_autotrader_multiaction_decision,
)
from src.integration.zenograph_autotrader_adapter import (  # noqa: E402
    build_zenograph_autotrader_advisory_observation,
)
from src.kernels.python.strategy_budget_guard_v1_adapter import StrategyBudgetState  # noqa: E402
from src.kernels.python.strategy_candidate_set_contract_v1_adapter import (  # noqa: E402
    check_strategy_candidate_set_contract,
)
from src.kernels.python.strategy_decision_kernel_v1_adapter import (  # noqa: E402
    check_strategy_decision_kernel,
)
from src.kernels.python.strategy_kill_switch_guard_v1_adapter import (  # noqa: E402
    check_strategy_kill_switch_guard,
)
from src.kernels.python.strategy_multi_action_candidate_set_contract_v1_adapter import (  # noqa: E402
    check_strategy_multi_action_candidate_set_contract,
)
from src.state.intents import Intent  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


def _load_json_file(path: str | Path) -> Any:
    p = Path(path).expanduser().resolve()
    return json.loads(p.read_text(encoding="utf-8"))


def _load_optional_object_file(path: str | Path | None, *, name: str) -> dict[str, object]:
    if path is None:
        return {}
    obj = _load_json_file(path)
    if not isinstance(obj, Mapping):
        raise ValueError(f"{name} file must be a JSON object")
    return dict(obj)


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
            pools = {str(key): _pool_state_from_dict(value) for key, value in obj.items()}
            return pools
    if isinstance(obj, list):
        pools = {}
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


def _load_external_signals_file(path: str | Path | None) -> tuple[ExternalSignalObservation, ...]:
    if path is None:
        return ()
    obj = _load_json_file(path)
    return tuple(external_signal_observations_from_object(obj))


def _load_signal_source_registry_file(path: str | Path | None) -> ExternalSignalSourceRegistry | None:
    if path is None:
        return None
    obj = _load_json_file(path)
    if isinstance(obj, Mapping) and "schema" in obj:
        ok, error = verify_external_signal_source_registry_payload(obj)
        if not ok:
            raise ValueError(f"signal source registry payload rejected: {error}")
    return external_signal_source_registry_from_object(obj)


def _load_krr_bundle_file(path: str | Path | None) -> AutoTraderKRRBundle | None:
    if path is None:
        return None
    return load_autotrader_krr_bundle_file(path)


def _load_zenograph_facts_file(path: str | Path | None) -> dict[tuple[str, str], object]:
    if path is None:
        return {}
    obj = _load_json_file(path)
    if isinstance(obj, Mapping):
        if "facts" in obj:
            obj = obj["facts"]
        else:
            out: dict[tuple[str, str], object] = {}
            for subject_id, predicates in obj.items():
                if not isinstance(subject_id, str) or not isinstance(predicates, Mapping):
                    raise ValueError(
                        "zenograph facts object form must map subject_id -> object of predicate -> value"
                    )
                for predicate, value in predicates.items():
                    if not isinstance(predicate, str):
                        raise ValueError("zenograph fact predicates must be strings")
                    out[(subject_id, predicate)] = value
            return out
    if not isinstance(obj, list):
        raise ValueError("zenograph facts file must be a list or nested object")
    rows_out: dict[tuple[str, str], object] = {}
    for row in obj:
        if not isinstance(row, Mapping):
            raise ValueError("zenograph fact entries must be objects")
        subject_id = row.get("subject_id")
        predicate = row.get("predicate")
        if not isinstance(subject_id, str) or not isinstance(predicate, str):
            raise ValueError("zenograph fact entries require string subject_id and predicate")
        if "value" in row:
            rows_out[(subject_id, predicate)] = row["value"]
        elif "object_id" in row:
            rows_out[(subject_id, predicate)] = row["object_id"]
        else:
            raise ValueError("zenograph fact entries require value or object_id")
    return rows_out


def _load_zenograph_trust_tier(value: str) -> ZGTrustTier:
    try:
        return ZGTrustTier(value)
    except ValueError as exc:
        raise ValueError(f"unsupported zenograph source trust tier: {value}") from exc


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


def _krr_advice_for_strategy(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    current_epoch: int,
    observation_packet: AutoTraderObservationPacket | None,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    kb_path: str | None,
    kb: Mapping[str, Any] | None,
    backend: str,
    history_check_stats: Mapping[str, object] | None,
) -> dict[str, Any] | None:
    if backend == "off":
        return None
    if isinstance(history_check_stats, Mapping):
        history = dict(history_check_stats)
    else:
        history = {}
    return advise_autotrader_krr(
        strategy=strategy,
        phase="shadow",
        current_epoch=current_epoch,
        backend=backend,
        kb_path=kb_path,
        kb=kb,
        history_check_stats=history,
        spent_in_window=controller_state.budget_state.spent_in_window,
        lifetime_spent=controller_state.lifetime_spent,
        live_orders=controller_state.live_orders,
        observation_packet=observation_packet,
        quote_receipt=receipt,
        pools_by_id=pools_by_id,
    )


def build_shadow_report(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    intent_deadline: int,
    slippage_bps: int | None,
    nonce_start: int | None,
    tau_config: AutoTraderTauConfig | None,
    krr_backend: str,
    krr_kb_path: str | None,
    krr_kb: Mapping[str, Any] | None,
    history_check_stats: Mapping[str, object] | None,
    external_signals: tuple[ExternalSignalObservation, ...],
    signal_source_registry: ExternalSignalSourceRegistry | None,
    krr_bundle: AutoTraderKRRBundle | None = None,
    chain_id: str = "tau-net-alpha",
    zenograph_enabled: bool = False,
    zenograph_facts: Mapping[tuple[str, str], object] | None = None,
    zenograph_signals: Mapping[str, object] | None = None,
    zenograph_user_state: Mapping[str, object] | None = None,
    zenograph_source_trust: ZGTrustTier = ZGTrustTier.ADVISORY,
    zenograph_liquidity_state: str | None = None,
) -> dict[str, Any]:
    observation_packet = None
    observation_packet_error: str | None = None
    try:
        primary_signal = build_quote_receipt_signal_packet(
            receipt=receipt,
            pools_by_id=pools_by_id,
            current_epoch=current_epoch,
        )
        observation_packet = build_autotrader_observation_packet(
            primary_signal=primary_signal,
            external_signals=external_signals,
            signal_source_registry=signal_source_registry,
            tau_enabled=False,
        )
    except Exception as exc:
        observation_packet = None
        observation_packet_error = f"{type(exc).__name__}:{exc}"
    decision = evaluate_autotrader_quote_receipt(
        strategy=strategy,
        controller_state=controller_state,
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=current_epoch,
        intent_deadline=intent_deadline,
        slippage_bps=slippage_bps,
        nonce_start=nonce_start,
        tau_config=tau_config,
    )
    zenograph_advisory = None
    if zenograph_enabled:
        zenograph_advisory = build_zenograph_autotrader_advisory_observation(
            strategy=strategy,
            receipt=receipt,
            pools_by_id=pools_by_id,
            current_epoch=current_epoch,
            chain_id=chain_id,
            facts=zenograph_facts or {},
            signals=zenograph_signals or {},
            user_state=zenograph_user_state or {},
            source_trust=zenograph_source_trust,
            liquidity_state=zenograph_liquidity_state,
            external_signals=external_signals,
            signal_source_registry=signal_source_registry,
            tau_enabled=bool(tau_config.enabled) if tau_config is not None else False,
            include_krr=False,
        )
    tau_policy_bundle = None
    policy_artifact = None
    candidate_set = None
    decision_certificate = None
    decision_witness = None
    bounded_multiaction_candidate_set = None
    bounded_multiaction_decision_certificate = None
    bounded_multiaction_decision_witness = None
    candidate_set_contract: dict[str, Any] = {"ok": None, "error": None}
    decision_contract: dict[str, Any] = {"ok": None, "error": None}
    decision_witness_contract: dict[str, Any] = {"ok": None, "error": None}
    bounded_multiaction_decision_contract: dict[str, Any] = {
        "ok": None,
        "error": None,
        "frontier_unambiguous": None,
    }
    bounded_multiaction_candidate_set_contract: dict[str, Any] = {
        "ok": None,
        "error": None,
        "frontier_unambiguous": None,
    }
    bounded_multiaction_decision_witness_contract: dict[str, Any] = {
        "ok": None,
        "error": None,
        "frontier_unambiguous": None,
    }
    bounded_multiaction_tau_argmax_contract: dict[str, Any] = {
        "ok": None,
        "error": None,
        "tau_enabled": bool(tau_config.enabled) if tau_config is not None else False,
        "tau_used": False,
        "frontier_unambiguous": None,
    }
    kill_switch: dict[str, Any] = {"ok": None, "error": None}
    compile_tau_receipt = build_compile_contract_tau_policy_receipt(strategy=strategy)
    tau_policy_bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=compile_tau_receipt.to_dict(),
    )
    policy_artifact = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=tau_policy_bundle,
    )
    if observation_packet is not None:
        kill_switch_result = check_strategy_kill_switch_guard(
            kill_switch_enabled=strategy.controls.kill_switch_enabled,
            kill_switch_active=controller_state.budget_state.kill_switch_on,
        )
        kill_switch = {"ok": bool(kill_switch_result.ok), "error": kill_switch_result.error}
        candidate_set = build_strategy_candidate_set(
            policy_artifact=policy_artifact,
            tau_policy_bundle=tau_policy_bundle,
            observation_packet=observation_packet,
            emit_requested=decision.tag.value == "submit",
            emit_admissible=decision.tag.value == "submit",
        )
        candidate_set_result = check_strategy_candidate_set_contract(candidate_set)
        candidate_set_contract = {
            "ok": bool(candidate_set_result.ok),
            "error": candidate_set_result.error,
        }
        decision_certificate = build_strategy_decision_certificate(
            candidate_set=candidate_set,
            kill_switch_active=controller_state.budget_state.kill_switch_on,
        )
        decision_runtime = check_strategy_decision_kernel(
            emit_requested=decision.tag.value == "submit",
            emit_admissible=(decision.tag.value == "submit") and bool(kill_switch_result.ok),
        )
        expected_winner_index = 1 if decision.tag.value == "submit" else 0
        decision_ok = bool(decision_runtime.ok) and decision_certificate.winner_index == expected_winner_index
        decision_contract = {
            "ok": decision_ok,
            "error": None
            if decision_ok
            else ("decision_prefers_noop" if expected_winner_index == 1 else "decision_prefers_emit"),
        }
        try:
            decision_witness = build_decision_witness_from_autotrader_binary_decision(
                strategy=strategy,
                observation_packet=observation_packet,
                candidate_set=candidate_set,
                certificate=decision_certificate,
            )
            witness_ok, witness_error = verify_decision_witness_against_autotrader_binary_decision(
                strategy=strategy,
                observation_packet=observation_packet,
                candidate_set=candidate_set,
                certificate=decision_certificate,
                witness_payload=decision_witness.to_dict(),
            )
            decision_witness_contract = {
                "ok": witness_ok,
                "error": witness_error,
            }
        except Exception as exc:
            decision_witness = None
            decision_witness_contract = {
                "ok": False,
                "error": f"{type(exc).__name__}:{exc}",
            }
        if len(strategy.allowed_actions) == 1:
            bounded_multiaction_candidate_set = build_bounded_multi_action_candidate_set(
                policy_artifact=policy_artifact,
                tau_policy_bundle=tau_policy_bundle,
                observation_packet=observation_packet,
                action_frontier={
                    strategy.allowed_actions[0]: (
                        decision.tag.value == "submit",
                        (decision.tag.value == "submit") and bool(kill_switch_result.ok),
                        1,
                    )
                },
            )
            multiaction_candidate_set_result = check_strategy_multi_action_candidate_set_contract(
                bounded_multiaction_candidate_set
            )
            bounded_multiaction_candidate_set_contract = {
                "ok": bool(multiaction_candidate_set_result.ok),
                "error": multiaction_candidate_set_result.error,
                "frontier_unambiguous": True,
            }
            if multiaction_candidate_set_result.ok:
                bounded_multiaction_decision_certificate = (
                    build_bounded_multi_action_decision_certificate(
                        candidate_set=bounded_multiaction_candidate_set
                    )
                )
                multiaction_ok, multiaction_error = verify_bounded_multi_action_decision_certificate(
                    candidate_set=bounded_multiaction_candidate_set,
                    certificate=bounded_multiaction_decision_certificate,
                )
                bounded_multiaction_decision_contract = {
                    "ok": multiaction_ok,
                    "error": multiaction_error,
                    "frontier_unambiguous": True,
                }
                try:
                    bounded_multiaction_decision_witness = (
                        build_decision_witness_from_autotrader_multiaction_decision(
                            strategy=strategy,
                            observation_packet=observation_packet,
                            candidate_set=bounded_multiaction_candidate_set,
                            certificate=bounded_multiaction_decision_certificate,
                        )
                    )
                    multiaction_witness_ok, multiaction_witness_error = (
                        verify_decision_witness_against_autotrader_multiaction_decision(
                            strategy=strategy,
                            observation_packet=observation_packet,
                            candidate_set=bounded_multiaction_candidate_set,
                            certificate=bounded_multiaction_decision_certificate,
                            witness_payload=bounded_multiaction_decision_witness.to_dict(),
                        )
                    )
                    bounded_multiaction_decision_witness_contract = {
                        "ok": multiaction_witness_ok,
                        "error": multiaction_witness_error,
                        "frontier_unambiguous": True,
                    }
                except Exception as exc:
                    bounded_multiaction_decision_witness = None
                    bounded_multiaction_decision_witness_contract = {
                        "ok": False,
                        "error": f"{type(exc).__name__}:{exc}",
                        "frontier_unambiguous": True,
                    }
                if tau_config is not None and tau_config.enabled:
                    tau_ok, tau_bin, tau_error = _resolve_tau_bin(tau_config)
                    if tau_ok and tau_bin is not None:
                        tau_contract = check_bounded_multi_action_decision_tau_argmax_contract(
                            candidate_set=bounded_multiaction_candidate_set,
                            certificate=bounded_multiaction_decision_certificate,
                            tau_bin=tau_bin,
                            timeout_s=tau_config.timeout_s,
                        )
                        bounded_multiaction_tau_argmax_contract = {
                            **tau_contract.to_dict(),
                            "frontier_unambiguous": True,
                        }
                    else:
                        bounded_multiaction_tau_argmax_contract = {
                            "ok": False,
                            "error": tau_error or "tau_not_available",
                            "tau_enabled": True,
                            "tau_used": False,
                            "frontier_unambiguous": True,
                        }
                else:
                    bounded_multiaction_tau_argmax_contract = {
                        "ok": None,
                        "error": "tau_disabled",
                        "tau_enabled": False,
                        "tau_used": False,
                        "frontier_unambiguous": True,
                    }
            else:
                bounded_multiaction_decision_contract = {
                    "ok": False,
                    "error": f"candidate_set_rejected:{multiaction_candidate_set_result.error}",
                    "frontier_unambiguous": True,
                }
                bounded_multiaction_decision_witness_contract = {
                    "ok": None,
                    "error": "candidate_set_rejected",
                    "frontier_unambiguous": True,
                }
                bounded_multiaction_tau_argmax_contract = {
                    "ok": None,
                    "error": "candidate_set_rejected",
                    "tau_enabled": bool(tau_config.enabled) if tau_config is not None else False,
                    "tau_used": False,
                    "frontier_unambiguous": True,
                }
        else:
            bounded_multiaction_candidate_set_contract = {
                "ok": None,
                "error": "multi_action_frontier_ambiguous",
                "frontier_unambiguous": False,
            }
            bounded_multiaction_decision_contract = {
                "ok": None,
                "error": "multi_action_frontier_ambiguous",
                "frontier_unambiguous": False,
            }
            bounded_multiaction_decision_witness_contract = {
                "ok": None,
                "error": "multi_action_frontier_ambiguous",
                "frontier_unambiguous": False,
            }
            bounded_multiaction_tau_argmax_contract = {
                "ok": None,
                "error": "multi_action_frontier_ambiguous",
                "tau_enabled": bool(tau_config.enabled) if tau_config is not None else False,
                "tau_used": False,
                "frontier_unambiguous": False,
            }
    return {
        "schema": "zenodex/autotrader-shadow-report/v1",
        "mode": "shadow",
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="shadow",
            requires_explicit_acknowledgement=False,
            user_acknowledged=False,
        ),
        "inputs": {
            "current_epoch": int(current_epoch),
            "intent_deadline": int(intent_deadline),
            "slippage_bps": slippage_bps,
            "nonce_start": nonce_start,
            "chain_id": chain_id,
            "pool_count": len(pools_by_id),
            "external_signal_count": len(external_signals),
            "zenograph_enabled": bool(zenograph_enabled),
        },
        "strategy": strategy.to_dict(),
        "strategy_hash": strategy.strategy_hash_hex(),
        "decision_model_version": tau_policy_bundle.decision_model_version,
        "compile_contract_tau_receipt": compile_tau_receipt.to_dict(),
        "tau_policy_bundle_hash": tau_policy_bundle.tau_policy_bundle_hash_hex(),
        "tau_policy_bundle": tau_policy_bundle.to_dict(),
        "policy_artifact_hash": policy_artifact.policy_artifact_hash_hex(),
        "policy_artifact": policy_artifact.to_dict(),
        "krr_bundle": None if krr_bundle is None else krr_bundle.to_dict(),
        "external_signals": [signal.to_dict() for signal in external_signals],
        "signal_source_registry": (
            None if signal_source_registry is None else signal_source_registry.to_dict()
        ),
        "observation_packet": None if observation_packet is None else observation_packet.to_dict(),
        "observation_packet_error": observation_packet_error,
        "zenograph_advisory": (
            None if zenograph_advisory is None else zenograph_advisory.to_dict()
        ),
        "candidate_set": None if candidate_set is None else candidate_set.to_dict(),
        "candidate_set_contract": candidate_set_contract,
        "decision_certificate": None if decision_certificate is None else decision_certificate.to_dict(),
        "decision_contract": decision_contract,
        "decision_witness": None if decision_witness is None else decision_witness.to_dict(),
        "decision_witness_contract": decision_witness_contract,
        "bounded_multiaction_candidate_set": (
            None
            if bounded_multiaction_candidate_set is None
            else bounded_multiaction_candidate_set.to_dict()
        ),
        "bounded_multiaction_candidate_set_contract": (
            bounded_multiaction_candidate_set_contract
        ),
        "bounded_multiaction_decision_certificate": (
            None
            if bounded_multiaction_decision_certificate is None
            else bounded_multiaction_decision_certificate.to_dict()
        ),
        "bounded_multiaction_decision_contract": bounded_multiaction_decision_contract,
        "bounded_multiaction_decision_witness": (
            None
            if bounded_multiaction_decision_witness is None
            else bounded_multiaction_decision_witness.to_dict()
        ),
        "bounded_multiaction_decision_witness_contract": (
            bounded_multiaction_decision_witness_contract
        ),
        "bounded_multiaction_tau_argmax_contract": (
            bounded_multiaction_tau_argmax_contract
        ),
        "kill_switch": kill_switch,
        "controller_state_before": _controller_state_to_dict(controller_state),
        "decision": {
            "tag": decision.tag.value,
            "should_submit": bool(decision.should_submit),
            "reason": decision.reason,
            "explain": list(decision.explain),
            "controller_state_after": _controller_state_to_dict(decision.state),
            "intents": [_intent_to_dict(intent) for intent in decision.intents],
            "tau_policy_receipt": (
                None if decision.tau_policy_receipt is None else decision.tau_policy_receipt.to_dict()
            ),
        },
        "krr_advice": _krr_advice_for_strategy(
            strategy=strategy,
            controller_state=controller_state,
            current_epoch=current_epoch,
            observation_packet=observation_packet,
            receipt=receipt,
            pools_by_id=pools_by_id,
            kb_path=krr_kb_path,
            kb=krr_kb,
            backend=krr_backend,
            history_check_stats=history_check_stats,
        ),
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "Advanced experimental automation and AI shadow surface. "
            "Dry-run only, but any live use of these outputs is at your own risk "
            "and can still lead to total loss."
        ),
    )
    policy_group = ap.add_mutually_exclusive_group(required=True)
    policy_group.add_argument("--policy-file", help="Local policy document JSON")
    policy_group.add_argument("--candidate-file", help="Raw candidate JSON to compile into StrategyIR")
    policy_group.add_argument("--policy-text", help="Inline controlled policy text")
    policy_group.add_argument("--policy-text-file", help="Path to controlled policy text")
    ap.add_argument(
        "--owner-pubkey",
        help="Owner pubkey override when compiling from candidate or controlled text input",
    )
    ap.add_argument("--receipt-file", required=True, help="Route quote receipt JSON")
    ap.add_argument("--pools-file", required=True, help="Pools JSON (map or list form)")
    ap.add_argument("--controller-state-file", help="Optional autotrader controller state JSON")
    ap.add_argument("--external-signals-file", help="Optional external advisory/attested signals JSON")
    ap.add_argument(
        "--signal-source-registry-file",
        help="Optional external signal source registry JSON",
    )
    ap.add_argument("--history-check-stats-file", help="Optional KRR history-check-stats JSON")
    ap.add_argument("--krr-bundle-file", help="Optional reviewed signed offline KRR bundle JSON")
    ap.add_argument("--current-epoch", required=True, type=int)
    ap.add_argument("--intent-deadline", required=True, type=int)
    ap.add_argument("--chain-id", default="tau-net-alpha")
    ap.add_argument("--slippage-bps", type=int)
    ap.add_argument("--nonce-start", type=int)
    ap.add_argument("--tau-enabled", action="store_true")
    ap.add_argument("--tau-bin", help="Absolute tau binary path (unless --tau-allow-path-lookup)")
    ap.add_argument("--tau-timeout-s", type=float, default=2.0)
    ap.add_argument("--tau-allow-path-lookup", action="store_true")
    ap.add_argument(
        "--krr-backend",
        choices=("off", "python", "auto", "prolog", "souffle"),
        default="python",
        help="Advisory KRR backend. Does not affect execution semantics.",
    )
    ap.add_argument("--krr-kb", help="Path to KRR knowledge base JSON")
    ap.add_argument("--zenograph-enable", action="store_true")
    ap.add_argument("--zenograph-facts-file", help="Optional ZenoGraph facts JSON")
    ap.add_argument(
        "--zenograph-fact-pack-file",
        help="Optional reviewed signed ZenoGraph fact pack JSON",
    )
    ap.add_argument("--zenograph-signals-file", help="Optional ZenoGraph signals JSON")
    ap.add_argument("--zenograph-user-state-file", help="Optional ZenoGraph user-state JSON")
    ap.add_argument(
        "--zenograph-source-trust",
        choices=tuple(tier.value for tier in ZGTrustTier),
        default=ZGTrustTier.ADVISORY.value,
        help="ZenoGraph source trust tier for advisory evaluation",
    )
    ap.add_argument(
        "--zenograph-liquidity-state",
        help="Optional ZenoGraph liquidity state token",
    )
    ap.add_argument("--telemetry-out", help="Optional path to write the JSON report")
    ap.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
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
            raise ValueError("receipt file must be a JSON object")
        pools_by_id = _load_pools_file(args.pools_file)
        controller_state = _load_controller_state_file(args.controller_state_file)
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
            bundle_krr_kb = (
                dict(krr_bundle.runtime_krr_kb) if isinstance(krr_bundle.runtime_krr_kb, Mapping) else None
            )
            external_signals = (
                tuple(external_signal_observations_from_object(krr_bundle.runtime_external_signals))
                if krr_bundle.runtime_external_signals is not None
                else ()
            )
            signal_source_registry = (
                external_signal_source_registry_from_object(krr_bundle.runtime_signal_source_registry)
                if krr_bundle.runtime_signal_source_registry is not None
                else None
            )
            history_check_stats = (
                dict(krr_bundle.runtime_history) if isinstance(krr_bundle.runtime_history, Mapping) else None
            )
        else:
            bundle_krr_kb = None
            external_signals = _load_external_signals_file(args.external_signals_file)
            signal_source_registry = _load_signal_source_registry_file(
                args.signal_source_registry_file
            )
            history_check_stats = None
            if args.history_check_stats_file:
                loaded_history = _load_json_file(args.history_check_stats_file)
                if not isinstance(loaded_history, Mapping):
                    raise ValueError("history check stats file must be a JSON object")
                history_check_stats = dict(loaded_history)
        tau_config = AutoTraderTauConfig(
            enabled=bool(args.tau_enabled),
            timeout_s=float(args.tau_timeout_s),
            tau_bin=args.tau_bin,
            allow_path_lookup=bool(args.tau_allow_path_lookup),
        )
        if args.zenograph_facts_file and args.zenograph_fact_pack_file:
            raise ValueError(
                "--zenograph-facts-file cannot be combined with --zenograph-fact-pack-file"
            )
        zenograph_facts = _load_zenograph_facts_file(args.zenograph_facts_file)
        if args.zenograph_fact_pack_file:
            zenograph_facts = zenograph_runtime_facts(
                load_zenograph_fact_pack_file(args.zenograph_fact_pack_file)
            )
        zenograph_signals = _load_optional_object_file(
            args.zenograph_signals_file,
            name="zenograph signals",
        )
        zenograph_user_state = _load_optional_object_file(
            args.zenograph_user_state_file,
            name="zenograph user state",
        )
        report = build_shadow_report(
            strategy=strategy,
            controller_state=controller_state,
            receipt=receipt,
            pools_by_id=pools_by_id,
            current_epoch=int(args.current_epoch),
            intent_deadline=int(args.intent_deadline),
            chain_id=str(args.chain_id),
            slippage_bps=args.slippage_bps,
            nonce_start=args.nonce_start,
            tau_config=tau_config,
            krr_backend=str(args.krr_backend),
            krr_kb_path=args.krr_kb,
            krr_kb=bundle_krr_kb,
            history_check_stats=history_check_stats,
            external_signals=external_signals,
            signal_source_registry=signal_source_registry,
            krr_bundle=krr_bundle,
            zenograph_enabled=bool(args.zenograph_enable),
            zenograph_facts=zenograph_facts,
            zenograph_signals=zenograph_signals,
            zenograph_user_state=zenograph_user_state,
            zenograph_source_trust=_load_zenograph_trust_tier(args.zenograph_source_trust),
            zenograph_liquidity_state=args.zenograph_liquidity_state,
        )
    except Exception as exc:
        error_report = {
            "schema": "zenodex/autotrader-shadow-report/v1",
            "mode": "shadow",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
            "risk_disclosure": build_autotrader_risk_disclosure(
                mode="shadow",
                requires_explicit_acknowledgement=False,
                user_acknowledged=False,
            ),
        }
        text = json.dumps(error_report, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stderr.write(text)
        if args.telemetry_out:
            out_path = Path(args.telemetry_out).expanduser().resolve()
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(text, encoding="utf-8")
        return 1

    text = json.dumps(report, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    sys.stdout.write(text)
    if args.telemetry_out:
        out_path = Path(args.telemetry_out).expanduser().resolve()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
