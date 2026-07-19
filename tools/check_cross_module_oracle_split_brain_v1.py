#!/usr/bin/env python3
"""Replayable cross-module oracle split-brain pack."""

# This executable supports direct invocation from any working directory; the
# repository root must be admitted before importing project modules.
# ruff: noqa: E402

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.zusd import E8, ZUSDCommand, ZUSDState, init_state, step
from src.integration.zusd_oracle_contracts import (
    ZUSDCrossModuleOracleSyncContract,
    ZUSDOraclePendingGateContract,
    build_zusd_cross_module_oracle_sync_contract,
    build_zusd_oracle_pending_gate_contract,
    verify_zusd_cross_module_oracle_sync_contract_payload,
    verify_zusd_oracle_pending_gate_contract_payload,
)
from src.integration.zusd_oracle_recovery_lifecycle import (
    build_zusd_oracle_recovery_lifecycle_packet,
    verify_zusd_oracle_recovery_lifecycle_packet_payload,
)

_state = init_state()


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _reset() -> None:
    global _state
    _state = init_state()


def _step(tag: str, **args: Any) -> dict[str, Any]:
    global _state
    result = step(_state, ZUSDCommand(tag=tag, args=args))
    _assert(result.ok and result.state is not None, f"zusd step failed for {tag}: {result.error}")
    _state = result.state
    return dict(_state.__dict__)


def _build_pending_gate(*, state: dict[str, Any], risky_requested: bool, tcr_ok: bool) -> dict[str, Any]:
    return build_zusd_oracle_pending_gate_contract(
        ZUSDState(**state),
        risky_requested=risky_requested,
        tcr_ok=tcr_ok,
    ).to_dict()


def _build_sync(
    *,
    zusd_price_e8: int,
    zusd_epoch: int,
    perp_price_e8: int,
    perp_oracle_epoch: int,
    max_divergence_bps: int,
    max_epoch_lag: int,
) -> dict[str, Any]:
    return build_zusd_cross_module_oracle_sync_contract(
        market_id="TAU-USD",
        zusd_price_e8=zusd_price_e8,
        zusd_epoch=zusd_epoch,
        perp_price_e8=perp_price_e8,
        perp_oracle_epoch=perp_oracle_epoch,
        max_divergence_bps=max_divergence_bps,
        max_epoch_lag=max_epoch_lag,
    ).to_dict()


def _build_recovery(
    *,
    previous_pending_gate_contract: dict[str, Any],
    current_pending_gate_contract: dict[str, Any],
    current_sync_contract: dict[str, Any],
) -> dict[str, Any]:
    return build_zusd_oracle_recovery_lifecycle_packet(
        previous_pending_gate_contract=ZUSDOraclePendingGateContract.from_dict(
            previous_pending_gate_contract
        ),
        current_pending_gate_contract=ZUSDOraclePendingGateContract.from_dict(
            current_pending_gate_contract
        ),
        current_sync_contract=ZUSDCrossModuleOracleSyncContract.from_dict(current_sync_contract),
    ).to_dict()


def _verify(path: str, key: str, payload: dict[str, Any]) -> None:
    del key
    verifiers = {
        "/api/zusd/verify_oracle_pending_gate_contract": (
            verify_zusd_oracle_pending_gate_contract_payload
        ),
        "/api/zusd/verify_cross_module_oracle_sync_contract": (
            verify_zusd_cross_module_oracle_sync_contract_payload
        ),
        "/api/zusd/verify_oracle_recovery_lifecycle_packet": (
            verify_zusd_oracle_recovery_lifecycle_packet_payload
        ),
    }
    ok, error = verifiers[path](payload)
    _assert(ok, f"verify failed: {error}")


def _healthy_local_state() -> tuple[dict[str, Any], dict[str, Any]]:
    state = _step("bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    pending = _build_pending_gate(state=state, risky_requested=True, tcr_ok=True)
    _assert(pending["env_ok"] is True, "healthy local oracle should satisfy env_ok")
    _assert(pending["action_allowed"] is True, "healthy local oracle should allow risky action")
    _verify("/api/zusd/verify_oracle_pending_gate_contract", "contract", pending)
    return state, pending


def _local_green_but_divergence_sync_red() -> dict[str, Any]:
    _reset()
    state, pending = _healthy_local_state()
    sync = _build_sync(
        zusd_price_e8=state["price_e8"],
        zusd_epoch=state["oracle_last_update_epoch"],
        perp_price_e8=110 * E8,
        perp_oracle_epoch=state["oracle_last_update_epoch"],
        max_divergence_bps=100,
        max_epoch_lag=0,
    )
    _assert(pending["action_allowed"] is True, "local oracle gate should stay green")
    _assert(sync["epoch_lag_bounded"] is True, "divergence witness should keep lag aligned")
    _assert(sync["divergence_bounded"] is False, "divergence witness should break sync bounds")
    _assert(sync["sync_gate_ok"] is False, "split-brain divergence should reject shared-world sync")
    _verify("/api/zusd/verify_cross_module_oracle_sync_contract", "contract", sync)
    return {
        "scenario_id": "local_green_but_divergence_sync_red",
        "status": "OK",
        "local_action_allowed": pending["action_allowed"],
        "divergence_bps": sync["divergence_bps"],
        "max_divergence_bps": sync["max_divergence_bps"],
    }


def _local_green_but_epoch_lag_sync_red() -> dict[str, Any]:
    _reset()
    state, pending = _healthy_local_state()
    sync = _build_sync(
        zusd_price_e8=state["price_e8"],
        zusd_epoch=state["oracle_last_update_epoch"],
        perp_price_e8=state["price_e8"],
        perp_oracle_epoch=state["oracle_last_update_epoch"] + 3,
        max_divergence_bps=0,
        max_epoch_lag=1,
    )
    _assert(pending["action_allowed"] is True, "local oracle gate should stay green")
    _assert(sync["divergence_bounded"] is True, "epoch-lag witness should keep prices aligned")
    _assert(sync["epoch_lag_bounded"] is False, "epoch-lag witness should break shared-world lag bounds")
    _assert(sync["sync_gate_ok"] is False, "split-brain epoch lag should reject shared-world sync")
    _verify("/api/zusd/verify_cross_module_oracle_sync_contract", "contract", sync)
    return {
        "scenario_id": "local_green_but_epoch_lag_sync_red",
        "status": "OK",
        "local_action_allowed": pending["action_allowed"],
        "epoch_lag": sync["epoch_lag"],
        "max_epoch_lag": sync["max_epoch_lag"],
    }


def _recovery_divergence_split_brain_rejects() -> dict[str, Any]:
    _reset()
    _step("bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    stale_state = _step("advance_epoch", delta=150)
    previous_pending = _build_pending_gate(state=stale_state, risky_requested=True, tcr_ok=True)
    _assert(previous_pending["action_allowed"] is False, "previous stale state should block risky ops")
    _step("oracle_report", price_e8=100 * E8, auth_ok=True)
    current_state = _step("oracle_commit", auth_ok=True)
    current_pending = _build_pending_gate(state=current_state, risky_requested=True, tcr_ok=True)
    _assert(current_pending["action_allowed"] is True, "current local oracle gate should recover")
    sync = _build_sync(
        zusd_price_e8=current_state["price_e8"],
        zusd_epoch=current_state["oracle_last_update_epoch"],
        perp_price_e8=110 * E8,
        perp_oracle_epoch=current_state["oracle_last_update_epoch"],
        max_divergence_bps=100,
        max_epoch_lag=0,
    )
    packet = _build_recovery(
        previous_pending_gate_contract=previous_pending,
        current_pending_gate_contract=current_pending,
        current_sync_contract=sync,
    )
    _assert(packet["current_oracle_env_ok"] is True, "current local oracle env should be healthy")
    _assert(packet["sync_aligned_to_current_gate"] is True, "divergence split-brain should stay aligned to local gate")
    _assert(packet["current_sync_gate_ok"] is False, "divergence split-brain should fail sync gate")
    _assert(packet["risky_ops_reenabled"] is False, "divergence split-brain should block re-enable")
    _assert(packet["rejection_reason"] == "current_cross_module_sync_not_ok", "divergence rejection changed")
    _assert(packet["lifecycle_ok"] is True, "divergence rejection packet should stay replayable")
    _verify("/api/zusd/verify_oracle_recovery_lifecycle_packet", "packet", packet)
    return {
        "scenario_id": "recovery_divergence_split_brain_rejects",
        "status": "OK",
        "rejection_reason": packet["rejection_reason"],
        "current_oracle_env_ok": packet["current_oracle_env_ok"],
    }


def _recovery_epoch_lag_split_brain_rejects() -> dict[str, Any]:
    _reset()
    _step("bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    stale_state = _step("advance_epoch", delta=150)
    previous_pending = _build_pending_gate(state=stale_state, risky_requested=True, tcr_ok=True)
    _step("oracle_report", price_e8=100 * E8, auth_ok=True)
    current_state = _step("oracle_commit", auth_ok=True)
    current_pending = _build_pending_gate(state=current_state, risky_requested=True, tcr_ok=True)
    sync = _build_sync(
        zusd_price_e8=current_state["price_e8"],
        zusd_epoch=current_state["oracle_last_update_epoch"],
        perp_price_e8=current_state["price_e8"],
        perp_oracle_epoch=current_state["oracle_last_update_epoch"] + 3,
        max_divergence_bps=0,
        max_epoch_lag=1,
    )
    packet = _build_recovery(
        previous_pending_gate_contract=previous_pending,
        current_pending_gate_contract=current_pending,
        current_sync_contract=sync,
    )
    _assert(packet["current_oracle_env_ok"] is True, "current local oracle env should stay healthy")
    _assert(packet["sync_aligned_to_current_gate"] is True, "epoch-lag split-brain should stay aligned to local gate")
    _assert(packet["current_sync_gate_ok"] is False, "epoch-lag split-brain should fail sync gate")
    _assert(packet["risky_ops_reenabled"] is False, "epoch-lag split-brain should block re-enable")
    _assert(packet["rejection_reason"] == "current_cross_module_sync_not_ok", "epoch-lag rejection changed")
    _assert(packet["lifecycle_ok"] is True, "epoch-lag rejection packet should stay replayable")
    _verify("/api/zusd/verify_oracle_recovery_lifecycle_packet", "packet", packet)
    return {
        "scenario_id": "recovery_epoch_lag_split_brain_rejects",
        "status": "OK",
        "rejection_reason": packet["rejection_reason"],
        "current_oracle_env_ok": packet["current_oracle_env_ok"],
    }


def _aligned_shared_world_reenables_under_same_local_gate() -> dict[str, Any]:
    _reset()
    _step("bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    stale_state = _step("advance_epoch", delta=150)
    previous_pending = _build_pending_gate(state=stale_state, risky_requested=True, tcr_ok=True)
    _step("oracle_report", price_e8=100 * E8, auth_ok=True)
    current_state = _step("oracle_commit", auth_ok=True)
    current_pending = _build_pending_gate(state=current_state, risky_requested=True, tcr_ok=True)
    sync = _build_sync(
        zusd_price_e8=current_state["price_e8"],
        zusd_epoch=current_state["oracle_last_update_epoch"],
        perp_price_e8=current_state["price_e8"],
        perp_oracle_epoch=current_state["oracle_last_update_epoch"],
        max_divergence_bps=0,
        max_epoch_lag=0,
    )
    packet = _build_recovery(
        previous_pending_gate_contract=previous_pending,
        current_pending_gate_contract=current_pending,
        current_sync_contract=sync,
    )
    _assert(current_pending["action_allowed"] is True, "local oracle gate should be green in aligned control")
    _assert(sync["sync_gate_ok"] is True, "aligned shared world should pass sync gate")
    _assert(packet["risky_ops_reenabled"] is True, "aligned shared world should re-enable risky ops")
    _assert(packet["rejected_with_reason"] is False, "aligned shared world should not reject")
    _verify("/api/zusd/verify_cross_module_oracle_sync_contract", "contract", sync)
    _verify("/api/zusd/verify_oracle_recovery_lifecycle_packet", "packet", packet)
    return {
        "scenario_id": "aligned_shared_world_reenables_under_same_local_gate",
        "status": "OK",
        "local_action_allowed": current_pending["action_allowed"],
        "risky_ops_reenabled": packet["risky_ops_reenabled"],
    }


def check_cross_module_oracle_split_brain_v1() -> dict[str, Any]:
    scenarios = (
        _local_green_but_divergence_sync_red(),
        _local_green_but_epoch_lag_sync_red(),
        _recovery_divergence_split_brain_rejects(),
        _recovery_epoch_lag_split_brain_rejects(),
        _aligned_shared_world_reenables_under_same_local_gate(),
    )
    return {"ok": True, "scenario_count": len(scenarios), "scenarios": scenarios}


def main() -> int:
    parser = argparse.ArgumentParser(description="Replayable cross-module oracle split-brain pack.")
    _ = parser.parse_args()
    report = check_cross_module_oracle_split_brain_v1()
    print(f"OK CROSS_MODULE_ORACLE_SPLIT_BRAIN_V1 scenarios={report['scenario_count']}/{report['scenario_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
