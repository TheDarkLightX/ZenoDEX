from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from src.core.zusd import ZUSDState

from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1,
    TauSpecRef,
    build_zusd_cross_module_oracle_sync_gate_v1_step,
)

ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA = "zenodex/zusd-oracle-pending-gate-contract/v1"
ZUSD_CROSS_MODULE_ORACLE_SYNC_CONTRACT_SCHEMA = "zenodex/zusd-cross-module-oracle-sync-contract/v1"


def _require_bool(value: object, field_name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{field_name} must be a bool")
    return value


def _require_int(value: object, field_name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{field_name} must be an int")
    return value


def _require_nonempty_string(value: object, field_name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{field_name} must be a non-empty string")
    return value


def _require_state_mode(value: object) -> str:
    state_mode = _require_nonempty_string(value, "state_mode")
    if state_mode != "single":
        raise ValueError("state_mode must be single")
    return state_mode


def _require_int_field(payload: Mapping[str, Any], field_name: str) -> int:
    if field_name not in payload:
        raise ValueError(f"{field_name} must be an int")
    return _require_int(payload[field_name], field_name)


def _require_tau_step(payload: object) -> dict[str, int]:
    if not isinstance(payload, dict):
        raise ValueError("tau_step must be an object")
    return {str(key): _require_int(value, f"tau_step.{key}") for key, value in payload.items()}


@dataclass(frozen=True)
class ZUSDOraclePendingGateContract:
    state_mode: str
    oracle_seen: bool
    price_e8: int
    price_pending_e8: int
    oracle_last_update_epoch: int
    now_epoch: int
    max_staleness_epochs: int
    tcr_ok: bool
    risky_requested: bool
    pending_eq: bool
    price_pos: bool
    fresh: bool
    env_ok: bool
    risky_ops_allowed: bool
    blocked_by_recovery: bool
    action_allowed: bool

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA,
            "state_mode": str(self.state_mode),
            "oracle_seen": bool(self.oracle_seen),
            "price_e8": int(self.price_e8),
            "price_pending_e8": int(self.price_pending_e8),
            "oracle_last_update_epoch": int(self.oracle_last_update_epoch),
            "now_epoch": int(self.now_epoch),
            "max_staleness_epochs": int(self.max_staleness_epochs),
            "tcr_ok": bool(self.tcr_ok),
            "risky_requested": bool(self.risky_requested),
            "pending_eq": bool(self.pending_eq),
            "price_pos": bool(self.price_pos),
            "fresh": bool(self.fresh),
            "env_ok": bool(self.env_ok),
            "risky_ops_allowed": bool(self.risky_ops_allowed),
            "blocked_by_recovery": bool(self.blocked_by_recovery),
            "action_allowed": bool(self.action_allowed),
        }

    @classmethod
    def from_dict(cls, payload: object) -> "ZUSDOraclePendingGateContract":
        if not isinstance(payload, dict):
            raise ValueError("oracle pending gate contract must be an object")
        if payload.get("schema") != ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA:
            raise ValueError("unsupported oracle pending gate schema")
        return cls(
            state_mode=_require_state_mode(payload.get("state_mode")),
            oracle_seen=_require_bool(payload.get("oracle_seen"), "oracle_seen"),
            price_e8=_require_int_field(payload, "price_e8"),
            price_pending_e8=_require_int_field(payload, "price_pending_e8"),
            oracle_last_update_epoch=_require_int_field(payload, "oracle_last_update_epoch"),
            now_epoch=_require_int_field(payload, "now_epoch"),
            max_staleness_epochs=_require_int_field(payload, "max_staleness_epochs"),
            tcr_ok=_require_bool(payload.get("tcr_ok"), "tcr_ok"),
            risky_requested=_require_bool(payload.get("risky_requested"), "risky_requested"),
            pending_eq=_require_bool(payload.get("pending_eq"), "pending_eq"),
            price_pos=_require_bool(payload.get("price_pos"), "price_pos"),
            fresh=_require_bool(payload.get("fresh"), "fresh"),
            env_ok=_require_bool(payload.get("env_ok"), "env_ok"),
            risky_ops_allowed=_require_bool(payload.get("risky_ops_allowed"), "risky_ops_allowed"),
            blocked_by_recovery=_require_bool(payload.get("blocked_by_recovery"), "blocked_by_recovery"),
            action_allowed=_require_bool(payload.get("action_allowed"), "action_allowed"),
        )


@dataclass(frozen=True)
class ZUSDCrossModuleOracleSyncContract:
    market_id: str
    zusd_price_e8: int
    zusd_epoch: int
    perp_price_e8: int
    perp_oracle_epoch: int
    max_divergence_bps: int
    max_epoch_lag: int
    divergence_bps: int
    epoch_lag: int
    sync_snapshot_available: bool
    divergence_bounded: bool
    epoch_lag_bounded: bool
    sync_gate_ok: bool
    tau_step: dict[str, int]
    tau_spec_id: str = ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1.spec_id

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": ZUSD_CROSS_MODULE_ORACLE_SYNC_CONTRACT_SCHEMA,
            "market_id": str(self.market_id),
            "zusd_price_e8": int(self.zusd_price_e8),
            "zusd_epoch": int(self.zusd_epoch),
            "perp_price_e8": int(self.perp_price_e8),
            "perp_oracle_epoch": int(self.perp_oracle_epoch),
            "max_divergence_bps": int(self.max_divergence_bps),
            "max_epoch_lag": int(self.max_epoch_lag),
            "divergence_bps": int(self.divergence_bps),
            "epoch_lag": int(self.epoch_lag),
            "sync_snapshot_available": bool(self.sync_snapshot_available),
            "divergence_bounded": bool(self.divergence_bounded),
            "epoch_lag_bounded": bool(self.epoch_lag_bounded),
            "sync_gate_ok": bool(self.sync_gate_ok),
            "tau_spec_id": str(self.tau_spec_id),
            "tau_step": dict(self.tau_step),
        }

    @classmethod
    def from_dict(cls, payload: object) -> "ZUSDCrossModuleOracleSyncContract":
        if not isinstance(payload, dict):
            raise ValueError("cross-module oracle sync contract must be an object")
        if payload.get("schema") != ZUSD_CROSS_MODULE_ORACLE_SYNC_CONTRACT_SCHEMA:
            raise ValueError("unsupported cross-module oracle sync schema")
        tau_step = _require_tau_step(payload.get("tau_step"))
        return cls(
            market_id=_require_nonempty_string(payload.get("market_id"), "market_id"),
            zusd_price_e8=_require_int_field(payload, "zusd_price_e8"),
            zusd_epoch=_require_int_field(payload, "zusd_epoch"),
            perp_price_e8=_require_int_field(payload, "perp_price_e8"),
            perp_oracle_epoch=_require_int_field(payload, "perp_oracle_epoch"),
            max_divergence_bps=_require_int_field(payload, "max_divergence_bps"),
            max_epoch_lag=_require_int_field(payload, "max_epoch_lag"),
            divergence_bps=_require_int_field(payload, "divergence_bps"),
            epoch_lag=_require_int_field(payload, "epoch_lag"),
            sync_snapshot_available=_require_bool(
                payload.get("sync_snapshot_available"), "sync_snapshot_available"
            ),
            divergence_bounded=_require_bool(payload.get("divergence_bounded"), "divergence_bounded"),
            epoch_lag_bounded=_require_bool(payload.get("epoch_lag_bounded"), "epoch_lag_bounded"),
            sync_gate_ok=_require_bool(payload.get("sync_gate_ok"), "sync_gate_ok"),
            tau_spec_id=_require_nonempty_string(
                payload.get("tau_spec_id", ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1.spec_id),
                "tau_spec_id",
            ),
            tau_step=tau_step,
        )


def _is_oracle_fresh(*, now_epoch: int, last_update_epoch: int, max_staleness_epochs: int, oracle_seen: bool) -> bool:
    if not bool(oracle_seen):
        return False
    if int(max_staleness_epochs) < 0:
        return False
    return abs(int(now_epoch) - int(last_update_epoch)) <= int(max_staleness_epochs)


def build_zusd_oracle_pending_gate_contract(
    state: ZUSDState,
    *,
    risky_requested: bool,
    max_staleness_epochs: int = 100,
    tcr_ok: bool = True,
) -> ZUSDOraclePendingGateContract:
    if type(state) is not ZUSDState:
        raise TypeError("state must be a ZUSDState")
    state_mode = "single"
    oracle_seen = bool(state.oracle_seen)
    price_e8 = int(state.price_e8)
    price_pending_e8 = int(state.price_pending_e8)
    oracle_last_update_epoch = int(state.oracle_last_update_epoch)
    now_epoch = int(state.now_epoch)
    pending_eq = oracle_seen and price_e8 > 0 and price_pending_e8 > 0 and price_pending_e8 == price_e8
    price_pos = oracle_seen and price_e8 > 0 and price_pending_e8 > 0
    fresh = _is_oracle_fresh(
        now_epoch=int(now_epoch),
        last_update_epoch=int(oracle_last_update_epoch),
        max_staleness_epochs=int(max_staleness_epochs),
        oracle_seen=bool(oracle_seen),
    )
    env_ok = bool(oracle_seen) and bool(price_pos) and bool(pending_eq) and bool(fresh)
    risky_ops_allowed = bool(env_ok) and bool(tcr_ok)
    blocked_by_recovery = bool(env_ok) and not bool(tcr_ok)
    action_allowed = (not bool(risky_requested)) or bool(risky_ops_allowed)
    return ZUSDOraclePendingGateContract(
        state_mode=state_mode,
        oracle_seen=bool(oracle_seen),
        price_e8=int(price_e8),
        price_pending_e8=int(price_pending_e8),
        oracle_last_update_epoch=int(oracle_last_update_epoch),
        now_epoch=int(now_epoch),
        max_staleness_epochs=int(max_staleness_epochs),
        tcr_ok=bool(tcr_ok),
        risky_requested=bool(risky_requested),
        pending_eq=bool(pending_eq),
        price_pos=bool(price_pos),
        fresh=bool(fresh),
        env_ok=bool(env_ok),
        risky_ops_allowed=bool(risky_ops_allowed),
        blocked_by_recovery=bool(blocked_by_recovery),
        action_allowed=bool(action_allowed),
    )


def verify_zusd_oracle_pending_gate_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "contract payload must be a dict"
    required = {
        "schema",
        "state_mode",
        "oracle_seen",
        "price_e8",
        "price_pending_e8",
        "oracle_last_update_epoch",
        "now_epoch",
        "max_staleness_epochs",
        "tcr_ok",
        "risky_requested",
        "pending_eq",
        "price_pos",
        "fresh",
        "env_ok",
        "risky_ops_allowed",
        "blocked_by_recovery",
        "action_allowed",
    }
    if not required.issubset(payload.keys()):
        return False, "contract payload missing required keys"
    if payload.get("schema") != ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA:
        return False, "unsupported oracle pending gate schema"
    try:
        _require_state_mode(payload["state_mode"])
        oracle_seen = _require_bool(payload["oracle_seen"], "oracle_seen")
        tcr_ok = _require_bool(payload["tcr_ok"], "tcr_ok")
        risky_requested = _require_bool(payload["risky_requested"], "risky_requested")
        for flag_name in (
            "pending_eq",
            "price_pos",
            "fresh",
            "env_ok",
            "risky_ops_allowed",
            "blocked_by_recovery",
            "action_allowed",
        ):
            _require_bool(payload[flag_name], flag_name)
    except ValueError as exc:
        return False, str(exc)
    try:
        price_e8 = _require_int_field(payload, "price_e8")
        price_pending_e8 = _require_int_field(payload, "price_pending_e8")
        now_epoch = _require_int_field(payload, "now_epoch")
        oracle_last_update_epoch = _require_int_field(payload, "oracle_last_update_epoch")
        max_staleness_epochs = _require_int_field(payload, "max_staleness_epochs")
    except ValueError as exc:
        return False, str(exc)
    pending_eq = oracle_seen and price_e8 > 0 and price_pending_e8 > 0 and price_pending_e8 == price_e8
    price_pos = oracle_seen and price_e8 > 0 and price_pending_e8 > 0
    fresh = _is_oracle_fresh(
        now_epoch=int(now_epoch),
        last_update_epoch=int(oracle_last_update_epoch),
        max_staleness_epochs=int(max_staleness_epochs),
        oracle_seen=bool(oracle_seen),
    )
    env_ok = bool(oracle_seen) and bool(price_pos) and bool(pending_eq) and bool(fresh)
    risky_ops_allowed = bool(env_ok) and bool(tcr_ok)
    blocked_by_recovery = bool(env_ok) and not bool(tcr_ok)
    action_allowed = (not bool(risky_requested)) or bool(risky_ops_allowed)
    expected = {
        "pending_eq": bool(pending_eq),
        "price_pos": bool(price_pos),
        "fresh": bool(fresh),
        "env_ok": bool(env_ok),
        "risky_ops_allowed": bool(risky_ops_allowed),
        "blocked_by_recovery": bool(blocked_by_recovery),
        "action_allowed": bool(action_allowed),
    }
    for key, value in expected.items():
        if payload.get(key) != bool(value):
            return False, f"{key} mismatch"
    return True, None


def build_zusd_cross_module_oracle_sync_contract(
    *,
    market_id: str,
    zusd_price_e8: int,
    zusd_epoch: int,
    perp_price_e8: int,
    perp_oracle_epoch: int,
    max_divergence_bps: int,
    max_epoch_lag: int,
) -> ZUSDCrossModuleOracleSyncContract:
    if not isinstance(market_id, str) or not market_id:
        raise ValueError("market_id must be a non-empty string")
    if int(max_divergence_bps) < 0 or int(max_divergence_bps) > 10_000:
        raise ValueError("max_divergence_bps out of range")
    if int(max_epoch_lag) < 0:
        raise ValueError("max_epoch_lag out of range")
    sync_snapshot_available = int(perp_price_e8) > 0
    divergence_bps = 0
    if bool(sync_snapshot_available):
        divergence_bps = (abs(int(zusd_price_e8) - int(perp_price_e8)) * 10_000) // int(perp_price_e8)
    epoch_lag = abs(int(zusd_epoch) - int(perp_oracle_epoch))
    divergence_bounded = bool(sync_snapshot_available) and int(divergence_bps) <= int(max_divergence_bps)
    epoch_lag_bounded = bool(sync_snapshot_available) and int(epoch_lag) <= int(max_epoch_lag)
    sync_gate_ok = bool(sync_snapshot_available) and bool(divergence_bounded) and bool(epoch_lag_bounded)
    tau_step = build_zusd_cross_module_oracle_sync_gate_v1_step(
        sync_snapshot_available=1 if sync_snapshot_available else 0,
        divergence_bounded=1 if divergence_bounded else 0,
        epoch_lag_bounded=1 if epoch_lag_bounded else 0,
    )
    return ZUSDCrossModuleOracleSyncContract(
        market_id=str(market_id),
        zusd_price_e8=int(zusd_price_e8),
        zusd_epoch=int(zusd_epoch),
        perp_price_e8=int(perp_price_e8),
        perp_oracle_epoch=int(perp_oracle_epoch),
        max_divergence_bps=int(max_divergence_bps),
        max_epoch_lag=int(max_epoch_lag),
        divergence_bps=int(divergence_bps),
        epoch_lag=int(epoch_lag),
        sync_snapshot_available=bool(sync_snapshot_available),
        divergence_bounded=bool(divergence_bounded),
        epoch_lag_bounded=bool(epoch_lag_bounded),
        sync_gate_ok=bool(sync_gate_ok),
        tau_step=tau_step,
    )


def verify_zusd_cross_module_oracle_sync_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "contract payload must be a dict"
    required = {
        "schema",
        "market_id",
        "zusd_price_e8",
        "zusd_epoch",
        "perp_price_e8",
        "perp_oracle_epoch",
        "max_divergence_bps",
        "max_epoch_lag",
        "divergence_bps",
        "epoch_lag",
        "sync_snapshot_available",
        "divergence_bounded",
        "epoch_lag_bounded",
        "sync_gate_ok",
        "tau_spec_id",
        "tau_step",
    }
    if not required.issubset(payload.keys()):
        return False, "contract payload missing required keys"
    if payload.get("schema") != ZUSD_CROSS_MODULE_ORACLE_SYNC_CONTRACT_SCHEMA:
        return False, "unsupported cross-module oracle sync schema"
    for flag_name in (
        "sync_snapshot_available",
        "divergence_bounded",
        "epoch_lag_bounded",
        "sync_gate_ok",
    ):
        try:
            _require_bool(payload[flag_name], flag_name)
        except ValueError as exc:
            return False, str(exc)
    try:
        zusd_price_e8 = _require_int_field(payload, "zusd_price_e8")
        zusd_epoch = _require_int_field(payload, "zusd_epoch")
        perp_price_e8 = _require_int_field(payload, "perp_price_e8")
        perp_oracle_epoch = _require_int_field(payload, "perp_oracle_epoch")
        max_divergence_bps = _require_int_field(payload, "max_divergence_bps")
        max_epoch_lag = _require_int_field(payload, "max_epoch_lag")
        _require_int_field(payload, "divergence_bps")
        _require_int_field(payload, "epoch_lag")
        market_id = _require_nonempty_string(payload["market_id"], "market_id")
        tau_spec_id = _require_nonempty_string(payload["tau_spec_id"], "tau_spec_id")
        _require_tau_step(payload["tau_step"])
    except ValueError as exc:
        return False, str(exc)
    if tau_spec_id != ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1.spec_id:
        return False, "tau_spec_id mismatch"
    expected = build_zusd_cross_module_oracle_sync_contract(
        market_id=market_id,
        zusd_price_e8=zusd_price_e8,
        zusd_epoch=zusd_epoch,
        perp_price_e8=perp_price_e8,
        perp_oracle_epoch=perp_oracle_epoch,
        max_divergence_bps=max_divergence_bps,
        max_epoch_lag=max_epoch_lag,
    )
    if payload != expected.to_dict():
        return False, "contract payload mismatch"
    return True, None


def replay_tau_step(
    spec_ref: TauSpecRef,
    *,
    step: dict[str, int],
    tau_bin: str | None = None,
    timeout_s: float = 10.0,
) -> tuple[bool, str | None]:
    resolved_tau_bin = tau_bin or find_tau_bin()
    if not resolved_tau_bin:
        return False, "tau not found"
    outputs = run_tau_spec_steps(
        tau_bin=str(resolved_tau_bin),
        spec_path=Path(spec_ref.path),
        steps=[dict(step)],
        timeout_s=float(timeout_s),
    )
    gate = outputs.get(0, {}).get(spec_ref.gate_output)
    if int(gate or 0) != 1:
        return False, f"Tau gate failed for {spec_ref.spec_id}"
    return True, None
