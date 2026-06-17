from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .zusd_oracle_contracts import (
    ZUSD_CROSS_MODULE_ORACLE_SYNC_CONTRACT_SCHEMA,
    ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA,
    ZUSDCrossModuleOracleSyncContract,
    ZUSDOraclePendingGateContract,
    verify_zusd_cross_module_oracle_sync_contract_payload,
    verify_zusd_oracle_pending_gate_contract_payload,
)

ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA = "zenodex/zusd-oracle-recovery-lifecycle-packet/v1"


@dataclass(frozen=True)
class ZUSDOracleRecoveryLifecyclePacket:
    previous_pending_gate_contract: ZUSDOraclePendingGateContract
    current_pending_gate_contract: ZUSDOraclePendingGateContract
    current_sync_contract: ZUSDCrossModuleOracleSyncContract
    nested_contracts_ok: bool
    risky_action_requested: bool
    previous_risky_action_blocked: bool
    current_oracle_env_ok: bool
    current_sync_gate_ok: bool
    sync_aligned_to_current_gate: bool
    healthy_now: bool
    current_risky_ops_allowed: bool
    risky_ops_reenabled: bool
    rejected_with_reason: bool
    rejection_reason_present: bool
    rejection_reason: str | None
    lifecycle_ok: bool
    schema: str = ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.previous_pending_gate_contract.to_dict().get("schema") != ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA:
            raise ValueError("unexpected previous pending gate schema")
        if self.current_pending_gate_contract.to_dict().get("schema") != ZUSD_ORACLE_PENDING_GATE_CONTRACT_SCHEMA:
            raise ValueError("unexpected current pending gate schema")
        if self.current_sync_contract.to_dict().get("schema") != ZUSD_CROSS_MODULE_ORACLE_SYNC_CONTRACT_SCHEMA:
            raise ValueError("unexpected current sync schema")
        for name in (
            "nested_contracts_ok",
            "risky_action_requested",
            "previous_risky_action_blocked",
            "current_oracle_env_ok",
            "current_sync_gate_ok",
            "sync_aligned_to_current_gate",
            "healthy_now",
            "current_risky_ops_allowed",
            "risky_ops_reenabled",
            "rejected_with_reason",
            "rejection_reason_present",
            "lifecycle_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")
        if self.rejection_reason is not None and (
            not isinstance(self.rejection_reason, str) or not self.rejection_reason.strip()
        ):
            raise ValueError("rejection_reason must be a non-empty string when present")
        if self.rejection_reason_present != bool(
            isinstance(self.rejection_reason, str) and self.rejection_reason.strip()
        ):
            raise ValueError("rejection_reason_present mismatch")
        if self.rejected_with_reason != (not self.risky_ops_reenabled):
            raise ValueError("rejected_with_reason mismatch")
        if self.healthy_now != (
            self.current_oracle_env_ok and self.current_sync_gate_ok and self.sync_aligned_to_current_gate
        ):
            raise ValueError("healthy_now mismatch")
        if self.rejected_with_reason and not self.rejection_reason_present:
            raise ValueError("rejected_with_reason requires rejection_reason_present")
        success_formula = bool(
            self.nested_contracts_ok
            and self.risky_action_requested
            and self.previous_risky_action_blocked
            and self.healthy_now
            and self.current_risky_ops_allowed
        )
        lifecycle_formula = bool(
            (self.risky_ops_reenabled != self.rejected_with_reason)
            and ((not self.rejected_with_reason) or self.rejection_reason_present)
            and ((not self.risky_ops_reenabled) or success_formula)
        )
        if self.lifecycle_ok != lifecycle_formula:
            raise ValueError("lifecycle_ok formula mismatch")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "previous_pending_gate_contract": self.previous_pending_gate_contract.to_dict(),
            "current_pending_gate_contract": self.current_pending_gate_contract.to_dict(),
            "current_sync_contract": self.current_sync_contract.to_dict(),
            "nested_contracts_ok": bool(self.nested_contracts_ok),
            "risky_action_requested": bool(self.risky_action_requested),
            "previous_risky_action_blocked": bool(self.previous_risky_action_blocked),
            "current_oracle_env_ok": bool(self.current_oracle_env_ok),
            "current_sync_gate_ok": bool(self.current_sync_gate_ok),
            "sync_aligned_to_current_gate": bool(self.sync_aligned_to_current_gate),
            "healthy_now": bool(self.healthy_now),
            "current_risky_ops_allowed": bool(self.current_risky_ops_allowed),
            "risky_ops_reenabled": bool(self.risky_ops_reenabled),
            "rejected_with_reason": bool(self.rejected_with_reason),
            "rejection_reason_present": bool(self.rejection_reason_present),
            "rejection_reason": self.rejection_reason,
            "lifecycle_ok": bool(self.lifecycle_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ZUSDOracleRecoveryLifecyclePacket":
        if not isinstance(payload, Mapping):
            raise ValueError("oracle recovery lifecycle packet must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            previous_pending_gate_contract=ZUSDOraclePendingGateContract.from_dict(
                payload.get("previous_pending_gate_contract")
            ),
            current_pending_gate_contract=ZUSDOraclePendingGateContract.from_dict(
                payload.get("current_pending_gate_contract")
            ),
            current_sync_contract=ZUSDCrossModuleOracleSyncContract.from_dict(
                payload.get("current_sync_contract")
            ),
            nested_contracts_ok=bool(payload.get("nested_contracts_ok", False)),
            risky_action_requested=bool(payload.get("risky_action_requested", False)),
            previous_risky_action_blocked=bool(payload.get("previous_risky_action_blocked", False)),
            current_oracle_env_ok=bool(payload.get("current_oracle_env_ok", False)),
            current_sync_gate_ok=bool(payload.get("current_sync_gate_ok", False)),
            sync_aligned_to_current_gate=bool(payload.get("sync_aligned_to_current_gate", False)),
            healthy_now=bool(payload.get("healthy_now", False)),
            current_risky_ops_allowed=bool(payload.get("current_risky_ops_allowed", False)),
            risky_ops_reenabled=bool(payload.get("risky_ops_reenabled", False)),
            rejected_with_reason=bool(payload.get("rejected_with_reason", False)),
            rejection_reason_present=bool(payload.get("rejection_reason_present", False)),
            rejection_reason=payload.get("rejection_reason"),
            lifecycle_ok=bool(payload.get("lifecycle_ok", False)),
        )


def build_zusd_oracle_recovery_lifecycle_packet(
    *,
    previous_pending_gate_contract: ZUSDOraclePendingGateContract,
    current_pending_gate_contract: ZUSDOraclePendingGateContract,
    current_sync_contract: ZUSDCrossModuleOracleSyncContract,
) -> ZUSDOracleRecoveryLifecyclePacket:
    previous_ok, _ = verify_zusd_oracle_pending_gate_contract_payload(previous_pending_gate_contract.to_dict())
    current_ok, _ = verify_zusd_oracle_pending_gate_contract_payload(current_pending_gate_contract.to_dict())
    sync_ok, _ = verify_zusd_cross_module_oracle_sync_contract_payload(current_sync_contract.to_dict())
    nested_contracts_ok = bool(previous_ok and current_ok and sync_ok)

    risky_action_requested = bool(
        previous_pending_gate_contract.risky_requested and current_pending_gate_contract.risky_requested
    )
    previous_risky_action_blocked = bool(
        previous_pending_gate_contract.risky_requested and not previous_pending_gate_contract.action_allowed
    )
    current_oracle_env_ok = bool(current_pending_gate_contract.env_ok)
    current_sync_gate_ok = bool(current_sync_contract.sync_gate_ok)
    sync_aligned_to_current_gate = bool(
        current_sync_contract.zusd_price_e8 == current_pending_gate_contract.price_e8
        and current_sync_contract.zusd_epoch == current_pending_gate_contract.oracle_last_update_epoch
    )
    healthy_now = bool(current_oracle_env_ok and current_sync_gate_ok and sync_aligned_to_current_gate)
    current_risky_ops_allowed = bool(current_pending_gate_contract.risky_ops_allowed)
    risky_ops_reenabled = bool(
        nested_contracts_ok
        and risky_action_requested
        and previous_risky_action_blocked
        and healthy_now
        and current_risky_ops_allowed
    )

    rejection_reason: str | None = None
    if not nested_contracts_ok:
        rejection_reason = "nested_contract_invalid"
    elif not risky_action_requested:
        rejection_reason = "risky_action_not_requested"
    elif not previous_risky_action_blocked:
        rejection_reason = "previous_risky_action_not_blocked"
    elif not current_oracle_env_ok:
        rejection_reason = "current_oracle_env_not_healthy"
    elif not sync_aligned_to_current_gate:
        rejection_reason = "current_sync_not_aligned_to_oracle_gate"
    elif not current_sync_gate_ok:
        rejection_reason = "current_cross_module_sync_not_ok"
    elif not current_risky_ops_allowed:
        rejection_reason = "recovery_mode_still_active"

    rejected_with_reason = not risky_ops_reenabled
    rejection_reason_present = bool(isinstance(rejection_reason, str) and rejection_reason.strip())
    if rejected_with_reason and not rejection_reason_present:
        rejection_reason = "oracle recovery lifecycle missing rejection reason"
        rejection_reason_present = True

    return ZUSDOracleRecoveryLifecyclePacket(
        previous_pending_gate_contract=previous_pending_gate_contract,
        current_pending_gate_contract=current_pending_gate_contract,
        current_sync_contract=current_sync_contract,
        nested_contracts_ok=nested_contracts_ok,
        risky_action_requested=risky_action_requested,
        previous_risky_action_blocked=previous_risky_action_blocked,
        current_oracle_env_ok=current_oracle_env_ok,
        current_sync_gate_ok=current_sync_gate_ok,
        sync_aligned_to_current_gate=sync_aligned_to_current_gate,
        healthy_now=healthy_now,
        current_risky_ops_allowed=current_risky_ops_allowed,
        risky_ops_reenabled=risky_ops_reenabled,
        rejected_with_reason=rejected_with_reason,
        rejection_reason_present=rejection_reason_present,
        rejection_reason=rejection_reason,
        lifecycle_ok=True,
    )


def verify_zusd_oracle_recovery_lifecycle_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, Mapping):
        return False, "oracle recovery lifecycle packet payload must be a dict"
    if str(payload.get("schema", "")) != ZUSD_ORACLE_RECOVERY_LIFECYCLE_PACKET_SCHEMA:
        return False, "unsupported oracle recovery lifecycle packet schema"
    try:
        packet = ZUSDOracleRecoveryLifecyclePacket.from_dict(payload)
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    expected = build_zusd_oracle_recovery_lifecycle_packet(
        previous_pending_gate_contract=packet.previous_pending_gate_contract,
        current_pending_gate_contract=packet.current_pending_gate_contract,
        current_sync_contract=packet.current_sync_contract,
    )
    if dict(payload) != expected.to_dict():
        return False, "oracle recovery lifecycle packet payload mismatch"
    return True, None
