from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex

from .settlement_attestation_policy import (
    SettlementAttestationPolicy,
    coerce_settlement_attestation_policy,
)


SETTLEMENT_SIGNER_REGISTRY_SNAPSHOT_SCHEMA = "zenodex/settlement-signer-registry-snapshot/v1"


@dataclass(frozen=True)
class SettlementSignerRegistrySnapshot:
    chain_id: int
    registry_contract: str
    registry_root: str
    snapshot_block_number: int
    snapshot_block_hash: str
    policy: SettlementAttestationPolicy
    schema: str = SETTLEMENT_SIGNER_REGISTRY_SNAPSHOT_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_SIGNER_REGISTRY_SNAPSHOT_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.policy, SettlementAttestationPolicy):
            raise TypeError("policy must be a SettlementAttestationPolicy")
        for name in ("chain_id", "snapshot_block_number"):
            value = getattr(self, name)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError(f"{name} must be a non-negative int")
        object.__setattr__(
            self,
            "registry_contract",
            canonical_hex_fixed_allow_0x(self.registry_contract, nbytes=20, name="registry_contract"),
        )
        object.__setattr__(
            self,
            "registry_root",
            canonical_hex_fixed_allow_0x(self.registry_root, nbytes=32, name="registry_root"),
        )
        object.__setattr__(
            self,
            "snapshot_block_hash",
            canonical_hex_fixed_allow_0x(self.snapshot_block_hash, nbytes=32, name="snapshot_block_hash"),
        )
        if int(self.policy.chain_id) != int(self.chain_id):
            raise ValueError("registry snapshot chain_id must match policy.chain_id")
        if self.policy.registry_contract != self.registry_contract:
            raise ValueError("registry snapshot registry_contract must match policy.registry_contract")
        if self.policy.registry_root != self.registry_root:
            raise ValueError("registry snapshot registry_root must match policy.registry_root")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "chain_id": int(self.chain_id),
            "registry_contract": self.registry_contract,
            "registry_root": self.registry_root,
            "snapshot_block_number": int(self.snapshot_block_number),
            "snapshot_block_hash": self.snapshot_block_hash,
            "policy": self.policy.to_dict(),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSignerRegistrySnapshot":
        if not isinstance(payload, Mapping):
            raise ValueError("attestation_registry_snapshot must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            chain_id=int(payload.get("chain_id", -1)),
            registry_contract=str(payload.get("registry_contract", "")),
            registry_root=str(payload.get("registry_root", "")),
            snapshot_block_number=int(payload.get("snapshot_block_number", -1)),
            snapshot_block_hash=str(payload.get("snapshot_block_hash", "")),
            policy=SettlementAttestationPolicy.from_dict(payload.get("policy", {})),
        )

    def snapshot_hash_hex(self) -> str:
        return sha256_hex(
            domain_sep_bytes("settlement_signer_registry_snapshot", version=1) + canonical_json_bytes(self.to_dict())
        )


@dataclass(frozen=True)
class SettlementAttestationRegistryBindingResult:
    ok: bool
    policy_present: bool
    snapshot_present: bool
    chain_id_match: bool
    registry_contract_match: bool
    registry_root_match: bool
    policy_id_match: bool
    policy_epoch_match: bool
    policy_hash_match: bool
    error: str | None = None
    error_code: str | None = None
    details: Mapping[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "ok": bool(self.ok),
            "policy_present": bool(self.policy_present),
            "snapshot_present": bool(self.snapshot_present),
            "chain_id_match": bool(self.chain_id_match),
            "registry_contract_match": bool(self.registry_contract_match),
            "registry_root_match": bool(self.registry_root_match),
            "policy_id_match": bool(self.policy_id_match),
            "policy_epoch_match": bool(self.policy_epoch_match),
            "policy_hash_match": bool(self.policy_hash_match),
            "error": self.error,
            "error_code": self.error_code,
            "details": None if self.details is None else dict(self.details),
        }

    def telemetry_payload(self) -> dict[str, Any]:
        return self.to_dict()


@dataclass(frozen=True)
class SettlementSignerRegistrySnapshotRequest:
    chain_id: int
    registry_contract: str
    policy_id: str
    policy_epoch: int
    registry_root_hint: str
    policy_hash_hint: str
    consumer_now_epoch: int

    def __post_init__(self) -> None:
        for name in ("chain_id", "policy_epoch", "consumer_now_epoch"):
            value = getattr(self, name)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError(f"{name} must be a non-negative int")
        if not isinstance(self.policy_id, str) or not self.policy_id.strip():
            raise ValueError("policy_id must be a non-empty string")
        object.__setattr__(self, "policy_id", self.policy_id.strip())
        object.__setattr__(
            self,
            "registry_contract",
            canonical_hex_fixed_allow_0x(self.registry_contract, nbytes=20, name="registry_contract"),
        )
        object.__setattr__(
            self,
            "registry_root_hint",
            canonical_hex_fixed_allow_0x(self.registry_root_hint, nbytes=32, name="registry_root_hint"),
        )
        object.__setattr__(
            self,
            "policy_hash_hint",
            canonical_hex_fixed_allow_0x(self.policy_hash_hint, nbytes=32, name="policy_hash_hint"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "chain_id": int(self.chain_id),
            "registry_contract": self.registry_contract,
            "policy_id": self.policy_id,
            "policy_epoch": int(self.policy_epoch),
            "registry_root_hint": self.registry_root_hint,
            "policy_hash_hint": self.policy_hash_hint,
            "consumer_now_epoch": int(self.consumer_now_epoch),
        }


@dataclass(frozen=True)
class SettlementSignerRegistrySnapshotLoadResult:
    ok: bool
    snapshot_present: bool
    binding_ok: bool
    error: str | None = None
    error_code: str | None = None
    details: Mapping[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "ok": bool(self.ok),
            "snapshot_present": bool(self.snapshot_present),
            "binding_ok": bool(self.binding_ok),
            "error": self.error,
            "error_code": self.error_code,
            "details": None if self.details is None else dict(self.details),
        }

    def telemetry_payload(self) -> dict[str, Any]:
        return self.to_dict()


class InMemorySettlementSignerRegistrySnapshotLoader:
    def __init__(self, snapshots: Mapping[tuple[int, str, str, int], SettlementSignerRegistrySnapshot | Mapping[str, Any]]):
        if not isinstance(snapshots, Mapping):
            raise TypeError("snapshots must be a mapping")
        normalized: dict[tuple[int, str, str, int], SettlementSignerRegistrySnapshot] = {}
        for key, raw_snapshot in snapshots.items():
            if (
                not isinstance(key, tuple)
                or len(key) != 4
                or not isinstance(key[0], int)
                or not isinstance(key[1], str)
                or not isinstance(key[2], str)
                or not isinstance(key[3], int)
            ):
                raise TypeError("snapshot loader keys must be (chain_id, registry_contract, policy_id, policy_epoch)")
            normalized_key = (
                int(key[0]),
                canonical_hex_fixed_allow_0x(key[1], nbytes=20, name="registry_contract"),
                str(key[2]).strip(),
                int(key[3]),
            )
            normalized[normalized_key] = coerce_settlement_signer_registry_snapshot(raw_snapshot)
        self._snapshots = normalized

    def load_snapshot(self, request: SettlementSignerRegistrySnapshotRequest) -> SettlementSignerRegistrySnapshot | None:
        return self._snapshots.get(
            (
                int(request.chain_id),
                request.registry_contract,
                request.policy_id,
                int(request.policy_epoch),
            )
        )


def check_settlement_attestation_policy_registry_binding(
    *,
    policy: SettlementAttestationPolicy | None,
    registry_snapshot: SettlementSignerRegistrySnapshot | None,
) -> SettlementAttestationRegistryBindingResult:
    if policy is None or registry_snapshot is None:
        details = {
            "policy_present": bool(policy is not None),
            "snapshot_present": bool(registry_snapshot is not None),
        }
        return SettlementAttestationRegistryBindingResult(
            ok=False,
            policy_present=bool(policy is not None),
            snapshot_present=bool(registry_snapshot is not None),
            chain_id_match=False,
            registry_contract_match=False,
            registry_root_match=False,
            policy_id_match=False,
            policy_epoch_match=False,
            policy_hash_match=False,
            error=_format_binding_error(
                "attestation policy registry binding requires both policy and attestation_registry_snapshot",
                details=details,
            ),
            error_code="attestation_registry_binding_missing_surface",
            details=details,
        )

    chain_id_match = int(policy.chain_id) == int(registry_snapshot.chain_id)
    registry_contract_match = policy.registry_contract == registry_snapshot.registry_contract
    registry_root_match = policy.registry_root == registry_snapshot.registry_root
    policy_id_match = policy.policy_id == registry_snapshot.policy.policy_id
    policy_epoch_match = int(policy.policy_epoch) == int(registry_snapshot.policy.policy_epoch)
    policy_hash_match = policy.policy_hash_hex() == registry_snapshot.policy.policy_hash_hex()
    ok = (
        chain_id_match
        and registry_contract_match
        and registry_root_match
        and policy_id_match
        and policy_epoch_match
        and policy_hash_match
    )
    details = {
        "policy_id": policy.policy_id,
        "policy_epoch": int(policy.policy_epoch),
        "policy_hash": policy.policy_hash_hex(),
        "policy_chain_id": int(policy.chain_id),
        "policy_registry_contract": policy.registry_contract,
        "policy_registry_root": policy.registry_root,
        "snapshot_policy_id": registry_snapshot.policy.policy_id,
        "snapshot_policy_epoch": int(registry_snapshot.policy.policy_epoch),
        "snapshot_policy_hash": registry_snapshot.policy.policy_hash_hex(),
        "snapshot_chain_id": int(registry_snapshot.chain_id),
        "snapshot_registry_contract": registry_snapshot.registry_contract,
        "snapshot_registry_root": registry_snapshot.registry_root,
        "snapshot_block_number": int(registry_snapshot.snapshot_block_number),
        "snapshot_block_hash": registry_snapshot.snapshot_block_hash,
        "snapshot_hash": registry_snapshot.snapshot_hash_hex(),
    }
    if ok:
        return SettlementAttestationRegistryBindingResult(
            ok=True,
            policy_present=True,
            snapshot_present=True,
            chain_id_match=True,
            registry_contract_match=True,
            registry_root_match=True,
            policy_id_match=True,
            policy_epoch_match=True,
            policy_hash_match=True,
            details=details,
        )
    if not chain_id_match:
        error_code = "attestation_registry_binding_chain_id_mismatch"
        error = _format_binding_error("attestation policy chain_id does not match registry snapshot", details=details)
    elif not registry_contract_match:
        error_code = "attestation_registry_binding_registry_contract_mismatch"
        error = _format_binding_error(
            "attestation policy registry_contract does not match registry snapshot",
            details=details,
        )
    elif not registry_root_match:
        error_code = "attestation_registry_binding_registry_root_mismatch"
        error = _format_binding_error("attestation policy registry_root does not match registry snapshot", details=details)
    elif not policy_id_match:
        error_code = "attestation_registry_binding_policy_id_mismatch"
        error = _format_binding_error("attestation policy_id does not match registry snapshot policy", details=details)
    elif not policy_epoch_match:
        error_code = "attestation_registry_binding_policy_epoch_mismatch"
        error = _format_binding_error(
            "attestation policy_epoch does not match registry snapshot policy",
            details=details,
        )
    else:
        error_code = "attestation_registry_binding_policy_hash_mismatch"
        error = _format_binding_error("attestation policy content does not match registry snapshot policy", details=details)
    return SettlementAttestationRegistryBindingResult(
        ok=False,
        policy_present=True,
        snapshot_present=True,
        chain_id_match=chain_id_match,
        registry_contract_match=registry_contract_match,
        registry_root_match=registry_root_match,
        policy_id_match=policy_id_match,
        policy_epoch_match=policy_epoch_match,
        policy_hash_match=policy_hash_match,
        error=error,
        error_code=error_code,
        details=details,
    )


def coerce_settlement_signer_registry_snapshot(
    registry_snapshot: SettlementSignerRegistrySnapshot | Mapping[str, Any] | None,
) -> SettlementSignerRegistrySnapshot | None:
    if registry_snapshot is None:
        return None
    if isinstance(registry_snapshot, SettlementSignerRegistrySnapshot):
        return registry_snapshot
    if isinstance(registry_snapshot, Mapping):
        return SettlementSignerRegistrySnapshot.from_dict(registry_snapshot)
    raise TypeError(
        "attestation_registry_snapshot must be a SettlementSignerRegistrySnapshot or object mapping"
    )


def resolve_attestation_policy_and_registry_snapshot(
    *,
    attestation_policy: SettlementAttestationPolicy | Mapping[str, Any] | None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | Mapping[str, Any] | None,
) -> tuple[SettlementAttestationPolicy | None, SettlementSignerRegistrySnapshot | None]:
    policy = coerce_settlement_attestation_policy(attestation_policy)
    registry_snapshot = coerce_settlement_signer_registry_snapshot(attestation_registry_snapshot)
    if registry_snapshot is None:
        return policy, None
    if policy is None:
        return registry_snapshot.policy, registry_snapshot
    binding = check_settlement_attestation_policy_registry_binding(
        policy=policy,
        registry_snapshot=registry_snapshot,
    )
    if not binding.ok:
        raise ValueError(binding.error or "attestation policy registry binding failed")
    return policy, registry_snapshot


def load_attestation_policy_and_registry_snapshot(
    *,
    attestation_policy: SettlementAttestationPolicy | Mapping[str, Any] | None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | Mapping[str, Any] | None,
    attestation_registry_snapshot_loader: object | None,
    consumer_now_epoch: int,
) -> tuple[SettlementAttestationPolicy | None, SettlementSignerRegistrySnapshot | None]:
    policy, registry_snapshot = resolve_attestation_policy_and_registry_snapshot(
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
    )
    if registry_snapshot is not None or policy is None or attestation_registry_snapshot_loader is None:
        return policy, registry_snapshot
    if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
        raise ValueError("consumer_now_epoch must be a non-negative int")
    load_snapshot = getattr(attestation_registry_snapshot_loader, "load_snapshot", None)
    if not callable(load_snapshot):
        raise TypeError("attestation_registry_snapshot_loader must define load_snapshot(request)")
    request = SettlementSignerRegistrySnapshotRequest(
        chain_id=int(policy.chain_id),
        registry_contract=policy.registry_contract,
        policy_id=policy.policy_id,
        policy_epoch=int(policy.policy_epoch),
        registry_root_hint=policy.registry_root,
        policy_hash_hint=policy.policy_hash_hex(),
        consumer_now_epoch=int(consumer_now_epoch),
    )
    raw_snapshot = load_snapshot(request)
    if raw_snapshot is None:
        details = request.to_dict()
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot loader returned no snapshot",
                details=details,
            )
        )
    registry_snapshot = coerce_settlement_signer_registry_snapshot(raw_snapshot)
    binding = check_settlement_attestation_policy_registry_binding(
        policy=policy,
        registry_snapshot=registry_snapshot,
    )
    if not binding.ok:
        raise ValueError(binding.error or "attestation policy registry binding failed")
    return policy, registry_snapshot


def _format_binding_error(base_error: str, *, details: Mapping[str, Any]) -> str:
    rendered = ", ".join(f"{key}={_format_detail_value(value)}" for key, value in sorted(details.items()))
    if not rendered:
        return base_error
    return f"{base_error} [{rendered}]"


def _format_detail_value(value: Any) -> str:
    if isinstance(value, Mapping):
        return "{" + ", ".join(
            f"{_format_detail_value(k)}:{_format_detail_value(v)}"
            for k, v in sorted(value.items(), key=lambda item: str(item[0]))
        ) + "}"
    if isinstance(value, tuple):
        return "(" + ", ".join(_format_detail_value(item) for item in value) + ")"
    if isinstance(value, list):
        return "[" + ", ".join(_format_detail_value(item) for item in value) + "]"
    return str(value)


__all__ = [
    "SETTLEMENT_SIGNER_REGISTRY_SNAPSHOT_SCHEMA",
    "SettlementAttestationRegistryBindingResult",
    "SettlementSignerRegistrySnapshotLoadResult",
    "SettlementSignerRegistrySnapshotRequest",
    "SettlementSignerRegistrySnapshot",
    "InMemorySettlementSignerRegistrySnapshotLoader",
    "check_settlement_attestation_policy_registry_binding",
    "coerce_settlement_signer_registry_snapshot",
    "load_attestation_policy_and_registry_snapshot",
    "resolve_attestation_policy_and_registry_snapshot",
]
