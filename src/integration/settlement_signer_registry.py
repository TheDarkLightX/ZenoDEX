from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping
from urllib import error as urllib_error
from urllib import request as urllib_request

from src.state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

from .settlement_attestation_policy import (
    SettlementAttestationPolicy,
    coerce_settlement_attestation_policy,
)
from .tau_net_client import (
    TauNetAppStateView,
    TauNetRpcError,
    TauNetStateProofView,
    TauNetTauStateView,
    compute_tau_state_commitment_hash_hex,
)
from .tau_state_proof_binding import validate_tau_state_proof_binding

SETTLEMENT_SIGNER_REGISTRY_SNAPSHOT_SCHEMA = "zenodex/settlement-signer-registry-snapshot/v1"
SETTLEMENT_SIGNER_REGISTRY_ANCHOR_SCHEMA = "zenodex/settlement-signer-registry-anchor/v1"
SETTLEMENT_SIGNER_REGISTRY_INTERFACE_SCHEMA = "zenodex/settlement-signer-registry-interface/v1"
SETTLEMENT_SIGNER_REGISTRY_TAU_BRIDGE_SCHEMA = "zenodex/settlement-signer-registry-tau-bridge/v1"
_JSON_RPC_MAX_RESPONSE_BYTES = 1_048_576
_JSON_RPC_ERROR_BODY_PREVIEW_BYTES = 4096


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
class SettlementSignerRegistryAnchor:
    chain_id: int
    registry_contract: str
    policy_id: str
    policy_epoch: int
    registry_root: str
    policy_hash: str
    anchor_block_number: int
    anchor_block_hash: str
    schema: str = SETTLEMENT_SIGNER_REGISTRY_ANCHOR_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_SIGNER_REGISTRY_ANCHOR_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.policy_id, str) or not self.policy_id.strip():
            raise ValueError("policy_id must be a non-empty string")
        object.__setattr__(self, "policy_id", self.policy_id.strip())
        for name in ("chain_id", "policy_epoch", "anchor_block_number"):
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
            "policy_hash",
            canonical_hex_fixed_allow_0x(self.policy_hash, nbytes=32, name="policy_hash"),
        )
        object.__setattr__(
            self,
            "anchor_block_hash",
            canonical_hex_fixed_allow_0x(self.anchor_block_hash, nbytes=32, name="anchor_block_hash"),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "chain_id": int(self.chain_id),
            "registry_contract": self.registry_contract,
            "policy_id": self.policy_id,
            "policy_epoch": int(self.policy_epoch),
            "registry_root": self.registry_root,
            "policy_hash": self.policy_hash,
            "anchor_block_number": int(self.anchor_block_number),
            "anchor_block_hash": self.anchor_block_hash,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSignerRegistryAnchor":
        if not isinstance(payload, Mapping):
            raise ValueError("attestation_registry_anchor must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            chain_id=int(payload.get("chain_id", -1)),
            registry_contract=str(payload.get("registry_contract", "")),
            policy_id=str(payload.get("policy_id", "")),
            policy_epoch=int(payload.get("policy_epoch", -1)),
            registry_root=str(payload.get("registry_root", "")),
            policy_hash=str(payload.get("policy_hash", "")),
            anchor_block_number=int(payload.get("anchor_block_number", -1)),
            anchor_block_hash=str(payload.get("anchor_block_hash", "")),
        )


@dataclass(frozen=True)
class SettlementSignerRegistryContractInterface:
    interface_id: str
    chain_id: int
    registry_contract: str
    anchor_rpc_method: str
    schema: str = SETTLEMENT_SIGNER_REGISTRY_INTERFACE_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_SIGNER_REGISTRY_INTERFACE_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.interface_id, str) or not self.interface_id.strip():
            raise ValueError("interface_id must be a non-empty string")
        object.__setattr__(self, "interface_id", self.interface_id.strip())
        if not isinstance(self.chain_id, int) or isinstance(self.chain_id, bool) or self.chain_id < 0:
            raise ValueError("chain_id must be a non-negative int")
        object.__setattr__(
            self,
            "registry_contract",
            canonical_hex_fixed_allow_0x(self.registry_contract, nbytes=20, name="registry_contract"),
        )
        if not isinstance(self.anchor_rpc_method, str) or not self.anchor_rpc_method.strip():
            raise ValueError("anchor_rpc_method must be a non-empty string")
        object.__setattr__(self, "anchor_rpc_method", self.anchor_rpc_method.strip())

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "interface_id": self.interface_id,
            "chain_id": int(self.chain_id),
            "registry_contract": self.registry_contract,
            "anchor_rpc_method": self.anchor_rpc_method,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSignerRegistryContractInterface":
        if not isinstance(payload, Mapping):
            raise ValueError("settlement_signer_registry_interface must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            interface_id=str(payload.get("interface_id", "")),
            chain_id=int(payload.get("chain_id", -1)),
            registry_contract=str(payload.get("registry_contract", "")),
            anchor_rpc_method=str(payload.get("anchor_rpc_method", "")),
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


class InMemorySettlementSignerRegistryAnchorLoader:
    def __init__(self, anchors: Mapping[tuple[int, str, str, int], SettlementSignerRegistryAnchor | Mapping[str, Any]]):
        if not isinstance(anchors, Mapping):
            raise TypeError("anchors must be a mapping")
        normalized: dict[tuple[int, str, str, int], SettlementSignerRegistryAnchor] = {}
        for key, raw_anchor in anchors.items():
            if (
                not isinstance(key, tuple)
                or len(key) != 4
                or not isinstance(key[0], int)
                or not isinstance(key[1], str)
                or not isinstance(key[2], str)
                or not isinstance(key[3], int)
            ):
                raise TypeError("anchor loader keys must be (chain_id, registry_contract, policy_id, policy_epoch)")
            normalized_key = (
                int(key[0]),
                canonical_hex_fixed_allow_0x(key[1], nbytes=20, name="registry_contract"),
                str(key[2]).strip(),
                int(key[3]),
            )
            normalized[normalized_key] = coerce_settlement_signer_registry_anchor(raw_anchor)
        self._anchors = normalized

    def load_anchor(self, request: SettlementSignerRegistrySnapshotRequest) -> SettlementSignerRegistryAnchor | None:
        return self._anchors.get(
            (
                int(request.chain_id),
                request.registry_contract,
                request.policy_id,
                int(request.policy_epoch),
            )
        )


class JsonRpcSettlementSignerRegistryAnchorLoader:
    def __init__(
        self,
        endpoint_url: str,
        *,
        method: str = "zenodex_getSettlementSignerRegistryAnchor",
        interface: SettlementSignerRegistryContractInterface | Mapping[str, Any] | None = None,
        timeout_s: float = 5.0,
        headers: Mapping[str, str] | None = None,
        transport: object | None = None,
    ):
        if not isinstance(endpoint_url, str) or not endpoint_url.strip():
            raise ValueError("endpoint_url must be a non-empty string")
        normalized_endpoint = endpoint_url.strip()
        if not (normalized_endpoint.startswith("http://") or normalized_endpoint.startswith("https://")):
            raise ValueError("endpoint_url must start with http:// or https://")
        if not isinstance(method, str) or not method.strip():
            raise ValueError("method must be a non-empty string")
        if not isinstance(timeout_s, (int, float)) or isinstance(timeout_s, bool) or float(timeout_s) <= 0.0:
            raise ValueError("timeout_s must be a positive number")
        resolved_interface = coerce_settlement_signer_registry_contract_interface(interface)
        normalized_headers: dict[str, str] = {"Content-Type": "application/json"}
        if headers is not None:
            if not isinstance(headers, Mapping):
                raise TypeError("headers must be a mapping")
            for raw_key, raw_value in headers.items():
                if not isinstance(raw_key, str) or not raw_key.strip():
                    raise ValueError("header names must be non-empty strings")
                if not isinstance(raw_value, str):
                    raise TypeError("header values must be strings")
                normalized_headers[raw_key.strip()] = raw_value
        if transport is not None and not callable(transport):
            raise TypeError("transport must be callable")
        self._endpoint_url = normalized_endpoint
        self._method = resolved_interface.anchor_rpc_method if resolved_interface is not None else method.strip()
        self._interface = resolved_interface
        self._timeout_s = float(timeout_s)
        self._headers = dict(sorted(normalized_headers.items()))
        self._transport = transport

    def load_anchor(self, request: SettlementSignerRegistrySnapshotRequest) -> SettlementSignerRegistryAnchor | None:
        if self._interface is not None:
            _require_contract_interface_matches_request(
                interface=self._interface,
                request=request,
            )
        payload = {
            "jsonrpc": "2.0",
            "id": "settlement-signer-registry-anchor",
            "method": self._method,
            "params": request.to_dict(),
        }
        response = self._call(payload)
        if not isinstance(response, Mapping):
            raise ValueError(
                _format_binding_error(
                    "attestation registry json-rpc response must be an object",
                    details={
                        "endpoint_url": self._endpoint_url,
                        "method": self._method,
                        "response_type": type(response).__name__,
                    },
                )
            )
        rpc_error = response.get("error")
        if rpc_error is not None:
            if isinstance(rpc_error, Mapping):
                code = rpc_error.get("code")
                message = rpc_error.get("message")
                data = rpc_error.get("data")
                raise ValueError(
                    _format_binding_error(
                        "attestation registry json-rpc returned an error",
                        details={
                            "endpoint_url": self._endpoint_url,
                            "method": self._method,
                            "request": request.to_dict(),
                            "rpc_error_code": code,
                            "rpc_error_message": message,
                            "rpc_error_data": data,
                        },
                    )
                )
            raise ValueError(
                _format_binding_error(
                    "attestation registry json-rpc returned a non-object error",
                    details={
                        "endpoint_url": self._endpoint_url,
                        "method": self._method,
                        "request": request.to_dict(),
                        "rpc_error": rpc_error,
                    },
                )
            )
        result = response.get("result")
        if result is None:
            return None
        anchor = coerce_settlement_signer_registry_anchor(result)
        _require_anchor_matches_request(anchor=anchor, request=request)
        return anchor

    def _call(self, payload: Mapping[str, Any]) -> Any:
        if self._transport is not None:
            return self._transport(
                self._endpoint_url,
                dict(self._headers),
                dict(payload),
                self._timeout_s,
            )
        return _json_rpc_post_json(
            endpoint_url=self._endpoint_url,
            headers=self._headers,
            payload=payload,
            timeout_s=self._timeout_s,
        )


class ChainAnchoredSettlementSignerRegistrySnapshotLoader:
    def __init__(self, *, anchor_loader: object, snapshot_loader: object):
        load_anchor = getattr(anchor_loader, "load_anchor", None)
        if not callable(load_anchor):
            raise TypeError("anchor_loader must define load_anchor(request)")
        load_snapshot = getattr(snapshot_loader, "load_snapshot", None)
        if not callable(load_snapshot):
            raise TypeError("snapshot_loader must define load_snapshot(request)")
        self._anchor_loader = anchor_loader
        self._snapshot_loader = snapshot_loader

    def load_snapshot(self, request: SettlementSignerRegistrySnapshotRequest) -> SettlementSignerRegistrySnapshot | None:
        anchor = self._anchor_loader.load_anchor(request)
        if anchor is None:
            raise ValueError(
                _format_binding_error(
                    "attestation registry anchor loader returned no anchor",
                    details=request.to_dict(),
                )
            )
        anchor = coerce_settlement_signer_registry_anchor(anchor)
        _require_anchor_matches_request(anchor=anchor, request=request)
        raw_snapshot = self._snapshot_loader.load_snapshot(request)
        if raw_snapshot is None:
            raise ValueError(
                _format_binding_error(
                    "attestation registry snapshot source returned no snapshot",
                    details={**request.to_dict(), **anchor.to_dict()},
                )
            )
        snapshot = coerce_settlement_signer_registry_snapshot(raw_snapshot)
        _require_snapshot_matches_anchor(snapshot=snapshot, anchor=anchor)
        return SettlementSignerRegistrySnapshot(
            chain_id=int(anchor.chain_id),
            registry_contract=anchor.registry_contract,
            registry_root=anchor.registry_root,
            snapshot_block_number=int(anchor.anchor_block_number),
            snapshot_block_hash=anchor.anchor_block_hash,
            policy=snapshot.policy,
        )


class TauNetSettlementSignerRegistrySnapshotLoader:
    def __init__(
        self,
        tau_client: object,
        *,
        bridge_key: str = "settlement_signer_registry_tau_bridge",
        require_state_proof: bool = True,
        require_tau_state_app_hash_binding: bool = False,
        stable_read_attempts: int = 3,
    ):
        getappstate_view = getattr(tau_client, "getappstate_view", None)
        if not callable(getappstate_view):
            raise TypeError("tau_client must define getappstate_view()")
        getstateproof_view = getattr(tau_client, "getstateproof_view", None)
        if require_state_proof and not callable(getstateproof_view):
            raise TypeError("tau_client must define getstateproof_view() when require_state_proof is enabled")
        gettaustate_view = getattr(tau_client, "gettaustate_view", None)
        if require_tau_state_app_hash_binding and not callable(gettaustate_view):
            raise TypeError("tau_client must define gettaustate_view(state_hash) when Tau state app-hash binding is enabled")
        if not isinstance(bridge_key, str) or not bridge_key.strip():
            raise ValueError("bridge_key must be a non-empty string")
        if not isinstance(require_state_proof, bool):
            raise TypeError("require_state_proof must be a bool")
        if not isinstance(require_tau_state_app_hash_binding, bool):
            raise TypeError("require_tau_state_app_hash_binding must be a bool")
        if (
            not isinstance(stable_read_attempts, int)
            or isinstance(stable_read_attempts, bool)
            or stable_read_attempts <= 0
        ):
            raise ValueError("stable_read_attempts must be a positive int")
        if require_tau_state_app_hash_binding and not require_state_proof:
            raise ValueError("require_tau_state_app_hash_binding requires require_state_proof=True")
        self._tau_client = tau_client
        self._bridge_key = bridge_key.strip()
        self._require_state_proof = require_state_proof
        self._require_tau_state_app_hash_binding = require_tau_state_app_hash_binding
        self._stable_read_attempts = int(stable_read_attempts)

    def load_snapshot(self, request: SettlementSignerRegistrySnapshotRequest) -> SettlementSignerRegistrySnapshot | None:
        app_state_view, state_proof_view, tau_state_view = self._load_stable_tau_bridge_views(request)
        bridge_obj = app_state_view.app_state.get(self._bridge_key)
        if bridge_obj is None:
            raise ValueError(
                _format_binding_error(
                    "Tau app_state is missing settlement signer registry bridge payload",
                    details={
                        **request.to_dict(),
                        "tau_app_hash": app_state_view.app_hash,
                        "bridge_key": self._bridge_key,
                    },
                )
            )
        if not isinstance(bridge_obj, Mapping):
            raise ValueError(
                _format_binding_error(
                    "Tau settlement signer registry bridge payload must be an object",
                    details={
                        **request.to_dict(),
                        "tau_app_hash": app_state_view.app_hash,
                        "bridge_key": self._bridge_key,
                        "bridge_type": type(bridge_obj).__name__,
                    },
                )
            )
        bridge_schema = bridge_obj.get("schema")
        if bridge_schema != SETTLEMENT_SIGNER_REGISTRY_TAU_BRIDGE_SCHEMA:
            raise ValueError(
                _format_binding_error(
                    "Tau settlement signer registry bridge schema mismatch",
                    details={
                        **request.to_dict(),
                        "tau_app_hash": app_state_view.app_hash,
                        "bridge_key": self._bridge_key,
                        "observed_schema": bridge_schema,
                        "expected_schema": SETTLEMENT_SIGNER_REGISTRY_TAU_BRIDGE_SCHEMA,
                    },
                )
            )
        anchor = coerce_settlement_signer_registry_anchor(bridge_obj.get("anchor"))
        snapshot = coerce_settlement_signer_registry_snapshot(bridge_obj.get("snapshot"))
        if snapshot is None:
            raise ValueError(
                _format_binding_error(
                    "Tau settlement signer registry bridge is missing snapshot payload",
                    details={
                        **request.to_dict(),
                        "tau_app_hash": app_state_view.app_hash,
                        "bridge_key": self._bridge_key,
                    },
                )
        )
        _require_anchor_matches_request(anchor=anchor, request=request)
        _require_snapshot_matches_anchor(snapshot=snapshot, anchor=anchor)
        if self._require_state_proof:
            state_proof_view = _require_tau_state_proof_view(
                state_proof_view=state_proof_view,
                request=request,
                app_state_view=app_state_view,
                bridge_key=self._bridge_key,
            )
            if not state_proof_view.present:
                raise ValueError(
                    _format_binding_error(
                        "Tau state proof missing for settlement signer registry bridge",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": state_proof_view.state_hash,
                            "bridge_key": self._bridge_key,
                        },
                    )
                )
            if state_proof_view.error:
                raise ValueError(
                    _format_binding_error(
                        "Tau state proof surface reported an error for settlement signer registry bridge",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": state_proof_view.state_hash,
                            "tau_state_proof_error": state_proof_view.error,
                            "tau_state_proof_type": state_proof_view.proof_type,
                            "bridge_key": self._bridge_key,
                        },
                    )
                )
        if self._require_tau_state_app_hash_binding:
            state_proof_view = _require_tau_state_proof_view(
                state_proof_view=state_proof_view,
                request=request,
                app_state_view=app_state_view,
                bridge_key=self._bridge_key,
            )
            tau_state_view = _require_tau_state_view(
                tau_state_view=tau_state_view,
                request=request,
                app_state_view=app_state_view,
                state_proof_view=state_proof_view,
                bridge_key=self._bridge_key,
            )
            try:
                computed_tau_state_hash = compute_tau_state_commitment_hash_hex(
                    rules=tau_state_view.rules,
                    accounts_hash=tau_state_view.accounts_hash,
                    app_hash=tau_state_view.app_hash,
                )
            except TauNetRpcError as exc:
                raise ValueError(
                    _format_binding_error(
                        "Tau state snapshot could not be validated against committed state_hash for settlement signer registry bridge",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": tau_state_view.state_hash,
                            "tau_state_validation_error": str(exc),
                            "bridge_key": self._bridge_key,
                        },
                    )
                ) from exc
            if computed_tau_state_hash != state_proof_view.state_hash:
                raise ValueError(
                    _format_binding_error(
                        "Tau state snapshot does not hash to committed state_hash for settlement signer registry bridge",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": tau_state_view.state_hash,
                            "tau_state_committed_hash": state_proof_view.state_hash,
                            "tau_state_computed_hash": computed_tau_state_hash,
                            "bridge_key": self._bridge_key,
                        },
                    )
                )
            if not tau_state_view.app_hash:
                raise ValueError(
                    _format_binding_error(
                        "Tau state snapshot is missing app_hash for settlement signer registry bridge",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": tau_state_view.state_hash,
                            "bridge_key": self._bridge_key,
                        },
                    )
                )
            if tau_state_view.app_hash != app_state_view.app_hash:
                raise ValueError(
                    _format_binding_error(
                        "Tau state snapshot app_hash does not match committed app_state hash for settlement signer registry bridge",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": tau_state_view.state_hash,
                            "tau_state_app_hash": tau_state_view.app_hash,
                            "bridge_key": self._bridge_key,
                        },
                    )
                )
            binding_ok, binding_error = validate_tau_state_proof_binding(
                state_proof={
                    "present": state_proof_view.present,
                    "state_hash": state_proof_view.state_hash,
                },
                committed_state_hash=state_proof_view.state_hash,
                committed_app_hash=app_state_view.app_hash,
                tau_state={"app_hash": tau_state_view.app_hash},
            )
            if not binding_ok:
                raise ValueError(
                    _format_binding_error(
                        f"Tau state proof binding invalid for settlement signer registry bridge: {binding_error}",
                        details={
                            **request.to_dict(),
                            "tau_app_hash": app_state_view.app_hash,
                            "tau_state_hash": tau_state_view.state_hash,
                            "bridge_key": self._bridge_key,
                        },
                    )
                )
        return SettlementSignerRegistrySnapshot(
            chain_id=int(anchor.chain_id),
            registry_contract=anchor.registry_contract,
            registry_root=anchor.registry_root,
            snapshot_block_number=int(anchor.anchor_block_number),
            snapshot_block_hash=anchor.anchor_block_hash,
            policy=snapshot.policy,
        )

    def _load_stable_tau_bridge_views(
        self,
        request: SettlementSignerRegistrySnapshotRequest,
    ) -> tuple[TauNetAppStateView, TauNetStateProofView | None, TauNetTauStateView | None]:
        if not self._require_state_proof:
            app_state_view = self._tau_client.getappstate_view()
            _require_tau_app_state_view(app_state_view=app_state_view, request=request)
            return app_state_view, None, None

        last_before: TauNetStateProofView | None = None
        last_after: TauNetStateProofView | None = None
        last_app_state_before: TauNetAppStateView | None = None
        last_app_state_after: TauNetAppStateView | None = None
        last_tau_state_before: TauNetTauStateView | None = None
        last_tau_state_after: TauNetTauStateView | None = None
        for _attempt in range(1, self._stable_read_attempts + 1):
            state_proof_before = self._tau_client.getstateproof_view()
            if not isinstance(state_proof_before, TauNetStateProofView):
                raise TypeError("tau_client.getstateproof_view() must return TauNetStateProofView")
            tau_state_before: TauNetTauStateView | None = None
            if self._require_tau_state_app_hash_binding:
                if not state_proof_before.state_hash:
                    raise ValueError(
                        _format_binding_error(
                            "Tau state proof surface did not expose state_hash for Tau state app-hash binding",
                            details={
                                **request.to_dict(),
                                "state_proof_before": _tau_state_proof_view_details(state_proof_before),
                            },
                        )
                    )
                tau_state_before = self._tau_client.gettaustate_view(state_proof_before.state_hash)
                if not isinstance(tau_state_before, TauNetTauStateView):
                    raise TypeError("tau_client.gettaustate_view() must return TauNetTauStateView")
            app_state_before = self._tau_client.getappstate_view()
            _require_tau_app_state_view(app_state_view=app_state_before, request=request)
            app_state_after = self._tau_client.getappstate_view()
            _require_tau_app_state_view(app_state_view=app_state_after, request=request)
            state_proof_after = self._tau_client.getstateproof_view()
            if not isinstance(state_proof_after, TauNetStateProofView):
                raise TypeError("tau_client.getstateproof_view() must return TauNetStateProofView")
            tau_state_after: TauNetTauStateView | None = None
            if self._require_tau_state_app_hash_binding:
                if not state_proof_after.state_hash:
                    raise ValueError(
                        _format_binding_error(
                            "Tau state proof surface did not expose state_hash for Tau state app-hash binding",
                            details={
                                **request.to_dict(),
                                "state_proof_after": _tau_state_proof_view_details(state_proof_after),
                            },
                        )
                    )
                tau_state_after = self._tau_client.gettaustate_view(state_proof_after.state_hash)
                if not isinstance(tau_state_after, TauNetTauStateView):
                    raise TypeError("tau_client.gettaustate_view() must return TauNetTauStateView")
            last_before = state_proof_before
            last_after = state_proof_after
            last_app_state_before = app_state_before
            last_app_state_after = app_state_after
            last_tau_state_before = tau_state_before
            last_tau_state_after = tau_state_after
            stable_state_views = state_proof_before == state_proof_after and app_state_before == app_state_after
            if self._require_tau_state_app_hash_binding:
                stable_state_views = stable_state_views and tau_state_before == tau_state_after
            if stable_state_views:
                return app_state_before, state_proof_before, tau_state_before
        raise ValueError(
            _format_binding_error(
                "Tau bridge views changed during settlement signer registry bridge load",
                details={
                    **request.to_dict(),
                    "tau_app_hash": "" if last_app_state_before is None else last_app_state_before.app_hash,
                    "stable_read_attempts": self._stable_read_attempts,
                    "app_state_before": None if last_app_state_before is None else _tau_app_state_view_details(last_app_state_before),
                    "app_state_after": None if last_app_state_after is None else _tau_app_state_view_details(last_app_state_after),
                    "state_proof_before": None if last_before is None else _tau_state_proof_view_details(last_before),
                    "state_proof_after": None if last_after is None else _tau_state_proof_view_details(last_after),
                    "tau_state_before": None if last_tau_state_before is None else _tau_tau_state_view_details(last_tau_state_before),
                    "tau_state_after": None if last_tau_state_after is None else _tau_tau_state_view_details(last_tau_state_after),
                },
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


def coerce_settlement_signer_registry_anchor(
    anchor: SettlementSignerRegistryAnchor | Mapping[str, Any],
) -> SettlementSignerRegistryAnchor:
    if isinstance(anchor, SettlementSignerRegistryAnchor):
        return anchor
    if isinstance(anchor, Mapping):
        return SettlementSignerRegistryAnchor.from_dict(anchor)
    raise TypeError("attestation_registry_anchor must be a SettlementSignerRegistryAnchor or object mapping")


def coerce_settlement_signer_registry_contract_interface(
    interface: SettlementSignerRegistryContractInterface | Mapping[str, Any] | None,
) -> SettlementSignerRegistryContractInterface | None:
    if interface is None:
        return None
    if isinstance(interface, SettlementSignerRegistryContractInterface):
        return interface
    if isinstance(interface, Mapping):
        return SettlementSignerRegistryContractInterface.from_dict(interface)
    raise TypeError(
        "settlement_signer_registry_interface must be a SettlementSignerRegistryContractInterface or object mapping"
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


def _tau_state_proof_view_details(view: TauNetStateProofView) -> dict[str, Any]:
    return {
        "state_hash": view.state_hash,
        "present": bool(view.present),
        "proof_type": view.proof_type,
        "proof_bytes": view.proof_bytes,
        "proof_sha256": view.proof_sha256,
        "error": view.error,
    }

def _tau_app_state_view_details(view: TauNetAppStateView) -> dict[str, Any]:
    return {
        "app_hash": view.app_hash,
        "app_state": view.app_state,
    }


def _tau_tau_state_view_details(view: TauNetTauStateView) -> dict[str, Any]:
    return {
        "state_hash": view.state_hash,
        "rules": view.rules,
        "accounts_hash": view.accounts_hash,
        "app_hash": view.app_hash,
    }


def _require_tau_app_state_view(
    *,
    app_state_view: TauNetAppStateView,
    request: SettlementSignerRegistrySnapshotRequest,
) -> None:
    if not isinstance(app_state_view, TauNetAppStateView):
        raise TypeError("tau_client.getappstate_view() must return TauNetAppStateView")
    if not app_state_view.app_hash:
        raise ValueError(
            _format_binding_error(
                "Tau app_state hash missing for settlement signer registry bridge",
                details=request.to_dict(),
            )
        )
    if not isinstance(app_state_view.app_state, Mapping):
        raise ValueError(
            _format_binding_error(
                "Tau app_state must be an object to load settlement signer registry bridge",
                details={**request.to_dict(), "tau_app_hash": app_state_view.app_hash},
            )
        )
    observed_app_hash = hashlib.sha256(canonical_json_bytes(app_state_view.app_state)).hexdigest()
    if observed_app_hash != app_state_view.app_hash:
        raise ValueError(
            _format_binding_error(
                "Tau app_state does not hash to the committed app_hash for settlement signer registry bridge",
                details={
                    **request.to_dict(),
                    "tau_app_hash": app_state_view.app_hash,
                    "observed_app_hash": observed_app_hash,
                },
            )
        )


def _require_tau_state_proof_view(
    *,
    state_proof_view: TauNetStateProofView | None,
    request: SettlementSignerRegistrySnapshotRequest,
    app_state_view: TauNetAppStateView,
    bridge_key: str,
) -> TauNetStateProofView:
    if state_proof_view is None:
        raise ValueError(
            _format_binding_error(
                "Tau state proof view missing for settlement signer registry bridge",
                details={
                    **request.to_dict(),
                    "tau_app_hash": app_state_view.app_hash,
                    "bridge_key": bridge_key,
                },
            )
        )
    return state_proof_view


def _require_tau_state_view(
    *,
    tau_state_view: TauNetTauStateView | None,
    request: SettlementSignerRegistrySnapshotRequest,
    app_state_view: TauNetAppStateView,
    state_proof_view: TauNetStateProofView,
    bridge_key: str,
) -> TauNetTauStateView:
    if tau_state_view is None:
        raise ValueError(
            _format_binding_error(
                "Tau state snapshot view missing for settlement signer registry bridge",
                details={
                    **request.to_dict(),
                    "tau_app_hash": app_state_view.app_hash,
                    "tau_state_hash": state_proof_view.state_hash,
                    "bridge_key": bridge_key,
                },
            )
        )
    return tau_state_view


def _require_anchor_matches_request(
    *,
    anchor: SettlementSignerRegistryAnchor,
    request: SettlementSignerRegistrySnapshotRequest,
) -> None:
    details = {
        "request_chain_id": int(request.chain_id),
        "request_registry_contract": request.registry_contract,
        "request_policy_id": request.policy_id,
        "request_policy_epoch": int(request.policy_epoch),
        "request_registry_root_hint": request.registry_root_hint,
        "request_policy_hash_hint": request.policy_hash_hint,
        "anchor_chain_id": int(anchor.chain_id),
        "anchor_registry_contract": anchor.registry_contract,
        "anchor_policy_id": anchor.policy_id,
        "anchor_policy_epoch": int(anchor.policy_epoch),
        "anchor_registry_root": anchor.registry_root,
        "anchor_policy_hash": anchor.policy_hash,
        "anchor_block_number": int(anchor.anchor_block_number),
        "anchor_block_hash": anchor.anchor_block_hash,
    }
    if int(anchor.chain_id) != int(request.chain_id):
        raise ValueError(
            _format_binding_error(
                "attestation registry anchor chain_id does not match request",
                details=details,
            )
        )
    if anchor.registry_contract != request.registry_contract:
        raise ValueError(
            _format_binding_error(
                "attestation registry anchor registry_contract does not match request",
                details=details,
            )
        )
    if anchor.policy_id != request.policy_id:
        raise ValueError(
            _format_binding_error(
                "attestation registry anchor policy_id does not match request",
                details=details,
            )
        )
    if int(anchor.policy_epoch) != int(request.policy_epoch):
        raise ValueError(
            _format_binding_error(
                "attestation registry anchor policy_epoch does not match request",
                details=details,
            )
        )
    if anchor.registry_root != request.registry_root_hint:
        raise ValueError(
            _format_binding_error(
                "attestation registry anchor registry_root does not match request hint",
                details=details,
            )
        )
    if anchor.policy_hash != request.policy_hash_hint:
        raise ValueError(
            _format_binding_error(
                "attestation registry anchor policy_hash does not match request hint",
                details=details,
            )
        )


def _require_contract_interface_matches_request(
    *,
    interface: SettlementSignerRegistryContractInterface,
    request: SettlementSignerRegistrySnapshotRequest,
) -> None:
    details = {
        "interface_id": interface.interface_id,
        "interface_chain_id": int(interface.chain_id),
        "interface_registry_contract": interface.registry_contract,
        "interface_anchor_rpc_method": interface.anchor_rpc_method,
        "request_chain_id": int(request.chain_id),
        "request_registry_contract": request.registry_contract,
        "request_policy_id": request.policy_id,
        "request_policy_epoch": int(request.policy_epoch),
    }
    if int(interface.chain_id) != int(request.chain_id):
        raise ValueError(
            _format_binding_error(
                "attestation registry interface chain_id does not match request",
                details=details,
            )
        )
    if interface.registry_contract != request.registry_contract:
        raise ValueError(
            _format_binding_error(
                "attestation registry interface registry_contract does not match request",
                details=details,
            )
        )


def _require_snapshot_matches_anchor(
    *,
    snapshot: SettlementSignerRegistrySnapshot,
    anchor: SettlementSignerRegistryAnchor,
) -> None:
    details = {
        "anchor_chain_id": int(anchor.chain_id),
        "anchor_registry_contract": anchor.registry_contract,
        "anchor_policy_id": anchor.policy_id,
        "anchor_policy_epoch": int(anchor.policy_epoch),
        "anchor_registry_root": anchor.registry_root,
        "anchor_policy_hash": anchor.policy_hash,
        "snapshot_chain_id": int(snapshot.chain_id),
        "snapshot_registry_contract": snapshot.registry_contract,
        "snapshot_policy_id": snapshot.policy.policy_id,
        "snapshot_policy_epoch": int(snapshot.policy.policy_epoch),
        "snapshot_registry_root": snapshot.registry_root,
        "snapshot_policy_hash": snapshot.policy.policy_hash_hex(),
        "snapshot_block_number": int(snapshot.snapshot_block_number),
        "snapshot_block_hash": snapshot.snapshot_block_hash,
    }
    if int(snapshot.chain_id) != int(anchor.chain_id):
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot chain_id does not match chain anchor",
                details=details,
            )
        )
    if snapshot.registry_contract != anchor.registry_contract:
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot registry_contract does not match chain anchor",
                details=details,
            )
        )
    if snapshot.policy.policy_id != anchor.policy_id:
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot policy_id does not match chain anchor",
                details=details,
            )
        )
    if int(snapshot.policy.policy_epoch) != int(anchor.policy_epoch):
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot policy_epoch does not match chain anchor",
                details=details,
            )
        )
    if snapshot.registry_root != anchor.registry_root:
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot registry_root does not match chain anchor",
                details=details,
            )
        )
    if snapshot.policy.policy_hash_hex() != anchor.policy_hash:
        raise ValueError(
            _format_binding_error(
                "attestation registry snapshot policy content does not match chain anchor",
                details=details,
            )
        )


def _json_rpc_post_json(
    *,
    endpoint_url: str,
    headers: Mapping[str, str],
    payload: Mapping[str, Any],
    timeout_s: float,
) -> Any:
    body = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    req = urllib_request.Request(endpoint_url, data=body, method="POST")
    for key, value in headers.items():
        req.add_header(key, value)
    try:
        with urllib_request.urlopen(req, timeout=timeout_s) as resp:
            raw = _read_json_rpc_response_body(resp, endpoint_url=endpoint_url)
    except urllib_error.HTTPError as exc:
        try:
            raw = _read_json_rpc_response_body(exc, endpoint_url=endpoint_url)
        except ValueError as read_exc:
            raise read_exc from exc
        raise ValueError(
            _format_binding_error(
                "attestation registry json-rpc endpoint returned HTTP error",
                details={
                    "endpoint_url": endpoint_url,
                    "status": int(exc.code),
                    "body": _json_rpc_body_preview(raw),
                },
            )
        ) from exc
    except urllib_error.URLError as exc:
        raise ValueError(
            _format_binding_error(
                "attestation registry json-rpc request failed",
                details={
                    "endpoint_url": endpoint_url,
                    "reason": exc.reason,
                },
            )
        ) from exc
    except OSError as exc:
        raise ValueError(
            _format_binding_error(
                "attestation registry json-rpc transport failed",
                details={
                    "endpoint_url": endpoint_url,
                    "reason": str(exc),
                },
            )
        ) from exc
    try:
        return json.loads(raw.decode("utf-8"))
    except Exception as exc:
        raise ValueError(
            _format_binding_error(
                "attestation registry json-rpc response is not valid json",
                details={
                    "endpoint_url": endpoint_url,
                    "body": _json_rpc_body_preview(raw),
                },
            )
        ) from exc


def _read_json_rpc_response_body(response: Any, *, endpoint_url: str) -> bytes:
    raw = response.read(_JSON_RPC_MAX_RESPONSE_BYTES + 1)
    if len(raw) > _JSON_RPC_MAX_RESPONSE_BYTES:
        raise ValueError(
            _format_binding_error(
                "attestation registry json-rpc response exceeds size limit",
                details={
                    "endpoint_url": endpoint_url,
                    "max_response_bytes": _JSON_RPC_MAX_RESPONSE_BYTES,
                },
            )
        )
    return raw


def _json_rpc_body_preview(raw: bytes) -> str:
    preview = raw[:_JSON_RPC_ERROR_BODY_PREVIEW_BYTES].decode("utf-8", "replace")
    if len(raw) > _JSON_RPC_ERROR_BODY_PREVIEW_BYTES:
        return f"{preview}...<truncated>"
    return preview


__all__ = [
    "SETTLEMENT_SIGNER_REGISTRY_ANCHOR_SCHEMA",
    "SETTLEMENT_SIGNER_REGISTRY_INTERFACE_SCHEMA",
    "SETTLEMENT_SIGNER_REGISTRY_SNAPSHOT_SCHEMA",
    "SettlementAttestationRegistryBindingResult",
    "SettlementSignerRegistryAnchor",
    "SettlementSignerRegistryContractInterface",
    "SettlementSignerRegistrySnapshotLoadResult",
    "SettlementSignerRegistrySnapshotRequest",
    "SettlementSignerRegistrySnapshot",
    "ChainAnchoredSettlementSignerRegistrySnapshotLoader",
    "InMemorySettlementSignerRegistryAnchorLoader",
    "InMemorySettlementSignerRegistrySnapshotLoader",
    "JsonRpcSettlementSignerRegistryAnchorLoader",
    "check_settlement_attestation_policy_registry_binding",
    "coerce_settlement_signer_registry_anchor",
    "coerce_settlement_signer_registry_contract_interface",
    "coerce_settlement_signer_registry_snapshot",
    "load_attestation_policy_and_registry_snapshot",
    "resolve_attestation_policy_and_registry_snapshot",
]
