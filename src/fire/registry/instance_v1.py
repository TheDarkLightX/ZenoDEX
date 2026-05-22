from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Mapping, Sequence

from src.fire.registry.object_manifest_v1 import FireObjectManifest
from src.fire.verifier.cert_v1 import _require_sha256_prefixed


INSTANCE_SCHEMA = "zenodex/fire-object-instance/v1"


def _require_nonempty_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(dict(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def fire_object_instance_sha256(payload_without_hash: Mapping[str, object]) -> str:
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(payload_without_hash)).hexdigest()


def fire_object_instance_file_sha256(instance: "FireObjectInstanceManifest") -> str:
    return fire_object_instance_sha256(instance.to_dict())


def _parse_iso_timestamp(name: str, value: str) -> datetime:
    normalized = value.replace("Z", "+00:00")
    try:
        parsed = datetime.fromisoformat(normalized)
    except ValueError as exc:
        raise ValueError(f"{name} must be an ISO-8601 timestamp") from exc
    if parsed.tzinfo is None:
        raise ValueError(f"{name} must include timezone information")
    return parsed


@dataclass(frozen=True)
class FireObjectParameterValue:
    name: str
    value: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "name", _require_nonempty_str("name", self.name))
        object.__setattr__(self, "value", _require_int("value", self.value))

    def to_dict(self) -> dict[str, object]:
        return {"name": self.name, "value": self.value}

    @classmethod
    def from_dict(cls, payload: object) -> "FireObjectParameterValue":
        if not isinstance(payload, dict):
            raise TypeError("parameter payload must be an object")
        return cls(name=payload.get("name"), value=payload.get("value"))


@dataclass(frozen=True)
class FireObjectPartyBinding:
    role: str
    party_id: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "role", _require_nonempty_str("role", self.role))
        object.__setattr__(self, "party_id", _require_nonempty_str("party_id", self.party_id))

    def to_dict(self) -> dict[str, object]:
        return {"role": self.role, "party_id": self.party_id}

    @classmethod
    def from_dict(cls, payload: object) -> "FireObjectPartyBinding":
        if not isinstance(payload, dict):
            raise TypeError("party binding payload must be an object")
        return cls(role=payload.get("role"), party_id=payload.get("party_id"))


@dataclass(frozen=True)
class FireSettlementWindow:
    start: str
    end: str

    def __post_init__(self) -> None:
        object.__setattr__(self, "start", _require_nonempty_str("start", self.start))
        object.__setattr__(self, "end", _require_nonempty_str("end", self.end))

    def to_dict(self) -> dict[str, object]:
        return {"start": self.start, "end": self.end}

    @classmethod
    def from_dict(cls, payload: object) -> "FireSettlementWindow":
        if not isinstance(payload, dict):
            raise TypeError("settlement_window payload must be an object")
        return cls(start=payload.get("start"), end=payload.get("end"))


@dataclass(frozen=True)
class FireObjectInstanceManifest:
    object_hash: str
    lock_hash: str
    object_name: str
    object_version: str
    object_family: str
    parameters: tuple[FireObjectParameterValue, ...]
    parties: tuple[FireObjectPartyBinding, ...]
    nonce: str
    instance_hash: str
    maturity: str | None = None
    settlement_window: FireSettlementWindow | None = None
    schema: str = INSTANCE_SCHEMA

    def __post_init__(self) -> None:
        object.__setattr__(self, "object_hash", _require_sha256_prefixed("object_hash", self.object_hash))
        object.__setattr__(self, "lock_hash", _require_sha256_prefixed("lock_hash", self.lock_hash))
        object.__setattr__(self, "object_name", _require_nonempty_str("object_name", self.object_name))
        object.__setattr__(self, "object_version", _require_nonempty_str("object_version", self.object_version))
        object.__setattr__(self, "object_family", _require_nonempty_str("object_family", self.object_family))
        object.__setattr__(self, "nonce", _require_nonempty_str("nonce", self.nonce))
        object.__setattr__(self, "instance_hash", _require_sha256_prefixed("instance_hash", self.instance_hash))
        if self.maturity is not None:
            object.__setattr__(self, "maturity", _require_nonempty_str("maturity", self.maturity))
            _parse_iso_timestamp("maturity", self.maturity)
        if self.schema != INSTANCE_SCHEMA:
            raise ValueError(f"unsupported instance schema: {self.schema}")
        if not isinstance(self.parameters, tuple):
            raise TypeError("parameters must be a tuple")
        if any(not isinstance(item, FireObjectParameterValue) for item in self.parameters):
            raise TypeError("parameters must contain FireObjectParameterValue values")
        if not isinstance(self.parties, tuple):
            raise TypeError("parties must be a tuple")
        if any(not isinstance(item, FireObjectPartyBinding) for item in self.parties):
            raise TypeError("parties must contain FireObjectPartyBinding values")
        if self.settlement_window is not None and not isinstance(self.settlement_window, FireSettlementWindow):
            raise TypeError("settlement_window must be a FireSettlementWindow")
        if self.settlement_window is not None:
            start = _parse_iso_timestamp("settlement_window.start", self.settlement_window.start)
            end = _parse_iso_timestamp("settlement_window.end", self.settlement_window.end)
            if start > end:
                raise ValueError("settlement_window must be ordered")
        parameter_names = [item.name for item in self.parameters]
        if len(parameter_names) != len(set(parameter_names)):
            raise ValueError("duplicate parameter names")
        party_roles = [item.role for item in self.parties]
        if len(party_roles) != len(set(party_roles)):
            raise ValueError("duplicate party roles")

    def payload_without_hash(self) -> dict[str, object]:
        payload: dict[str, object] = {
            "schema": self.schema,
            "object_hash": self.object_hash,
            "lock_hash": self.lock_hash,
            "object_name": self.object_name,
            "object_version": self.object_version,
            "object_family": self.object_family,
            "parameters": [item.to_dict() for item in self.parameters],
            "parties": [item.to_dict() for item in self.parties],
            "nonce": self.nonce,
        }
        if self.maturity is not None:
            payload["maturity"] = self.maturity
        if self.settlement_window is not None:
            payload["settlement_window"] = self.settlement_window.to_dict()
        return payload

    def to_dict(self) -> dict[str, object]:
        payload = self.payload_without_hash()
        payload["instance_hash"] = self.instance_hash
        return payload

    @classmethod
    def build(
        cls,
        *,
        object_hash: str,
        lock_hash: str,
        object_name: str,
        object_version: str,
        object_family: str,
        parameters: Sequence[FireObjectParameterValue],
        parties: Sequence[FireObjectPartyBinding],
        nonce: str,
        maturity: str | None = None,
        settlement_window: FireSettlementWindow | None = None,
    ) -> "FireObjectInstanceManifest":
        parameter_items = tuple(sorted(parameters, key=lambda item: item.name))
        party_items = tuple(sorted(parties, key=lambda item: item.role))
        payload_without_hash: dict[str, object] = {
            "schema": INSTANCE_SCHEMA,
            "object_hash": object_hash,
            "lock_hash": lock_hash,
            "object_name": object_name,
            "object_version": object_version,
            "object_family": object_family,
            "parameters": [item.to_dict() for item in parameter_items],
            "parties": [item.to_dict() for item in party_items],
            "nonce": nonce,
        }
        if maturity is not None:
            payload_without_hash["maturity"] = maturity
        if settlement_window is not None:
            payload_without_hash["settlement_window"] = settlement_window.to_dict()
        return cls(
            object_hash=object_hash,
            lock_hash=lock_hash,
            object_name=object_name,
            object_version=object_version,
            object_family=object_family,
            parameters=parameter_items,
            parties=party_items,
            nonce=nonce,
            maturity=maturity,
            settlement_window=settlement_window,
            instance_hash=fire_object_instance_sha256(payload_without_hash),
        )

    @classmethod
    def from_dict(cls, payload: object) -> "FireObjectInstanceManifest":
        if not isinstance(payload, dict):
            raise TypeError("instance payload must be an object")
        parameters = payload.get("parameters")
        parties = payload.get("parties")
        if not isinstance(parameters, list):
            raise TypeError("parameters must be a list")
        if not isinstance(parties, list):
            raise TypeError("parties must be a list")
        settlement_window = payload.get("settlement_window")
        return cls(
            schema=payload.get("schema", INSTANCE_SCHEMA),
            object_hash=payload.get("object_hash"),
            lock_hash=payload.get("lock_hash"),
            object_name=payload.get("object_name"),
            object_version=payload.get("object_version"),
            object_family=payload.get("object_family"),
            parameters=tuple(FireObjectParameterValue.from_dict(item) for item in parameters),
            parties=tuple(FireObjectPartyBinding.from_dict(item) for item in parties),
            nonce=payload.get("nonce"),
            maturity=payload.get("maturity"),
            settlement_window=None if settlement_window is None else FireSettlementWindow.from_dict(settlement_window),
            instance_hash=payload.get("instance_hash"),
        )


@dataclass(frozen=True)
class FireInstanceGateReport:
    param_ok: bool
    authorization_ok: bool
    nonce_ok: bool
    maturity_ok: bool
    window_ok: bool
    ok: bool
    error: str | None = None

    def to_dict(self) -> dict[str, object]:
        return {
            "param_ok": self.param_ok,
            "authorization_ok": self.authorization_ok,
            "nonce_ok": self.nonce_ok,
            "maturity_ok": self.maturity_ok,
            "window_ok": self.window_ok,
            "ok": self.ok,
            "error": self.error,
        }


def verify_fire_object_instance(
    instance: FireObjectInstanceManifest,
    *,
    expected_object_hash: str,
    expected_lock_hash: str,
) -> tuple[bool, str | None]:
    if instance.object_hash != expected_object_hash:
        return False, "instance_object_hash_mismatch"
    if instance.lock_hash != expected_lock_hash:
        return False, "instance_lock_hash_mismatch"
    expected_hash = fire_object_instance_sha256(instance.payload_without_hash())
    if instance.instance_hash != expected_hash:
        return False, "instance_hash_mismatch"
    return True, None


def verify_fire_object_instance_against_manifest(
    instance: FireObjectInstanceManifest,
    *,
    object_manifest: FireObjectManifest,
) -> tuple[bool, str | None, FireInstanceGateReport]:
    if instance.object_hash != object_manifest.manifest_hash:
        report = FireInstanceGateReport(False, False, False, False, False, False, "instance_manifest_hash_mismatch")
        return False, report.error, report
    if instance.object_name != object_manifest.object_name:
        report = FireInstanceGateReport(False, False, False, False, False, False, "instance_object_name_mismatch")
        return False, report.error, report
    if instance.object_version != object_manifest.object_version:
        report = FireInstanceGateReport(False, False, False, False, False, False, "instance_object_version_mismatch")
        return False, report.error, report
    if instance.object_family != object_manifest.object_family:
        report = FireInstanceGateReport(False, False, False, False, False, False, "instance_object_family_mismatch")
        return False, report.error, report

    expected_parameters = {item.name: item for item in object_manifest.parameters}
    actual_parameters = {item.name: item.value for item in instance.parameters}
    if set(actual_parameters) != set(expected_parameters):
        missing = sorted(set(expected_parameters) - set(actual_parameters))
        extra = sorted(set(actual_parameters) - set(expected_parameters))
        error = f"param_missing:{','.join(missing)}" if missing else f"param_unexpected:{','.join(extra)}"
        report = FireInstanceGateReport(False, True, True, True, True, False, error)
        return False, error, report
    for name, requirement in expected_parameters.items():
        value = actual_parameters[name]
        if value < requirement.minimum or value > requirement.maximum:
            error = f"param_out_of_range:{name}"
            report = FireInstanceGateReport(False, True, True, True, True, False, error)
            return False, error, report

    expected_roles = tuple(sorted(object_manifest.instance_policy.required_party_roles))
    actual_roles = tuple(sorted(item.role for item in instance.parties))
    if actual_roles != expected_roles:
        error = "authorization_role_mismatch"
        report = FireInstanceGateReport(True, False, True, True, True, False, error)
        return False, error, report
    if object_manifest.instance_policy.authorization_mode == "role_binding":
        if any(not item.party_id for item in instance.parties):
            error = "authorization_party_id_missing"
            report = FireInstanceGateReport(True, False, True, True, True, False, error)
            return False, error, report

    if object_manifest.instance_policy.nonce_required and not instance.nonce:
        error = "nonce_missing"
        report = FireInstanceGateReport(True, True, False, True, True, False, error)
        return False, error, report

    if object_manifest.instance_policy.maturity_required and instance.maturity is None:
        error = "maturity_missing"
        report = FireInstanceGateReport(True, True, True, False, True, False, error)
        return False, error, report
    if instance.maturity is not None:
        try:
            _parse_iso_timestamp("maturity", instance.maturity)
        except ValueError as exc:
            error = f"maturity_invalid:{exc}"
            report = FireInstanceGateReport(True, True, True, False, True, False, error)
            return False, error, report

    if object_manifest.instance_policy.settlement_window_required and instance.settlement_window is None:
        error = "settlement_window_missing"
        report = FireInstanceGateReport(True, True, True, True, False, False, error)
        return False, error, report
    if instance.settlement_window is not None:
        try:
            start = _parse_iso_timestamp("settlement_window.start", instance.settlement_window.start)
            end = _parse_iso_timestamp("settlement_window.end", instance.settlement_window.end)
        except ValueError as exc:
            error = f"settlement_window_invalid:{exc}"
            report = FireInstanceGateReport(True, True, True, True, False, False, error)
            return False, error, report
        if start > end:
            error = "settlement_window_order_invalid"
            report = FireInstanceGateReport(True, True, True, True, False, False, error)
            return False, error, report

    report = FireInstanceGateReport(True, True, True, True, True, True, None)
    return True, None, report


def write_fire_object_instance(path: str | Path, instance: FireObjectInstanceManifest) -> str:
    file_path = Path(path)
    file_path.write_bytes(_canonical_json_bytes(instance.to_dict()))
    return fire_object_instance_file_sha256(instance)


def load_fire_object_instance(path: str | Path) -> tuple[FireObjectInstanceManifest, str]:
    file_path = Path(path)
    payload_bytes = file_path.read_bytes()
    payload = json.loads(payload_bytes.decode("utf-8"))
    instance = FireObjectInstanceManifest.from_dict(payload)
    file_sha256 = "sha256:" + hashlib.sha256(payload_bytes).hexdigest()
    return instance, file_sha256


__all__ = [
    "FireInstanceGateReport",
    "FireObjectInstanceManifest",
    "FireObjectParameterValue",
    "FireObjectPartyBinding",
    "FireSettlementWindow",
    "INSTANCE_SCHEMA",
    "fire_object_instance_file_sha256",
    "fire_object_instance_sha256",
    "load_fire_object_instance",
    "verify_fire_object_instance",
    "verify_fire_object_instance_against_manifest",
    "write_fire_object_instance",
]
