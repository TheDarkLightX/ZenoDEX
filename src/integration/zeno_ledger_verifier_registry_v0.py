"""ZenoLedger v0 proof verifier registry policy."""

from __future__ import annotations

from copy import deepcopy
from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_v0 import (
    PROOF_KINDS_V0,
    PROOF_METADATA_SCHEMA_V0,
    ZERO_ROOT_V0,
    hash_v0,
    validate_proof_metadata_v0,
)
from src.integration.production_key_management_v0 import SignatureVerifierV0
from src.integration.zeno_ledger_production_key_gates_v0 import validate_verifier_registry_update_gate_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

VERIFIER_REGISTRY_SCHEMA_V0 = "zenodex/zeno_ledger/verifier_registry/v0"
VERIFIER_REGISTRY_ENTRY_SCHEMA_V0 = "zenodex/zeno_ledger/verifier_registry_entry/v0"
VERIFIER_STATUS_ACTIVE_V0 = "active"
VERIFIER_STATUS_REVOKED_V0 = "revoked"
VERIFIER_STATUSES_V0 = frozenset({VERIFIER_STATUS_ACTIVE_V0, VERIFIER_STATUS_REVOKED_V0})


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_list(value: object, *, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty str")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_optional_nonnegative_int(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_nonnegative_int(value, name=name)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _entry_content_hash(entry: Mapping[str, Any]) -> str:
    obj = dict(entry)
    obj.pop("entry_id", None)
    return hash_v0("verifier_registry_entry_v0", obj)


def verifier_registry_content_hash_v0(registry: Mapping[str, Any]) -> str:
    obj = dict(_require_mapping(registry, name="verifier_registry"))
    obj.pop("registry_id", None)
    return hash_v0("verifier_registry_v0", obj)


def make_verifier_registry_entry_v0(
    *,
    proof_kind: str,
    program_id: str,
    verifier_id: str,
    status: str = VERIFIER_STATUS_ACTIVE_V0,
    valid_from_height: int = 0,
    valid_until_height: int | None = None,
    tee_measurement_hash: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    entry = {
        "schema": VERIFIER_REGISTRY_ENTRY_SCHEMA_V0,
        "entry_id": ZERO_ROOT_V0,
        "proof_kind": proof_kind,
        "program_id": program_id,
        "verifier_id": verifier_id,
        "status": status,
        "valid_from_height": valid_from_height,
        "valid_until_height": valid_until_height,
        "tee_measurement_hash": tee_measurement_hash,
    }
    entry["entry_id"] = _entry_content_hash(entry)
    validate_verifier_registry_entry_v0(entry)
    return entry


def validate_verifier_registry_entry_v0(entry: Mapping[str, Any]) -> None:
    obj = _require_mapping(entry, name="verifier_registry_entry")
    expected = {
        "schema",
        "entry_id",
        "proof_kind",
        "program_id",
        "verifier_id",
        "status",
        "valid_from_height",
        "valid_until_height",
        "tee_measurement_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("verifier_registry_entry keys mismatch")
    if obj.get("schema") != VERIFIER_REGISTRY_ENTRY_SCHEMA_V0:
        raise ValueError("verifier_registry_entry schema mismatch")
    entry_id = _require_root(obj.get("entry_id"), name="verifier_registry_entry.entry_id")
    if entry_id != _entry_content_hash(obj):
        raise ValueError("verifier_registry_entry entry_id mismatch")
    proof_kind = _require_str(obj.get("proof_kind"), name="verifier_registry_entry.proof_kind")
    if proof_kind not in PROOF_KINDS_V0:
        raise ValueError("verifier_registry_entry proof_kind is not allowed")
    _require_str(obj.get("program_id"), name="verifier_registry_entry.program_id")
    _require_str(obj.get("verifier_id"), name="verifier_registry_entry.verifier_id")
    status = _require_str(obj.get("status"), name="verifier_registry_entry.status")
    if status not in VERIFIER_STATUSES_V0:
        raise ValueError("verifier_registry_entry status is not allowed")
    valid_from = _require_nonnegative_int(
        obj.get("valid_from_height"),
        name="verifier_registry_entry.valid_from_height",
    )
    valid_until = _require_optional_nonnegative_int(
        obj.get("valid_until_height"),
        name="verifier_registry_entry.valid_until_height",
    )
    if valid_until is not None and valid_until < valid_from:
        raise ValueError("verifier_registry_entry valid_until_height precedes valid_from_height")
    tee_measurement_hash = _require_root(
        obj.get("tee_measurement_hash"),
        name="verifier_registry_entry.tee_measurement_hash",
    )
    if proof_kind == "tee_attestation_v0" and tee_measurement_hash == ZERO_ROOT_V0:
        raise ValueError("TEE verifier registry entry requires tee_measurement_hash")
    if proof_kind != "tee_attestation_v0" and tee_measurement_hash != ZERO_ROOT_V0:
        raise ValueError("non-TEE verifier registry entry must use zero tee_measurement_hash")


def make_verifier_registry_v0(*, entries: list[Mapping[str, Any]]) -> dict[str, Any]:
    registry = {
        "schema": VERIFIER_REGISTRY_SCHEMA_V0,
        "registry_id": ZERO_ROOT_V0,
        "entries": [dict(entry) for entry in entries],
    }
    registry["registry_id"] = verifier_registry_content_hash_v0(registry)
    validate_verifier_registry_v0(registry)
    return registry


def validate_verifier_registry_v0(
    registry: Mapping[str, Any],
    *,
    production_key_admission_receipt: Mapping[str, Any] | None = None,
    production_key_packet: Mapping[str, Any] | None = None,
    production_key_descriptors: Sequence[Mapping[str, Any]] | None = None,
    production_key_signature_envelopes: Sequence[Mapping[str, Any]] | None = None,
    production_key_signature_verifier: SignatureVerifierV0 | None = None,
    require_production_key_admission: bool = False,
) -> None:
    obj = _require_mapping(registry, name="verifier_registry")
    expected = {"schema", "registry_id", "entries"}
    if set(obj.keys()) != expected:
        raise ValueError("verifier_registry keys mismatch")
    if obj.get("schema") != VERIFIER_REGISTRY_SCHEMA_V0:
        raise ValueError("verifier_registry schema mismatch")
    registry_id = _require_root(obj.get("registry_id"), name="verifier_registry.registry_id")
    if registry_id != verifier_registry_content_hash_v0(obj):
        raise ValueError("verifier_registry registry_id mismatch")
    if require_production_key_admission:
        if production_key_admission_receipt is None:
            raise ValueError("verifier_registry production key-management admission receipt is required")
        validate_verifier_registry_update_gate_v0(
            production_key_admission_receipt,
            packet=production_key_packet,
            key_descriptors=production_key_descriptors,
            signature_envelopes=production_key_signature_envelopes,
            signature_verifier=production_key_signature_verifier,
            expected_target_kind="zeno_ledger_verifier_registry",
            expected_target_hash=registry_id,
            expected_payload_hash=registry_id,
        )
    entries = _require_list(obj.get("entries"), name="verifier_registry.entries")
    if not entries:
        raise ValueError("verifier_registry entries must be non-empty")
    seen: set[tuple[str, str, str]] = set()
    for index, raw_entry in enumerate(entries):
        entry = _require_mapping(raw_entry, name=f"verifier_registry.entries[{index}]")
        validate_verifier_registry_entry_v0(entry)
        key = (
            str(entry["proof_kind"]),
            str(entry["program_id"]),
            str(entry["verifier_id"]),
        )
        if key in seen:
            raise ValueError("verifier_registry duplicate proof/program/verifier entry")
        seen.add(key)


def validate_proof_metadata_against_verifier_registry_v0(
    *,
    proof_metadata: Mapping[str, Any],
    registry: Mapping[str, Any],
) -> None:
    metadata = dict(proof_metadata)
    validate_proof_metadata_v0(metadata)
    validate_verifier_registry_v0(registry)
    for raw_entry in _require_list(registry.get("entries"), name="verifier_registry.entries"):
        entry = _require_mapping(raw_entry, name="verifier_registry_entry")
        if entry["proof_kind"] != metadata["proof_kind"]:
            continue
        if entry["program_id"] != metadata["program_id"]:
            continue
        if entry["verifier_id"] != metadata["verifier_id"]:
            continue
        if entry["status"] != VERIFIER_STATUS_ACTIVE_V0:
            raise ValueError("proof verifier registry entry is not active")
        height = int(metadata["height"])
        if height < int(entry["valid_from_height"]):
            raise ValueError("proof metadata height precedes verifier registry entry")
        valid_until = entry["valid_until_height"]
        if valid_until is not None and height > int(valid_until):
            raise ValueError("proof metadata height exceeds verifier registry entry")
        if (
            metadata["proof_kind"] == "tee_attestation_v0"
            and entry["tee_measurement_hash"] != metadata["tee_measurement_hash"]
        ):
            raise ValueError("proof metadata TEE measurement is not admitted by verifier registry")
        return
    raise ValueError("proof metadata verifier is not admitted by registry")


def clone_verifier_registry_with_new_id_v0(registry: Mapping[str, Any], **updates: Any) -> dict[str, Any]:
    updated = deepcopy(dict(registry))
    updated.update(updates)
    updated["registry_id"] = verifier_registry_content_hash_v0(updated)
    return updated
