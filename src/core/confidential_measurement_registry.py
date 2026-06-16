"""Measurement registry helpers for confidential extension receipts."""

from __future__ import annotations

from typing import Any, Dict, Iterable, Tuple

from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

MAX_EPOCH = 0xFFFFFFFF
CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA = "zenodex/confidential_measurement_registry/v1"
CONFIDENTIAL_MEASUREMENT_REGISTRY_HASH_DOMAIN = "zenodex.confidential_measurement_registry/v1"


def _require_nonempty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_policy_digest(value: Any) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name="policy_digest")


def _require_bounded_int(value: Any, *, name: str, upper: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > upper:
        raise ValueError(f"{name} must be a bounded int")
    return value


def confidential_measurement_registry_hash(registry: Dict[str, Any]) -> str:
    unsigned = _measurement_registry_unsigned(registry)
    return sha256_hex(
        domain_sep_bytes(CONFIDENTIAL_MEASUREMENT_REGISTRY_HASH_DOMAIN)
        + canonical_json_bytes(unsigned)
    )


def _is_lower_hex(value: str, *, length: int) -> bool:
    return len(value) == length and all(ch in "0123456789abcdef" for ch in value)


def is_canonical_confidential_measurement(value: str) -> bool:
    if not isinstance(value, str) or not value:
        return False
    if value.startswith("nitro:"):
        parts = value.split(":")
        return (
            len(parts) == 5
            and parts[0] == "nitro"
            and parts[1] == "pcr0"
            and parts[3] == "pcr8"
            and _is_lower_hex(parts[2], length=96)
            and _is_lower_hex(parts[4], length=96)
        )
    if value.startswith("azure-sevsnp:"):
        parts = value.split(":")
        return (
            len(parts) == 3
            and parts[0] == "azure-sevsnp"
            and parts[1] == "hostdata"
            and _is_lower_hex(parts[2], length=64)
        )
    return True


def _to_measurement_set(values: Iterable[str]) -> set[str]:
    out = {str(v) for v in values}
    out.discard("")
    return out


def _measurement_registry_unsigned(registry: Dict[str, Any]) -> Dict[str, Any]:
    entries = registry.get("entries")
    if not isinstance(entries, list):
        raise ValueError("registry.entries must be a list")
    normalized_entries = []
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("registry entries must be objects")
        normalized_entries.append(
            {
                "provider_id": entry.get("provider_id"),
                "measurement": entry.get("measurement"),
                "policy_digest": entry.get("policy_digest"),
                "valid_from_epoch": entry.get("valid_from_epoch"),
                "valid_until_epoch": entry.get("valid_until_epoch"),
                "revoked": entry.get("revoked"),
            }
        )
    normalized_entries.sort(
        key=lambda entry: (
            str(entry["provider_id"]),
            str(entry["measurement"]),
            str(entry["policy_digest"]),
            int(entry["valid_from_epoch"]) if isinstance(entry["valid_from_epoch"], int) else -1,
            int(entry["valid_until_epoch"]) if isinstance(entry["valid_until_epoch"], int) else -1,
        )
    )
    return {
        "schema": registry.get("schema"),
        "registry_id": registry.get("registry_id"),
        "entries": normalized_entries,
    }


def verify_confidential_measurement_registry(
    registry: object,
    *,
    current_epoch: int,
    policy_digest: str | None = None,
) -> Tuple[bool, str, set[str]]:
    if not isinstance(registry, dict):
        return False, "bad_registry_type", set()
    try:
        current_epoch_v = _require_bounded_int(current_epoch, name="current_epoch", upper=MAX_EPOCH)
        policy_digest_v = None if policy_digest is None else _require_policy_digest(policy_digest)
        if registry.get("schema") != CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA:
            return False, "bad_registry_schema", set()
        _require_nonempty_str(registry.get("registry_id"), name="registry_id")
        entries_obj = registry.get("entries")
        if not isinstance(entries_obj, list):
            return False, "bad_registry_entries", set()
        if "registry_hash" in registry:
            want_hash = registry.get("registry_hash")
            if not isinstance(want_hash, str) or want_hash != confidential_measurement_registry_hash(registry):
                return False, "registry_hash_mismatch", set()
        active: set[str] = set()
        seen_keys: set[tuple[str, str, str]] = set()
        for entry_obj in entries_obj:
            if not isinstance(entry_obj, dict):
                return False, "bad_registry_entry", set()
            provider_id = _require_nonempty_str(entry_obj.get("provider_id"), name="entry.provider_id")
            measurement = _require_nonempty_str(entry_obj.get("measurement"), name="entry.measurement")
            if not is_canonical_confidential_measurement(measurement):
                return False, "bad_registry_measurement", set()
            entry_policy_digest = _require_policy_digest(entry_obj.get("policy_digest"))
            valid_from = _require_bounded_int(
                entry_obj.get("valid_from_epoch"),
                name="entry.valid_from_epoch",
                upper=MAX_EPOCH,
            )
            valid_until = _require_bounded_int(
                entry_obj.get("valid_until_epoch"),
                name="entry.valid_until_epoch",
                upper=MAX_EPOCH,
            )
            if valid_until < valid_from:
                return False, "bad_registry_epoch_window", set()
            revoked = entry_obj.get("revoked")
            if not isinstance(revoked, bool):
                return False, "bad_registry_revocation_flag", set()
            key = (provider_id, measurement, entry_policy_digest)
            if key in seen_keys:
                return False, "duplicate_registry_measurement", set()
            seen_keys.add(key)
            if policy_digest_v is not None and entry_policy_digest != policy_digest_v:
                continue
            if revoked:
                continue
            if valid_from <= current_epoch_v <= valid_until:
                active.add(measurement)
        return True, "ok", active
    except (TypeError, ValueError):
        return False, "bad_registry_entry", set()


def confidential_measurement_registry_approves_receipt(
    registry: Dict[str, Any],
    *,
    provider_id: str,
    measurement: str,
    current_epoch: int,
    policy_digest: str,
) -> Tuple[bool, str]:
    ok, err, _active = verify_confidential_measurement_registry(
        registry,
        current_epoch=current_epoch,
        policy_digest=policy_digest,
    )
    if not ok:
        return False, err
    try:
        provider_id_v = _require_nonempty_str(provider_id, name="provider_id")
        measurement_v = _require_nonempty_str(measurement, name="measurement")
        if not is_canonical_confidential_measurement(measurement_v):
            return False, "bad_registry_measurement"
        policy_digest_v = _require_policy_digest(policy_digest)
        current_epoch_v = _require_bounded_int(current_epoch, name="current_epoch", upper=MAX_EPOCH)
        entries_obj = registry.get("entries")
        if not isinstance(entries_obj, list):
            return False, "bad_registry_entries"
        for entry_obj in entries_obj:
            if not isinstance(entry_obj, dict):
                return False, "bad_registry_entry"
            if entry_obj.get("provider_id") != provider_id_v:
                continue
            if entry_obj.get("measurement") != measurement_v:
                continue
            if _require_policy_digest(entry_obj.get("policy_digest")) != policy_digest_v:
                continue
            valid_from = _require_bounded_int(
                entry_obj.get("valid_from_epoch"),
                name="entry.valid_from_epoch",
                upper=MAX_EPOCH,
            )
            valid_until = _require_bounded_int(
                entry_obj.get("valid_until_epoch"),
                name="entry.valid_until_epoch",
                upper=MAX_EPOCH,
            )
            if bool(entry_obj.get("revoked")):
                continue
            if valid_from <= current_epoch_v <= valid_until:
                return True, "ok"
        return False, "measurement_not_active_for_provider"
    except (TypeError, ValueError):
        return False, "bad_registry_entry"
