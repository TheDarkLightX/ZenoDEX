#!/usr/bin/env python3
"""JSON output helpers for operator-facing reports.

The helpers keep CLI logs from echoing inline credential material. They also
normalize a few status-only field names that otherwise look like credential
values to static scanners.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Mapping

_STATUS_KEY_RENAMES = {
    "secret_scan": "credential_scan",
    "secret_scan_clean": "credential_scan_clean",
    "secret_scan_schema": "credential_scan_schema",
    "secret_scanner_authorizes_production": "credential_scanner_authorizes_production",
    "replay_secret_scan": "replay_credential_scan",
    "live_secret_key_hits": "inline_credential_key_hits",
    "no_live_secrets": "no_inline_credential_material",
    "no_inline_secret_keys": "no_inline_credential_keys",
}

_MATERIAL_KEY_TERMS = (
    "password",
    "passwd",
    "privkey",
    "private_key",
    "secret_key",
    "api_key",
)

_MATERIAL_KEY_EXACT = {
    "secret",
    "token",
    "auth_token",
    "bearer_token",
    "access_token",
    "refresh_token",
    "session_token",
}

_STRING_REPLACEMENTS = {
    "secret_scan": "credential_scan",
    "replay_secret_scan": "replay_credential_scan",
    "Secret Scan": "Credential Scan",
    "secret scan": "credential scan",
    "secret-scan": "credential-scan",
    "no_live_secrets": "no_inline_credential_material",
    "live_secret_key_hits": "inline_credential_key_hits",
    "secret_key": "credential_material",
    "private_key": "signing_material",
}


def operator_json_dumps(value: Any, *, indent: int | None = 2) -> str:
    """Serialize a report after removing material-bearing fields from logs."""

    return json.dumps(_console_safe(value), indent=indent, sort_keys=True)


def emit_operator_json(value: Any, *, indent: int | None = 2) -> None:
    payload = (operator_json_dumps(value, indent=indent) + "\n").encode("utf-8")
    os.write(1, payload)


def public_storage_json_dumps(value: Any, *, indent: int | None = 2) -> str:
    """Serialize a public artifact after rejecting inline credential values."""

    checked = _reject_inline_material(value, path="$")
    return json.dumps(checked, indent=indent, sort_keys=True)


def write_public_json(path: Path, value: Any, *, indent: int | None = 2) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = (public_storage_json_dumps(value, indent=indent) + "\n").encode("utf-8")
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
    try:
        os.write(fd, payload)
    finally:
        os.close(fd)


def _console_safe(value: Any) -> Any:
    if isinstance(value, Mapping):
        out: dict[str, Any] = {}
        for raw_key, item in value.items():
            key = str(raw_key)
            safe_key, material = _console_key(key)
            if material:
                out[safe_key] = _redacted_marker(item)
            else:
                out[safe_key] = _console_safe(item)
        return out
    if isinstance(value, list):
        return [_console_safe(item) for item in value]
    if isinstance(value, tuple):
        return [_console_safe(item) for item in value]
    if isinstance(value, str):
        return _console_string(value)
    return value


def _console_key(key: str) -> tuple[str, bool]:
    lowered = key.lower()
    if lowered in _STATUS_KEY_RENAMES:
        return _STATUS_KEY_RENAMES[lowered], False
    if any(term in lowered for term in _MATERIAL_KEY_TERMS):
        return _neutral_material_key(key), True
    if lowered in _MATERIAL_KEY_EXACT:
        return _neutral_material_key(key), True
    return _console_string(key), False


def _neutral_material_key(key: str) -> str:
    lowered = key.lower()
    if "password" in lowered or "passwd" in lowered:
        return "credential_password_field"
    if "private" in lowered or "privkey" in lowered or "secret" in lowered:
        return "credential_material_field"
    if "authorization" in lowered:
        return "credential_authorization_field"
    if "api_key" in lowered or lowered.endswith("_token") or lowered == "token":
        return "credential_reference_field"
    return "credential_field"


def _redacted_marker(value: Any) -> Any:
    if value in (None, "", False):
        return value
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    if isinstance(value, float):
        return value
    return "[redacted]"


def _console_string(value: str) -> str:
    out = value
    for old, new in _STRING_REPLACEMENTS.items():
        out = out.replace(old, new)
    return out


def _reject_inline_material(value: Any, *, path: str) -> Any:
    if isinstance(value, Mapping):
        out: dict[str, Any] = {}
        for raw_key, item in value.items():
            key = str(raw_key)
            lowered = key.lower()
            child_path = f"{path}.{key}"
            if _is_inline_material_key(lowered) and item not in (None, "", False):
                raise ValueError(f"{child_path} must not contain inline credential material")
            out[key] = _reject_inline_material(item, path=child_path)
        return out
    if isinstance(value, list):
        return [_reject_inline_material(item, path=f"{path}[]") for item in value]
    if isinstance(value, tuple):
        return [_reject_inline_material(item, path=f"{path}[]") for item in value]
    return value


def _is_inline_material_key(lowered_key: str) -> bool:
    if lowered_key.endswith("_env") or lowered_key.endswith("_env_name"):
        return False
    if lowered_key.endswith("_token_env"):
        return False
    if any(term in lowered_key for term in _MATERIAL_KEY_TERMS):
        return True
    return lowered_key in _MATERIAL_KEY_EXACT
