"""Shared redaction helpers for operator-facing CLI output."""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from typing import Any

SENSITIVE_KEY_FRAGMENTS = (
    "auth_token",
    "bearer",
    "credential",
    "key_bundle",
    "password",
    "privkey",
    "private_key",
    "secret",
    "seed_override",
    "token_path",
    "write_token",
)


def _sensitive_key(key: object) -> bool:
    text = str(key).lower()
    return any(fragment in text for fragment in SENSITIVE_KEY_FRAGMENTS)


def redact_for_log(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            str(key): "[redacted]" if _sensitive_key(key) else redact_for_log(item)
            for key, item in value.items()
        }
    if isinstance(value, str):
        return value
    if isinstance(value, Sequence) and not isinstance(value, (bytes, bytearray)):
        return [redact_for_log(item) for item in value]
    return value


def json_dumps_for_log(value: Any, **kwargs: Any) -> str:
    return json.dumps(redact_for_log(value), **kwargs)
