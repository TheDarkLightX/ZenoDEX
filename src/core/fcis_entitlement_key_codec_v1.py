"""Canonical bytes for the unmounted M6 R03 entitlement key."""
from __future__ import annotations

from typing import cast

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    sha256_hex,
)
from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)
from .fcis_entitlement_key_v1 import (
    ENTITLEMENT_KEY_SCHEMA_ID_V1,
    EntitlementKeyV1,
)


def _entitlement_key_projection_v1(value: EntitlementKeyV1) -> dict[str, str]:
    value.__post_init__()
    return dict(value.canonical_fields)


def encode_entitlement_key_v1(value: object) -> bytes:
    """Encode exactly the four-field C02 entitlement identity."""

    if type(value) is not EntitlementKeyV1:
        raise TypeError("entitlement key codec requires an exact value")
    projection = _entitlement_key_projection_v1(value)
    envelope = {"schema": ENTITLEMENT_KEY_SCHEMA_ID_V1, "value": projection}
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return cast(bytes, canonical_json_bytes(envelope))


def canonical_sha256_entitlement_key_v1(value: object) -> str:
    """Return the evidence digest for one canonical entitlement key."""

    return cast(str, sha256_hex(encode_entitlement_key_v1(value)))


__all__ = (
    "canonical_sha256_entitlement_key_v1",
    "encode_entitlement_key_v1",
)
