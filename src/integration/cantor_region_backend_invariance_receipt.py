from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Any

from .cantor_region_assurance_bundle import build_default_cantor_region_assurance_bundle
from .region_ba_backends import DEFAULT_REGION_BA_BACKEND, resolve_region_ba_backend


CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA = "zenodex/cantor-region-backend-invariance-receipt/v1"


@dataclass(frozen=True)
class CantorRegionBackendInvarianceReceipt:
    left_backend: str
    right_backend: str
    payload_equal: bool
    left_bundle_sha256: str
    right_bundle_sha256: str
    shared_bundle_sha256: str | None
    left_surface_count: int
    right_surface_count: int
    left_product_receipt_count: int
    right_product_receipt_count: int
    schema: str = CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != CANTOR_REGION_BACKEND_INVARIANCE_RECEIPT_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "left_backend": self.left_backend,
            "right_backend": self.right_backend,
            "payload_equal": self.payload_equal,
            "left_bundle_sha256": self.left_bundle_sha256,
            "right_bundle_sha256": self.right_bundle_sha256,
            "shared_bundle_sha256": self.shared_bundle_sha256,
            "left_surface_count": self.left_surface_count,
            "right_surface_count": self.right_surface_count,
            "left_product_receipt_count": self.left_product_receipt_count,
            "right_product_receipt_count": self.right_product_receipt_count,
        }


def _canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_hex(payload: dict[str, Any]) -> str:
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def build_cantor_region_backend_invariance_receipt(
    *,
    left_backend: str = DEFAULT_REGION_BA_BACKEND,
    right_backend: str = "bdd",
) -> CantorRegionBackendInvarianceReceipt:
    left_payload = build_default_cantor_region_assurance_bundle(
        ba=resolve_region_ba_backend(left_backend)
    ).to_dict()
    right_payload = build_default_cantor_region_assurance_bundle(
        ba=resolve_region_ba_backend(right_backend)
    ).to_dict()
    left_hash = _sha256_hex(left_payload)
    right_hash = _sha256_hex(right_payload)
    payload_equal = left_payload == right_payload

    return CantorRegionBackendInvarianceReceipt(
        left_backend=str(left_backend),
        right_backend=str(right_backend),
        payload_equal=payload_equal,
        left_bundle_sha256=left_hash,
        right_bundle_sha256=right_hash,
        shared_bundle_sha256=left_hash if payload_equal else None,
        left_surface_count=int(left_payload["surface_count"]),
        right_surface_count=int(right_payload["surface_count"]),
        left_product_receipt_count=int(left_payload["product_receipt_count"]),
        right_product_receipt_count=int(right_payload["product_receipt_count"]),
    )
