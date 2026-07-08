"""Shared-pool frontier signature certificate root binding helpers."""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass

FRONTIER_SIGNATURE_CERTIFICATES_ROOT_DOMAIN_V1 = (
    "zenodex.mev.shared_pool_frontier_signature_certificates_root.v1"
)
FRONTIER_SIGNATURE_CERTIFICATES_MAX_V1 = 16
FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1 = "0x" + hashlib.sha256(
    len(FRONTIER_SIGNATURE_CERTIFICATES_ROOT_DOMAIN_V1.encode("utf-8")).to_bytes(
        4,
        "big",
    )
    + FRONTIER_SIGNATURE_CERTIFICATES_ROOT_DOMAIN_V1.encode("utf-8")
    + (0).to_bytes(4, "big")
).hexdigest()

_ROOT_RE = re.compile(r"^(?:0x)?[0-9a-f]{64}$")


@dataclass(frozen=True)
class FrontierSignatureCertificatesRootBinding:
    certificate_count: int
    certificates_root: str

    def __post_init__(self) -> None:
        count, root = normalize_frontier_signature_binding(
            count=self.certificate_count,
            root=self.certificates_root,
            count_name="certificate_count",
            root_name="certificates_root",
        )
        object.__setattr__(self, "certificate_count", count)
        object.__setattr__(self, "certificates_root", root)


def normalize_frontier_signature_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if _ROOT_RE.fullmatch(value) is None:
        raise ValueError(f"{name} must be lowercase 32-byte hex")
    return value if value.startswith("0x") else f"0x{value}"


def require_frontier_signature_count(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    count = int(value)
    if count < 0:
        raise ValueError(f"{name} must be non-negative")
    if count > FRONTIER_SIGNATURE_CERTIFICATES_MAX_V1:
        raise ValueError(f"{name} exceeds {FRONTIER_SIGNATURE_CERTIFICATES_MAX_V1}")
    return count


def normalize_frontier_signature_binding(
    *,
    count: object,
    root: object,
    count_name: str,
    root_name: str,
) -> tuple[int, str]:
    normalized_count = require_frontier_signature_count(count, name=count_name)
    normalized_root = normalize_frontier_signature_root(root, name=root_name)
    if (
        normalized_count == 0
        and normalized_root != FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1
    ):
        raise ValueError(f"{root_name} must be empty root when count is zero")
    return normalized_count, normalized_root
