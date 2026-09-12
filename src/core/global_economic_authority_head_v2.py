"""Canonical current-authority coordinates for isolated V2 publication.

This value is an immutable, content-addressed snapshot.  Constructing one from
ordinary caller data grants no write, governance, settlement, or migration
authority; an integrating journal must still validate and commit it.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_economic_durable_activation_v1 import _decode_exact_canonical_json_v1
from .global_settlement_primitives_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_U64_V2,
    _require_root_v2,
    _require_token_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)

GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V2: Final = (
    "global-economic-authority-head-v2"
)
MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V2: Final = 4096
_AUTHORITY_FIELDS_V2: Final = frozenset(
    {
        "schema",
        "abi",
        "generation",
        "genesis_id",
        "chain_id",
        "deployment_root",
        "epoch_store_root",
        "profile_root",
        "writer_epoch",
        "guest_role_binding_root",
        "signature_manifest_root",
        "status",
    }
)


class GlobalEconomicAuthorityStatusV2(str, Enum):
    ACTIVE = "ACTIVE"
    REVOKED = "REVOKED"


def _require_exact_u64_v2(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= MAX_U64_V2:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


@dataclass(frozen=True, slots=True)
class GlobalEconomicAuthorityHeadV2:
    """One complete, content-addressed isolated V2 authority generation."""

    generation: int
    genesis_id: str
    chain_id: str
    deployment_root: str
    epoch_store_root: str
    profile_root: str
    writer_epoch: int
    guest_role_binding_root: str
    signature_manifest_root: str
    status: GlobalEconomicAuthorityStatusV2

    def __post_init__(self) -> None:
        _require_exact_u64_v2(
            self.generation,
            name="global economic authority generation",
        )
        _require_root_v2(
            self.genesis_id,
            name="global economic authority genesis id",
        )
        _require_token_v2(
            self.chain_id,
            name="global economic authority chain id",
        )
        for field_name in (
            "deployment_root",
            "epoch_store_root",
            "profile_root",
            "guest_role_binding_root",
            "signature_manifest_root",
        ):
            _require_root_v2(
                getattr(self, field_name),
                name=f"global economic authority {field_name}",
            )
        _require_exact_u64_v2(
            self.writer_epoch,
            name="global economic authority writer epoch",
        )
        if type(self.status) is not GlobalEconomicAuthorityStatusV2:
            raise TypeError("global economic authority status is not closed")

    @property
    def authority_root(self) -> str:
        return hash_global_v2(
            "global-economic-current-authority-v2",
            self.to_canonical(),
        )

    @property
    def canonical_bytes(self) -> bytes:
        return canonical_global_bytes_v2(self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V2,
            "abi": GLOBAL_SETTLEMENT_ABI_V2,
            "generation": self.generation,
            "genesis_id": self.genesis_id,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "epoch_store_root": self.epoch_store_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "guest_role_binding_root": self.guest_role_binding_root,
            "signature_manifest_root": self.signature_manifest_root,
            "status": self.status,
        }

    def revoked_successor(self) -> GlobalEconomicAuthorityHeadV2:
        """Build the sole supported successor: adjacent coordinate-preserving revocation."""

        if self.status is not GlobalEconomicAuthorityStatusV2.ACTIVE:
            raise ValueError("global economic authority is already revoked")
        if self.generation == MAX_U64_V2:
            raise ValueError("global economic authority generation cannot advance")
        return GlobalEconomicAuthorityHeadV2(
            generation=self.generation + 1,
            genesis_id=self.genesis_id,
            chain_id=self.chain_id,
            deployment_root=self.deployment_root,
            epoch_store_root=self.epoch_store_root,
            profile_root=self.profile_root,
            writer_epoch=self.writer_epoch,
            guest_role_binding_root=self.guest_role_binding_root,
            signature_manifest_root=self.signature_manifest_root,
            status=GlobalEconomicAuthorityStatusV2.REVOKED,
        )


def decode_global_economic_authority_head_v2(
    payload: bytes,
) -> GlobalEconomicAuthorityHeadV2:
    """Decode one exact, bounded canonical V2 authority head."""

    if type(payload) is not bytes:
        raise TypeError("global economic authority bytes must be exact bytes")
    if not 1 <= len(payload) <= MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V2:
        raise ValueError("global economic authority bytes are outside the bound")
    try:
        value = _decode_exact_canonical_json_v1(
            payload,
            name="global economic authority head",
        )
    except RecursionError as exc:
        raise ValueError(
            "global economic authority JSON nesting exceeds the bound"
        ) from exc
    if type(value) is not dict or set(value) != _AUTHORITY_FIELDS_V2:
        raise ValueError("global economic authority field set is not closed")
    if value["schema"] != GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V2:
        raise ValueError("global economic authority schema mismatch")
    if value["abi"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise ValueError("global economic authority ABI mismatch")
    try:
        status = GlobalEconomicAuthorityStatusV2(value["status"])
    except (TypeError, ValueError) as exc:
        raise ValueError("global economic authority status is unknown") from exc
    head = GlobalEconomicAuthorityHeadV2(
        generation=value["generation"],
        genesis_id=value["genesis_id"],
        chain_id=value["chain_id"],
        deployment_root=value["deployment_root"],
        epoch_store_root=value["epoch_store_root"],
        profile_root=value["profile_root"],
        writer_epoch=value["writer_epoch"],
        guest_role_binding_root=value["guest_role_binding_root"],
        signature_manifest_root=value["signature_manifest_root"],
        status=status,
    )
    if head.canonical_bytes != payload:
        raise ValueError("global economic authority encoding is not canonical")
    return head


def require_global_economic_authority_successor_v2(
    current: GlobalEconomicAuthorityHeadV2,
    successor: GlobalEconomicAuthorityHeadV2,
) -> None:
    """Require the adjacent, coordinate-preserving V2 revocation transition."""

    if type(current) is not GlobalEconomicAuthorityHeadV2:
        raise TypeError("current global economic authority type is not closed")
    if type(successor) is not GlobalEconomicAuthorityHeadV2:
        raise TypeError("successor global economic authority type is not closed")
    if current.status is GlobalEconomicAuthorityStatusV2.REVOKED:
        raise ValueError("revoked global economic authority is terminal in ABI V2")
    if current.generation == MAX_U64_V2:
        raise ValueError("global economic authority generation cannot advance")
    if successor.generation != current.generation + 1:
        raise ValueError("global economic authority generation is not adjacent")
    if successor.status is not GlobalEconomicAuthorityStatusV2.REVOKED:
        raise ValueError(
            "global economic authority successor must be a coordinate-preserving revocation"
        )
    stable_coordinates = (
        "genesis_id",
        "chain_id",
        "deployment_root",
        "epoch_store_root",
        "profile_root",
        "writer_epoch",
        "guest_role_binding_root",
        "signature_manifest_root",
    )
    if any(
        getattr(successor, field) != getattr(current, field)
        for field in stable_coordinates
    ):
        raise ValueError("global economic authority revocation changed coordinates")


__all__ = [
    "GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V2",
    "GlobalEconomicAuthorityHeadV2",
    "GlobalEconomicAuthorityStatusV2",
    "MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V2",
    "decode_global_economic_authority_head_v2",
    "require_global_economic_authority_successor_v2",
]
