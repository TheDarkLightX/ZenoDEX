"""Canonical current-authority coordinates for global economic publication.

The value is a deterministic authority snapshot.  It grants no write access by
itself.  Durable adapters use its content-derived root as a CAS fence around
receipt verification and publication.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_economic_durable_activation_v1 import _decode_exact_canonical_json_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
    hash_global_v1,
)

GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1: Final = (
    "global-economic-authority-head-v1"
)
MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V1: Final = 4096
_U64_MAX_V1: Final = (1 << 64) - 1
_AUTHORITY_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "abi",
        "generation",
        "activation_id",
        "chain_id",
        "deployment_root",
        "epoch_store_root",
        "profile_root",
        "writer_epoch",
        "verifier_registry_root",
        "verifier_release_id",
        "verifier_binding_root",
        "root_image_id",
        "status",
    }
)


class GlobalEconomicAuthorityStatusV1(str, Enum):
    ACTIVE = "ACTIVE"
    REVOKED = "REVOKED"


def _require_exact_u64_v1(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= _U64_MAX_V1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_exact_root_v1(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return _require_root(value, name=name)


@dataclass(frozen=True, slots=True)
class GlobalEconomicAuthorityHeadV1:
    """One complete, content-addressed publication-authority generation."""

    generation: int
    activation_id: str
    chain_id: str
    deployment_root: str
    epoch_store_root: str
    profile_root: str
    writer_epoch: int
    verifier_registry_root: str
    verifier_release_id: str
    verifier_binding_root: str
    root_image_id: str
    status: GlobalEconomicAuthorityStatusV1

    def __post_init__(self) -> None:
        _require_exact_u64_v1(
            self.generation,
            name="global economic authority generation",
        )
        if type(self.chain_id) is not str:
            raise TypeError("global economic authority chain id must be exact str")
        _require_token(self.chain_id, name="global economic authority chain id")
        for field_name in (
            "activation_id",
            "deployment_root",
            "epoch_store_root",
            "profile_root",
            "verifier_registry_root",
            "verifier_release_id",
            "verifier_binding_root",
            "root_image_id",
        ):
            _require_exact_root_v1(
                getattr(self, field_name),
                name=f"global economic authority {field_name}",
            )
        _require_exact_u64_v1(
            self.writer_epoch,
            name="global economic authority writer epoch",
        )
        if type(self.status) is not GlobalEconomicAuthorityStatusV1:
            raise TypeError("global economic authority status is not closed")

    @property
    def authority_root(self) -> str:
        return hash_global_v1(
            "global-economic-current-authority-v1",
            self.to_canonical(),
        )

    @property
    def canonical_bytes(self) -> bytes:
        return canonical_global_bytes_v1(self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1,
            "abi": GLOBAL_SETTLEMENT_ABI_V1,
            "generation": self.generation,
            "activation_id": self.activation_id,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "epoch_store_root": self.epoch_store_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "verifier_registry_root": self.verifier_registry_root,
            "verifier_release_id": self.verifier_release_id,
            "verifier_binding_root": self.verifier_binding_root,
            "root_image_id": self.root_image_id,
            "status": self.status,
        }

    def revoked_successor(self) -> GlobalEconomicAuthorityHeadV1:
        if self.status is not GlobalEconomicAuthorityStatusV1.ACTIVE:
            raise ValueError("global economic authority is already revoked")
        if self.generation == _U64_MAX_V1:
            raise ValueError("global economic authority generation cannot advance")
        return GlobalEconomicAuthorityHeadV1(
            generation=self.generation + 1,
            activation_id=self.activation_id,
            chain_id=self.chain_id,
            deployment_root=self.deployment_root,
            epoch_store_root=self.epoch_store_root,
            profile_root=self.profile_root,
            writer_epoch=self.writer_epoch,
            verifier_registry_root=self.verifier_registry_root,
            verifier_release_id=self.verifier_release_id,
            verifier_binding_root=self.verifier_binding_root,
            root_image_id=self.root_image_id,
            status=GlobalEconomicAuthorityStatusV1.REVOKED,
        )


def decode_global_economic_authority_head_v1(
    payload: bytes,
) -> GlobalEconomicAuthorityHeadV1:
    if type(payload) is not bytes:
        raise TypeError("global economic authority bytes must be exact bytes")
    if not 1 <= len(payload) <= MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V1:
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
    if type(value) is not dict or set(value) != _AUTHORITY_FIELDS_V1:
        raise ValueError("global economic authority field set is not closed")
    if value["schema"] != GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1:
        raise ValueError("global economic authority schema mismatch")
    if value["abi"] != GLOBAL_SETTLEMENT_ABI_V1:
        raise ValueError("global economic authority ABI mismatch")
    try:
        status = GlobalEconomicAuthorityStatusV1(value["status"])
    except (TypeError, ValueError) as exc:
        raise ValueError("global economic authority status is unknown") from exc
    head = GlobalEconomicAuthorityHeadV1(
        generation=value["generation"],
        activation_id=value["activation_id"],
        chain_id=value["chain_id"],
        deployment_root=value["deployment_root"],
        epoch_store_root=value["epoch_store_root"],
        profile_root=value["profile_root"],
        writer_epoch=value["writer_epoch"],
        verifier_registry_root=value["verifier_registry_root"],
        verifier_release_id=value["verifier_release_id"],
        verifier_binding_root=value["verifier_binding_root"],
        root_image_id=value["root_image_id"],
        status=status,
    )
    if head.canonical_bytes != payload:
        raise ValueError("global economic authority encoding is not canonical")
    return head


def require_global_economic_authority_successor_v1(
    current: GlobalEconomicAuthorityHeadV1,
    successor: GlobalEconomicAuthorityHeadV1,
) -> None:
    """Require a monotone revocation or profile-migration rotation."""

    if type(current) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("current global economic authority type is not closed")
    if type(successor) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("successor global economic authority type is not closed")
    if current.status is GlobalEconomicAuthorityStatusV1.REVOKED:
        raise ValueError("revoked global economic authority is terminal in ABI V1")
    if current.generation == _U64_MAX_V1:
        raise ValueError("global economic authority generation cannot advance")
    if successor.generation != current.generation + 1:
        raise ValueError("global economic authority generation is not adjacent")
    if successor.chain_id != current.chain_id:
        raise ValueError("global economic authority chain changed")
    if successor.deployment_root != current.deployment_root:
        raise ValueError("global economic authority deployment changed")
    if successor.epoch_store_root != current.epoch_store_root:
        raise ValueError("global economic authority epoch store changed")

    if successor.status is GlobalEconomicAuthorityStatusV1.REVOKED:
        _require_coordinate_preserving_revocation_v1(current, successor)
        return
    if not _is_exact_profile_rotation_v1(current, successor):
        raise ValueError(
            "global economic authority successor is not an exact profile migration"
        )


def _require_coordinate_preserving_revocation_v1(
    current: GlobalEconomicAuthorityHeadV1,
    successor: GlobalEconomicAuthorityHeadV1,
) -> None:
    stable_coordinates = (
        "activation_id",
        "epoch_store_root",
        "profile_root",
        "writer_epoch",
        "verifier_registry_root",
        "verifier_release_id",
        "verifier_binding_root",
        "root_image_id",
    )
    if any(
        getattr(successor, field) != getattr(current, field)
        for field in stable_coordinates
    ):
        raise ValueError("global economic authority revocation changed coordinates")


def _is_exact_profile_rotation_v1(
    current: GlobalEconomicAuthorityHeadV1,
    successor: GlobalEconomicAuthorityHeadV1,
) -> bool:
    return (
        successor.activation_id != current.activation_id
        and successor.profile_root != current.profile_root
        and successor.writer_epoch == current.writer_epoch + 1
    )


__all__ = [
    "GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V1",
    "GlobalEconomicAuthorityHeadV1",
    "GlobalEconomicAuthorityStatusV1",
    "MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V1",
    "decode_global_economic_authority_head_v1",
    "require_global_economic_authority_successor_v1",
]
