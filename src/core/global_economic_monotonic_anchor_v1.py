"""Canonical external checkpoint coordinates for rollback detection.

This value is data, not authority.  A deployment must obtain it from an
independently durable, authenticated, monotonic source.  The deterministic
core binds that observation to one authority generation and publication head;
the integration shell owns source authentication, currentness, and CAS I/O.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_economic_durable_activation_v1 import _decode_exact_canonical_json_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
    hash_global_v1,
)

GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_SCHEMA_V1: Final = (
    "global-economic-monotonic-anchor-v1"
)
MAX_GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_BYTES_V1: Final = 8 * 1024
_U64_MAX_V1: Final = (1 << 64) - 1
_ANCHOR_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "abi",
        "anchor_namespace_root",
        "anchor_sequence",
        "previous_anchor_root",
        "authority_root",
        "authority_generation",
        "activation_id",
        "chain_id",
        "deployment_root",
        "epoch_store_root",
        "profile_root",
        "writer_epoch",
        "publication_id",
        "publication_sequence",
        "height",
        "state_root",
        "commit_id",
        "certificate_root",
    }
)


def _require_exact_u64_v1(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= _U64_MAX_V1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_exact_root_v1(
    value: object,
    *,
    name: str,
    allow_zero: bool = False,
) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return _require_root(value, name=name, allow_zero=allow_zero)


@dataclass(frozen=True, slots=True)
class GlobalEconomicMonotonicAnchorV1:
    """One complete rollback checkpoint obtained from an external source."""

    anchor_namespace_root: str
    anchor_sequence: int
    previous_anchor_root: str
    authority_root: str
    authority_generation: int
    activation_id: str
    chain_id: str
    deployment_root: str
    epoch_store_root: str
    profile_root: str
    writer_epoch: int
    publication_id: str
    publication_sequence: int
    height: int
    state_root: str
    commit_id: str
    certificate_root: str

    def __post_init__(self) -> None:
        for field_name in (
            "anchor_sequence",
            "authority_generation",
            "writer_epoch",
            "publication_sequence",
            "height",
        ):
            _require_exact_u64_v1(
                getattr(self, field_name),
                name=f"global economic monotonic anchor {field_name}",
            )
        for field_name in (
            "anchor_namespace_root",
            "authority_root",
            "activation_id",
            "deployment_root",
            "epoch_store_root",
            "profile_root",
            "publication_id",
            "state_root",
            "certificate_root",
        ):
            _require_exact_root_v1(
                getattr(self, field_name),
                name=f"global economic monotonic anchor {field_name}",
            )
        _require_exact_root_v1(
            self.previous_anchor_root,
            name="global economic monotonic anchor previous root",
            allow_zero=self.anchor_sequence == 0,
        )
        _require_exact_root_v1(
            self.commit_id,
            name="global economic monotonic anchor commit id",
            allow_zero=self.publication_sequence == 0,
        )
        if type(self.chain_id) is not str:
            raise TypeError("global economic monotonic anchor chain id must be exact str")
        _require_token(
            self.chain_id,
            name="global economic monotonic anchor chain id",
        )
        if self.anchor_sequence == 0:
            if self.previous_anchor_root != ZERO_ROOT_V1:
                raise ValueError("global economic genesis anchor previous root must be zero")
        elif self.previous_anchor_root == ZERO_ROOT_V1:
            raise ValueError("global economic successor anchor requires a previous root")
        if self.anchor_sequence < self.authority_generation:
            raise ValueError("global economic anchor precedes its authority generation")
        if self.anchor_sequence < self.publication_sequence:
            raise ValueError("global economic anchor precedes its publication sequence")
        if self.publication_sequence == 0:
            if self.publication_id != self.activation_id:
                raise ValueError("global economic activation publication identity mismatch")
            if self.commit_id != ZERO_ROOT_V1:
                raise ValueError("global economic activation anchor commit id must be zero")
        elif self.commit_id == ZERO_ROOT_V1:
            raise ValueError("global economic epoch anchor requires a commit id")

    @property
    def anchor_root(self) -> str:
        return hash_global_v1(
            "global-economic-monotonic-anchor-v1",
            self.to_canonical(),
        )

    @property
    def canonical_bytes(self) -> bytes:
        return canonical_global_bytes_v1(self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_SCHEMA_V1,
            "abi": GLOBAL_SETTLEMENT_ABI_V1,
            "anchor_namespace_root": self.anchor_namespace_root,
            "anchor_sequence": self.anchor_sequence,
            "previous_anchor_root": self.previous_anchor_root,
            "authority_root": self.authority_root,
            "authority_generation": self.authority_generation,
            "activation_id": self.activation_id,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "epoch_store_root": self.epoch_store_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "publication_id": self.publication_id,
            "publication_sequence": self.publication_sequence,
            "height": self.height,
            "state_root": self.state_root,
            "commit_id": self.commit_id,
            "certificate_root": self.certificate_root,
        }


def decode_global_economic_monotonic_anchor_v1(
    payload: bytes,
) -> GlobalEconomicMonotonicAnchorV1:
    """Decode exact canonical bytes; unknown, duplicate, and float fields reject."""

    if type(payload) is not bytes:
        raise TypeError("global economic monotonic anchor bytes must be exact bytes")
    if not 1 <= len(payload) <= MAX_GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_BYTES_V1:
        raise ValueError("global economic monotonic anchor bytes are outside the bound")
    try:
        value = _decode_exact_canonical_json_v1(
            payload,
            name="global economic monotonic anchor",
        )
    except RecursionError as exc:
        raise ValueError("global economic monotonic anchor nesting exceeds the bound") from exc
    if type(value) is not dict or set(value) != _ANCHOR_FIELDS_V1:
        raise ValueError("global economic monotonic anchor field set is not closed")
    if value["schema"] != GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_SCHEMA_V1:
        raise ValueError("global economic monotonic anchor schema mismatch")
    if value["abi"] != GLOBAL_SETTLEMENT_ABI_V1:
        raise ValueError("global economic monotonic anchor ABI mismatch")
    anchor = GlobalEconomicMonotonicAnchorV1(
        anchor_namespace_root=value["anchor_namespace_root"],
        anchor_sequence=value["anchor_sequence"],
        previous_anchor_root=value["previous_anchor_root"],
        authority_root=value["authority_root"],
        authority_generation=value["authority_generation"],
        activation_id=value["activation_id"],
        chain_id=value["chain_id"],
        deployment_root=value["deployment_root"],
        epoch_store_root=value["epoch_store_root"],
        profile_root=value["profile_root"],
        writer_epoch=value["writer_epoch"],
        publication_id=value["publication_id"],
        publication_sequence=value["publication_sequence"],
        height=value["height"],
        state_root=value["state_root"],
        commit_id=value["commit_id"],
        certificate_root=value["certificate_root"],
    )
    if anchor.canonical_bytes != payload:
        raise ValueError("global economic monotonic anchor is not canonical")
    return anchor


def require_global_economic_epoch_anchor_successor_v1(
    current: GlobalEconomicMonotonicAnchorV1,
    successor: GlobalEconomicMonotonicAnchorV1,
) -> None:
    """Require one adjacent ordinary-epoch advance under unchanged authority."""

    if type(current) is not GlobalEconomicMonotonicAnchorV1:
        raise TypeError("current global economic monotonic anchor type is not closed")
    if type(successor) is not GlobalEconomicMonotonicAnchorV1:
        raise TypeError("successor global economic monotonic anchor type is not closed")
    require_global_economic_monotonic_anchor_can_advance_v1(current)
    if successor.anchor_sequence != current.anchor_sequence + 1:
        raise ValueError("global economic monotonic anchor sequence is not adjacent")
    if successor.previous_anchor_root != current.anchor_root:
        raise ValueError("global economic monotonic anchor previous root mismatch")
    stable_bindings = (
        (successor.anchor_namespace_root, current.anchor_namespace_root),
        (successor.authority_root, current.authority_root),
        (successor.authority_generation, current.authority_generation),
        (successor.activation_id, current.activation_id),
        (successor.chain_id, current.chain_id),
        (successor.deployment_root, current.deployment_root),
        (successor.epoch_store_root, current.epoch_store_root),
        (successor.profile_root, current.profile_root),
        (successor.writer_epoch, current.writer_epoch),
    )
    if any(actual != expected for actual, expected in stable_bindings):
        raise ValueError("global economic epoch anchor changed a stable binding")
    if successor.publication_sequence != current.publication_sequence + 1:
        raise ValueError("global economic publication sequence is not adjacent")
    if successor.height != current.height + 1:
        raise ValueError("global economic publication height is not adjacent")
    if successor.publication_id == current.publication_id:
        raise ValueError("global economic epoch anchor reused a publication id")


def require_global_economic_monotonic_anchor_can_advance_v1(
    current: GlobalEconomicMonotonicAnchorV1,
) -> None:
    """Reject before mutation when an adjacent V1 epoch is unrepresentable."""

    if type(current) is not GlobalEconomicMonotonicAnchorV1:
        raise TypeError("current global economic monotonic anchor type is not closed")
    for field_name in ("anchor_sequence", "publication_sequence", "height"):
        if getattr(current, field_name) == _U64_MAX_V1:
            raise ValueError(
                f"global economic monotonic anchor {field_name} cannot advance"
            )


__all__ = [
    "GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_SCHEMA_V1",
    "MAX_GLOBAL_ECONOMIC_MONOTONIC_ANCHOR_BYTES_V1",
    "GlobalEconomicMonotonicAnchorV1",
    "decode_global_economic_monotonic_anchor_v1",
    "require_global_economic_monotonic_anchor_can_advance_v1",
    "require_global_economic_epoch_anchor_successor_v1",
]
