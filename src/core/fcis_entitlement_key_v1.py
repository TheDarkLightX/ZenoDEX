"""Canonical unmounted M6 R03 entitlement identity."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Final, final

from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .fcis_m6_profile_ids import (
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
)

ENTITLEMENT_KEY_SCHEMA_ID_V1: Final[str] = "zenodex/fcis/entitlement/key/v1"

ENTITLEMENT_KEY_FIELDS_V1: Final[tuple[str, str, str, str]] = (
    "fee_distribution_domain_id",
    "asset",
    "semantic_profile_id",
    "fixed_role_order_id",
)

ENTITLEMENT_KEY_EXCLUDED_FIELDS_V1: Final[tuple[str, ...]] = (
    "buyback_destination",
    "treasury_destination",
    "rewards_destination",
    "custody_account",
    "ordinary_policy_weights",
    "representation_codec",
)


def _require_bounded_text_v1(name: str, value: object) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")
    if not value:
        raise ValueError(f"{name} must be nonempty")
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


@final
@dataclass(frozen=True, slots=True)
class EntitlementKeyV1:
    """The four-field semantic identity for one entitlement history."""

    fee_distribution_domain_id: str
    asset: str
    semantic_profile_id: str
    fixed_role_order_id: str

    def __post_init__(self) -> None:
        for name, value in self.canonical_fields:
            _require_bounded_text_v1(name, value)
        if self.semantic_profile_id != SEMANTIC_ALLOCATOR_PROFILE_ID_V1:
            raise ValueError("unsupported entitlement semantic profile")
        if self.fixed_role_order_id != FIXED_ROLE_ORDER_ID_V1:
            raise ValueError("unsupported entitlement fixed role order")

    @property
    def canonical_fields(self) -> tuple[tuple[str, str], ...]:
        return (
            ("fee_distribution_domain_id", self.fee_distribution_domain_id),
            ("asset", self.asset),
            ("semantic_profile_id", self.semantic_profile_id),
            ("fixed_role_order_id", self.fixed_role_order_id),
        )

    @property
    def protocol_order_key(self) -> tuple[bytes, bytes, bytes, bytes]:
        return (
            self.fee_distribution_domain_id.encode("utf-8"),
            self.asset.encode("utf-8"),
            self.semantic_profile_id.encode("utf-8"),
            self.fixed_role_order_id.encode("utf-8"),
        )


__all__ = (
    "ENTITLEMENT_KEY_EXCLUDED_FIELDS_V1",
    "ENTITLEMENT_KEY_FIELDS_V1",
    "ENTITLEMENT_KEY_SCHEMA_ID_V1",
    "EntitlementKeyV1",
)
