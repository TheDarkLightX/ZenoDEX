"""Pure admission policy for protocol-managed asset operations.

The policy controls which generic token surfaces may touch a managed asset. It
does not authorize the protocol-specific mint, burn, liquidation, or recovery
transition that owns the asset's economic invariant.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

ZUSD_MONETARY_AUTHORITY_V1 = "zenodex/zusd-monetary-kernel/v1"
_LOWER_HEX = frozenset("0123456789abcdef")


class AssetOperationV1(str, Enum):
    TRANSFER = "transfer"
    GENERIC_MINT = "generic_mint"
    GENERIC_BURN = "generic_burn"
    FAUCET_MINT = "faucet_mint"


_OPERATION_ORDER = (
    AssetOperationV1.TRANSFER,
    AssetOperationV1.GENERIC_MINT,
    AssetOperationV1.GENERIC_BURN,
    AssetOperationV1.FAUCET_MINT,
)


class ManagedAssetRejectCodeV1(str, Enum):
    PROTOCOL_AUTHORITY_REQUIRED = "protocol_authority_required"


def _require_canonical_asset_id(asset_id: object) -> str:
    if type(asset_id) is not str:
        raise TypeError("asset_id must have exact type str")
    if len(asset_id) != 66 or not asset_id.startswith("0x"):
        raise ValueError("asset_id must be canonical 0x-prefixed 32-byte lowercase hex")
    if any(character not in _LOWER_HEX for character in asset_id[2:]):
        raise ValueError("asset_id must be canonical 0x-prefixed 32-byte lowercase hex")
    return asset_id


@dataclass(frozen=True)
class ManagedAssetPolicyV1:
    asset_id: str
    authority_id: str
    allowed_operations: tuple[AssetOperationV1, ...]

    def __post_init__(self) -> None:
        _require_canonical_asset_id(self.asset_id)
        if type(self.authority_id) is not str or not self.authority_id:
            raise TypeError("authority_id must be a nonempty exact str")
        try:
            self.authority_id.encode("ascii")
        except UnicodeEncodeError as exc:
            raise ValueError("authority_id must be ASCII") from exc
        if type(self.allowed_operations) is not tuple:
            raise TypeError("allowed_operations must have exact type tuple")
        if any(type(operation) is not AssetOperationV1 for operation in self.allowed_operations):
            raise TypeError("allowed_operations entries must have exact type AssetOperationV1")
        canonical_operations = tuple(
            operation for operation in _OPERATION_ORDER if operation in self.allowed_operations
        )
        if canonical_operations != self.allowed_operations:
            raise ValueError("allowed_operations must be unique and in canonical order")


@dataclass(frozen=True)
class ManagedAssetRejectV1:
    code: ManagedAssetRejectCodeV1
    asset_id: str
    operation: AssetOperationV1
    required_authority_id: str

    def message(self) -> str:
        return (
            f"managed asset operation {self.operation.value} requires authority "
            f"{self.required_authority_id}"
        )


def build_zusd_managed_asset_policy(asset_id: str) -> ManagedAssetPolicyV1:
    return ManagedAssetPolicyV1(
        asset_id=asset_id,
        authority_id=ZUSD_MONETARY_AUTHORITY_V1,
        allowed_operations=(AssetOperationV1.TRANSFER,),
    )


def check_managed_asset_operation(
    *,
    policy: ManagedAssetPolicyV1,
    asset_id: str,
    operation: AssetOperationV1,
) -> ManagedAssetRejectV1 | None:
    """Return a typed reject when a generic surface lacks asset authority."""

    if type(policy) is not ManagedAssetPolicyV1:
        raise TypeError("policy must have exact type ManagedAssetPolicyV1")
    canonical_asset_id = _require_canonical_asset_id(asset_id)
    if type(operation) is not AssetOperationV1:
        raise TypeError("operation must have exact type AssetOperationV1")
    if canonical_asset_id != policy.asset_id or operation in policy.allowed_operations:
        return None
    return ManagedAssetRejectV1(
        code=ManagedAssetRejectCodeV1.PROTOCOL_AUTHORITY_REQUIRED,
        asset_id=canonical_asset_id,
        operation=operation,
        required_authority_id=policy.authority_id,
    )


__all__ = [
    "AssetOperationV1",
    "ManagedAssetPolicyV1",
    "ManagedAssetRejectCodeV1",
    "ManagedAssetRejectV1",
    "ZUSD_MONETARY_AUTHORITY_V1",
    "build_zusd_managed_asset_policy",
    "check_managed_asset_operation",
]
