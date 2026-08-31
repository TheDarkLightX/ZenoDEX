"""Canonical primitives and lane-level base values for GlobalSettlementABI V2."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from enum import Enum
from typing import Any, Final, Mapping, Protocol, cast, runtime_checkable

from ..state.canonical import canonical_json_bytes, domain_sep_bytes

GLOBAL_SETTLEMENT_ABI_V2: Final = "zenodex/global-settlement-abi/v2"
MAX_TOKEN_BYTES_V2: Final = 160
MAX_U64_V2: Final = (1 << 64) - 1
MAX_ATOMS_V2: Final = (1 << 128) - 1
MIN_DELTA_ATOMS_V2: Final = -(1 << 127)
MAX_DELTA_ATOMS_V2: Final = (1 << 127) - 1
ZERO_ROOT_V2: Final = "0x" + "00" * 32


@runtime_checkable
class _CanonicalizableV2(Protocol):
    def to_canonical(self) -> object: ...


def _require_nonnegative_int_v2(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    if value > MAX_U64_V2:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_atoms_u128_v2(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    if value > MAX_ATOMS_V2:
        raise ValueError(f"{name} must fit an unsigned 128-bit integer")
    return value


def _require_delta_atoms_i128_v2(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer")
    if not MIN_DELTA_ATOMS_V2 <= value <= MAX_DELTA_ATOMS_V2:
        raise ValueError(f"{name} must fit a signed 128-bit integer")
    return value


def _require_bool_v2(value: object, *, name: str) -> bool:
    if type(value) is not bool:
        raise TypeError(f"{name} must be bool")
    return value


def _require_token_v2(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must not be empty")
    if len(value.encode("utf-8")) > MAX_TOKEN_BYTES_V2:
        raise ValueError(f"{name} exceeds {MAX_TOKEN_BYTES_V2} UTF-8 bytes")
    if any(ord(char) < 0x21 or ord(char) > 0x7E for char in value):
        raise ValueError(f"{name} must use printable ASCII")
    return value


def _require_root_v2(value: object, *, name: str, allow_zero: bool = False) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if len(value) != 66 or not value.startswith("0x") or value != value.lower():
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed 32-byte hex")
    if any(char not in "0123456789abcdef" for char in value[2:]):
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed 32-byte hex")
    if not allow_zero and value == ZERO_ROOT_V2:
        raise ValueError(f"{name} must be nonzero")
    return value


def _canonical_value_v2(value: object) -> object:
    if value is None or type(value) in {bool, int, str}:
        return value
    if isinstance(value, Enum):
        return _canonical_value_v2(value.value)
    if isinstance(value, bool | int | str):
        raise TypeError("canonical scalar subclasses are unsupported")
    if type(value) is tuple or type(value) is list:
        return [_canonical_value_v2(item) for item in value]
    if isinstance(value, tuple | list):
        raise TypeError("canonical sequence subclasses are unsupported")
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise TypeError("canonical mapping keys must be strings")
        return {
            key: _canonical_value_v2(item)
            for key, item in sorted(value.items(), key=lambda pair: pair[0])
        }
    if isinstance(value, Mapping):
        raise TypeError("canonical mapping subclasses are unsupported")
    if isinstance(value, _CanonicalizableV2):
        return _canonical_value_v2(value.to_canonical())
    raise TypeError("unsupported canonical value type")


def canonical_global_bytes_v2(value: object) -> bytes:
    """Encode a typed V2 value as deterministic canonical JSON."""

    encoded: object = canonical_json_bytes(_canonical_value_v2(value))
    if type(encoded) is not bytes:
        raise TypeError("canonical encoder returned an invalid value")
    return encoded


def hash_global_v2(domain: str, value: object) -> str:
    """Hash a canonical value under a V2-only ASCII domain."""

    _require_token_v2(domain, name="hash domain")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes(domain, version=2))
    digest.update(canonical_global_bytes_v2(value))
    return "0x" + digest.hexdigest()


def canonical_economic_command_body_bytes_v2(
    command_kind: str,
    command: object,
) -> bytes:
    _require_token_v2(command_kind, name="economic command body kind")
    return canonical_global_bytes_v2(
        {
            "command_kind": command_kind,
            "command": command,
        }
    )


def hash_economic_command_body_bytes_v2(command_body_bytes: bytes) -> str:
    if type(command_body_bytes) is not bytes:
        raise TypeError("economic command body bytes must be exact bytes")
    if not command_body_bytes:
        raise ValueError("economic command body bytes must not be empty")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes("authenticated-economic-command-body-v2", version=2))
    digest.update(command_body_bytes)
    return "0x" + digest.hexdigest()


def hash_economic_command_body_v2(command_kind: str, command: object) -> str:
    return hash_economic_command_body_bytes_v2(
        canonical_economic_command_body_bytes_v2(command_kind, command)
    )


def _require_tuple_v2(value: object, *, name: str) -> tuple[object, ...]:
    if type(value) is not tuple:
        raise TypeError(f"{name} must be a tuple")
    return value


def _require_sorted_unique_tokens_v2(
    values: object,
    *,
    name: str,
    allow_empty: bool = True,
) -> tuple[str, ...]:
    items = _require_tuple_v2(values, name=name)
    normalized = tuple(
        _require_token_v2(item, name=f"{name}[{index}]") for index, item in enumerate(items)
    )
    if not allow_empty and not normalized:
        raise ValueError(f"{name} must not be empty")
    if normalized != tuple(sorted(set(normalized))):
        raise ValueError(f"{name} must be sorted and unique")
    return normalized


def _require_ordered_objects_v2(
    values: object,
    *,
    name: str,
    expected_type: type[object],
    key: str,
) -> tuple[object, ...]:
    items = _require_tuple_v2(values, name=name)
    if any(type(item) is not expected_type for item in items):
        raise TypeError(f"{name} contains an invalid value")
    keys = tuple(getattr(item, key) for item in items)
    if keys != tuple(sorted(set(keys))):
        raise ValueError(f"{name} must be canonically ordered and unique")
    return items


def _snapshot_dataclass_tuple_v2(
    values: object,
    expected_type: type[Any],
    name: str,
) -> tuple[Any, ...]:
    items = _require_tuple_v2(values, name=name)
    if any(type(item) is not expected_type for item in items):
        raise TypeError(f"{name} must contain exact typed values")
    return tuple(replace(cast(Any, item)) for item in items)


class LaneIdV2(str, Enum):
    ASSET_TRANSFER = "ASSET_TRANSFER"
    SPOT_LIQUIDITY = "SPOT_LIQUIDITY"
    FARM_INCENTIVES = "FARM_INCENTIVES"
    ZDEX_TOKENOMICS = "ZDEX_TOKENOMICS"
    ZUSD_MONETARY = "ZUSD_MONETARY"
    PERPS_MARKET = "PERPS_MARKET"
    ORACLE_MARKET = "ORACLE_MARKET"
    SEALED_AUCTION = "SEALED_AUCTION"
    STRATEGY_ESCROW = "STRATEGY_ESCROW"
    PROOF_REWARDS = "PROOF_REWARDS"
    EXTERNAL_CUSTODY = "EXTERNAL_CUSTODY"
    GOVERNANCE_MIGRATION = "GOVERNANCE_MIGRATION"


ALL_LANE_IDS_V2: Final = tuple(LaneIdV2)


@dataclass(frozen=True, slots=True, order=True)
class EconomicAmountV2:
    owner: str
    asset: str
    custody_domain: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.owner, name="economic amount owner")
        _require_token_v2(self.asset, name="economic amount asset")
        _require_token_v2(self.custody_domain, name="economic amount custody domain")
        _require_atoms_u128_v2(self.amount_atoms, name="economic amount atoms")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.asset, self.owner, self.custody_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "owner": self.owner,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class AssetSupplyV2:
    asset: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="supply asset")
        _require_atoms_u128_v2(self.amount_atoms, name="supply atoms")

    def to_canonical(self) -> dict[str, object]:
        return {"asset": self.asset, "amount_atoms": self.amount_atoms}


__all__ = [
    "GLOBAL_SETTLEMENT_ABI_V2",
    "MAX_TOKEN_BYTES_V2",
    "MAX_U64_V2",
    "MAX_ATOMS_V2",
    "MIN_DELTA_ATOMS_V2",
    "MAX_DELTA_ATOMS_V2",
    "ZERO_ROOT_V2",
    "LaneIdV2",
    "ALL_LANE_IDS_V2",
    "EconomicAmountV2",
    "AssetSupplyV2",
    "canonical_global_bytes_v2",
    "canonical_economic_command_body_bytes_v2",
    "hash_economic_command_body_bytes_v2",
    "hash_economic_command_body_v2",
    "hash_global_v2",
]
