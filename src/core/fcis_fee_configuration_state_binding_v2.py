"""Bind one self-consistent fee configuration to an exact state projection.

The state projection is canonical candidate data.  This module establishes
that its exact authority header commits the validated configuration.  It does
not establish datastore currentness, full-state projection correctness,
publication authority, or a runtime mount.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast, final
from weakref import WeakValueDictionary

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_b1b_authority_values import FCISAuthorityHeaderV2
from .fcis_fee_distribution_configuration_codec import (
    canonical_fee_distribution_configuration_root_v2,
)
from .fcis_fee_distribution_configuration_values import (
    ValidatedFeeDistributionConfigurationClaimV2,
)
from .fcis_fee_distribution_configuration_verification import (
    revalidate_fee_distribution_configuration_claim_v2,
)

EXACT_FEE_AUTHORITY_STATE_PROJECTION_SCHEMA_V2: Final = (
    "zenodex/fcis/fee-configuration/exact-state-projection/v2"
)
STATE_BOUND_ACTIVE_FEE_CONFIGURATION_SCHEMA_V2: Final = (
    "zenodex/fcis/fee-configuration/state-bound-active/v2"
)

_STATE_BOUND_CONFIGURATION_TOKEN_V2 = object()
_LOWER_HEX = frozenset("0123456789abcdef")
_MAX_U32 = (1 << 32) - 1


class FeeConfigurationStateBindingRejectCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_STATE_PROJECTION = "invalid_state_projection"
    INVALID_CONFIGURATION = "invalid_configuration"
    CONFIGURATION_ROOT_MISMATCH = "configuration_root_mismatch"
    DEPLOYMENT_MISMATCH = "deployment_mismatch"
    ACTIVATION_SEQUENCE_IN_FUTURE = "activation_sequence_in_future"


def _digest32(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in _LOWER_HEX for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 32-byte hex digest")
    return value


def _sha256_digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _LOWER_HEX for character in value)
    ):
        raise TypeError(f"{name} must be a lowercase SHA-256 digest")
    return value


def _custody_pubkey(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 98
        or not value.startswith("0x")
        or any(character not in _LOWER_HEX for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 48-byte hex public key")
    return value


def _u32(value: object, name: str) -> int:
    if type(value) is not int or not 0 <= value <= _MAX_U32:
        raise TypeError(f"{name} must be an exact U32 integer")
    return value


def _state_projection_body_v2(
    value: ExactFeeAuthorityStateProjectionV2,
) -> dict[str, object]:
    header = value.authority_header
    return {
        "schema": EXACT_FEE_AUTHORITY_STATE_PROJECTION_SCHEMA_V2,
        "global_state_root": value.global_state_root,
        "zusd_state_root": value.zusd_state_root,
        "protocol_fee_claim_state_root": value.protocol_fee_claim_state_root,
        "protocol_fee_role_claim_state_root": value.protocol_fee_role_claim_state_root,
        "fee_apportionment_state_root": value.fee_apportionment_state_root,
        "deployment_config_root": value.deployment_config_root,
        "authority_epoch_index": value.authority_epoch_index,
        "zusd_asset_id": value.zusd_asset_id,
        "protocol_fee_claim_custody_pubkey": value.protocol_fee_claim_custody_pubkey,
        "authority_header": {
            "chain_deployment_id": header.chain_deployment_id,
            "sequence": header.sequence,
            "fee_distribution_configuration_root": (header.fee_distribution_configuration_root),
        },
    }


def _state_projection_root_v2(
    value: ExactFeeAuthorityStateProjectionV2,
) -> str:
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("fcis_fee_authority_state_projection", version=2)
            + canonical_json_bytes(_state_projection_body_v2(value))
        ),
    )


@final
@dataclass(frozen=True, slots=True)
class ExactFeeAuthorityStateProjectionV2:
    """Canonical candidate projection; never store-current authority."""

    global_state_root: str
    zusd_state_root: str
    protocol_fee_claim_state_root: str
    protocol_fee_role_claim_state_root: str
    fee_apportionment_state_root: str
    deployment_config_root: str
    authority_epoch_index: int
    zusd_asset_id: str
    protocol_fee_claim_custody_pubkey: str
    authority_header: FCISAuthorityHeaderV2

    def __post_init__(self) -> None:
        _digest32(self.global_state_root, "global state root")
        _digest32(self.zusd_state_root, "zUSD state root")
        _digest32(self.protocol_fee_claim_state_root, "protocol fee claim state root")
        _digest32(
            self.protocol_fee_role_claim_state_root,
            "protocol fee role-claim state root",
        )
        _digest32(self.fee_apportionment_state_root, "fee apportionment state root")
        _sha256_digest(self.deployment_config_root, "deployment configuration root")
        _u32(self.authority_epoch_index, "authority epoch index")
        _digest32(self.zusd_asset_id, "zUSD asset identifier")
        _custody_pubkey(
            self.protocol_fee_claim_custody_pubkey,
            "protocol fee claim custody public key",
        )
        if type(self.authority_header) is not FCISAuthorityHeaderV2:
            raise TypeError("authority header must be exact")
        self.authority_header.__post_init__()

    @property
    def state_projection_root(self) -> str:
        self.__post_init__()
        return _state_projection_root_v2(self)


def _binding_body_v2(
    *,
    state_projection_root: str,
    configuration_root: str,
) -> dict[str, object]:
    return {
        "schema": STATE_BOUND_ACTIVE_FEE_CONFIGURATION_SCHEMA_V2,
        "state_projection_root": state_projection_root,
        "configuration_root": configuration_root,
    }


def _binding_root_v2(
    *,
    state_projection_root: str,
    configuration_root: str,
) -> str:
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("fcis_state_bound_active_fee_configuration", version=2)
            + canonical_json_bytes(
                _binding_body_v2(
                    state_projection_root=state_projection_root,
                    configuration_root=configuration_root,
                )
            )
        ),
    )


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class StateBoundActiveFeeConfigurationV2:
    """Controlled proof that one exact header commits one B1A-valid configuration."""

    exact_state_projection: ExactFeeAuthorityStateProjectionV2
    validated_configuration: ValidatedFeeDistributionConfigurationClaimV2
    binding_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _STATE_BOUND_CONFIGURATION_TOKEN_V2:
            raise TypeError("state-bound fee configuration requires state binding")
        _validate_bound_value_fields_v2(self)

    @property
    def state_projection_root(self) -> str:
        return self.exact_state_projection.state_projection_root

    @property
    def configuration_root(self) -> str:
        return cast(str, self.validated_configuration.configuration_root)

    @property
    def chain_deployment_id(self) -> str:
        return cast(str, self.validated_configuration.body.chain_deployment_id)

    @property
    def activation_sequence(self) -> int:
        return cast(int, self.validated_configuration.body.activation_sequence)


@final
@dataclass(frozen=True, slots=True)
class FeeConfigurationStateBindingRejectV2:
    code: FeeConfigurationStateBindingRejectCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FeeConfigurationStateBindingRejectCodeV2:
            raise TypeError("binding rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("binding rejection path must be an exact string tuple")


FeeConfigurationStateBindingResultV2: TypeAlias = (
    StateBoundActiveFeeConfigurationV2 | FeeConfigurationStateBindingRejectV2
)

_BOUND_VALUES_V2: WeakValueDictionary[int, StateBoundActiveFeeConfigurationV2] = (
    WeakValueDictionary()
)
_BOUND_SNAPSHOTS_V2: dict[int, tuple[object, ...]] = {}


def _bound_snapshot_v2(
    value: StateBoundActiveFeeConfigurationV2,
) -> tuple[object, ...]:
    return (
        value.state_projection_root,
        value.configuration_root,
        value.binding_root,
    )


def _register_bound_value_v2(
    value: StateBoundActiveFeeConfigurationV2,
) -> StateBoundActiveFeeConfigurationV2:
    identity = id(value)
    _BOUND_VALUES_V2[identity] = value
    _BOUND_SNAPSHOTS_V2[identity] = _bound_snapshot_v2(value)
    return value


def _projection_is_valid_v2(value: object) -> bool:
    if type(value) is not ExactFeeAuthorityStateProjectionV2:
        return False
    try:
        value.__post_init__()
        _digest32(value.state_projection_root, "state projection root")
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError):
        return False
    return True


def _validate_bound_value_fields_v2(
    value: StateBoundActiveFeeConfigurationV2,
) -> None:
    if not _projection_is_valid_v2(value.exact_state_projection):
        raise ValueError("state projection is invalid")
    if not revalidate_fee_distribution_configuration_claim_v2(value.validated_configuration):
        raise ValueError("validated configuration is invalid")
    header = value.exact_state_projection.authority_header
    configuration = value.validated_configuration
    if configuration.configuration_root != canonical_fee_distribution_configuration_root_v2(
        configuration.body
    ):
        raise ValueError("configuration root is not canonical")
    if configuration.configuration_root != header.fee_distribution_configuration_root:
        raise ValueError("configuration root is not committed by the header")
    if configuration.body.chain_deployment_id != header.chain_deployment_id:
        raise ValueError("configuration deployment is not committed by the header")
    if configuration.body.activation_sequence > header.sequence:
        raise ValueError("configuration activation is in the future")
    expected_root = _binding_root_v2(
        state_projection_root=value.exact_state_projection.state_projection_root,
        configuration_root=configuration.configuration_root,
    )
    if _digest32(value.binding_root, "binding root") != expected_root:
        raise ValueError("binding root is not canonical")


def _reject_v2(
    code: FeeConfigurationStateBindingRejectCodeV2,
    *path: str,
) -> FeeConfigurationStateBindingRejectV2:
    return FeeConfigurationStateBindingRejectV2(code, tuple(path))


def bind_fee_configuration_to_state_projection_v2(
    *,
    exact_state_projection: object,
    validated_configuration: object,
) -> FeeConfigurationStateBindingResultV2:
    """Bind exact projection data and B1A evidence with deterministic precedence."""

    if type(exact_state_projection) is not ExactFeeAuthorityStateProjectionV2:
        return _reject_v2(
            FeeConfigurationStateBindingRejectCodeV2.WRONG_EXACT_TYPE,
            "exact_state_projection",
        )
    if not _projection_is_valid_v2(exact_state_projection):
        return _reject_v2(
            FeeConfigurationStateBindingRejectCodeV2.INVALID_STATE_PROJECTION,
            "exact_state_projection",
        )
    if not revalidate_fee_distribution_configuration_claim_v2(validated_configuration):
        return _reject_v2(
            FeeConfigurationStateBindingRejectCodeV2.INVALID_CONFIGURATION,
            "validated_configuration",
        )
    configuration = cast(
        ValidatedFeeDistributionConfigurationClaimV2,
        validated_configuration,
    )
    header = exact_state_projection.authority_header
    if configuration.configuration_root != header.fee_distribution_configuration_root:
        return _reject_v2(
            FeeConfigurationStateBindingRejectCodeV2.CONFIGURATION_ROOT_MISMATCH,
            "validated_configuration",
            "configuration_root",
        )
    if configuration.body.chain_deployment_id != header.chain_deployment_id:
        return _reject_v2(
            FeeConfigurationStateBindingRejectCodeV2.DEPLOYMENT_MISMATCH,
            "validated_configuration",
            "body",
            "chain_deployment_id",
        )
    if configuration.body.activation_sequence > header.sequence:
        return _reject_v2(
            FeeConfigurationStateBindingRejectCodeV2.ACTIVATION_SEQUENCE_IN_FUTURE,
            "validated_configuration",
            "body",
            "activation_sequence",
        )
    return _register_bound_value_v2(
        StateBoundActiveFeeConfigurationV2(
            exact_state_projection=exact_state_projection,
            validated_configuration=configuration,
            binding_root=_binding_root_v2(
                state_projection_root=exact_state_projection.state_projection_root,
                configuration_root=configuration.configuration_root,
            ),
            _construction_token=_STATE_BOUND_CONFIGURATION_TOKEN_V2,
        )
    )


def revalidate_state_bound_active_fee_configuration_v2(value: object) -> bool:
    """Recheck provenance, exact sources, all four B1B laws, and canonical root."""

    if type(value) is not StateBoundActiveFeeConfigurationV2:
        return False
    if _BOUND_VALUES_V2.get(id(value)) is not value:
        return False
    try:
        _validate_bound_value_fields_v2(value)
        return _BOUND_SNAPSHOTS_V2.get(id(value)) == _bound_snapshot_v2(value)
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError):
        return False


__all__ = (
    "EXACT_FEE_AUTHORITY_STATE_PROJECTION_SCHEMA_V2",
    "STATE_BOUND_ACTIVE_FEE_CONFIGURATION_SCHEMA_V2",
    "ExactFeeAuthorityStateProjectionV2",
    "FeeConfigurationStateBindingRejectCodeV2",
    "FeeConfigurationStateBindingRejectV2",
    "FeeConfigurationStateBindingResultV2",
    "StateBoundActiveFeeConfigurationV2",
    "bind_fee_configuration_to_state_projection_v2",
    "revalidate_state_bound_active_fee_configuration_v2",
)
