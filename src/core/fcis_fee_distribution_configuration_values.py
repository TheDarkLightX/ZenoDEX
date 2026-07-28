"""Exact candidate and controlled values for fee-distribution configuration."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    FeeDistributionPolicySourceV2,
    FeeDistributionPolicyV2,
)

FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2 = "zenodex/fcis/fee-distribution/configuration/v2"
FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2 = (
    "zenodex/fcis/fee-distribution/configuration-body/v2"
)
FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2 = (
    "zenodex/fcis/fee-distribution/configuration-claim/v2"
)
VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2 = (
    "zenodex/fcis/fee-distribution/validated-configuration-claim/v2"
)
PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2 = "PROVISIONAL_FEES_NO_SAME_BATCH_FUNDING_V2"

_VALIDATED_FEE_CONFIGURATION_CLAIM_TOKEN_V2 = object()


class FCISFeeDistributionConfigurationEnumTagV2(Enum):
    """This closed profile intentionally has no enum variants."""


class FCISFeeDistributionConfigurationRecordTagV2(Enum):
    DISTRIBUTION_POLICY = "fee_distribution_policy_v2"
    CONFIGURATION_BODY = "fee_distribution_configuration_body_v2"
    CONFIGURATION_CLAIM = "fee_distribution_configuration_claim_v2"


class FeeDistributionConfigurationVerificationCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_CLAIM = "invalid_claim"
    ALGORITHM_VERSION_MISMATCH = "algorithm_version_mismatch"
    ACCEPTED_LANGUAGE_VERSION_MISMATCH = "accepted_language_version_mismatch"
    POLICY_ROOT_MISMATCH = "policy_root_mismatch"
    CONFIGURATION_ROOT_MISMATCH = "configuration_root_mismatch"


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionConfigurationBodySourceV2:
    chain_deployment_id: object
    configuration_version: object
    fee_distribution_domain_id: object
    policy_root: object
    policy: object
    activation_sequence: object
    algorithm_version: object
    accepted_language_version: object


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionConfigurationClaimSourceV2:
    body: object
    configuration_root: object


def _require_text_v2(name: str, value: object) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


def _require_u256_v2(name: str, value: object, *, positive: bool) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    minimum = 1 if positive else 0
    if not minimum <= value <= MAX_FEE_AMOUNT_V2:
        raise ValueError(f"{name} is outside its U256 domain")
    return value


def _require_digest_v2(name: str, value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 32-byte hex digest")
    return value


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionConfigurationBodyV2:
    chain_deployment_id: str
    configuration_version: int
    fee_distribution_domain_id: str
    policy_root: str
    policy: FeeDistributionPolicyV2
    activation_sequence: int
    algorithm_version: str
    accepted_language_version: str

    def __post_init__(self) -> None:
        _require_text_v2("chain deployment identifier", self.chain_deployment_id)
        _require_u256_v2(
            "fee configuration version",
            self.configuration_version,
            positive=True,
        )
        _require_text_v2(
            "fee distribution domain identifier",
            self.fee_distribution_domain_id,
        )
        _require_digest_v2("fee distribution policy root", self.policy_root)
        if type(self.policy) is not FeeDistributionPolicyV2:
            raise TypeError("fee distribution policy must be exact")
        self.policy.__post_init__()
        _require_u256_v2(
            "fee configuration activation sequence",
            self.activation_sequence,
            positive=False,
        )
        _require_text_v2("fee algorithm version", self.algorithm_version)
        _require_text_v2(
            "fee accepted-language version",
            self.accepted_language_version,
        )


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionConfigurationClaimV2:
    body: FeeDistributionConfigurationBodyV2
    configuration_root: str

    def __post_init__(self) -> None:
        if type(self.body) is not FeeDistributionConfigurationBodyV2:
            raise TypeError("fee configuration claim body must be exact")
        self.body.__post_init__()
        _require_digest_v2("fee distribution configuration root", self.configuration_root)


@final
@dataclass(frozen=True, slots=True)
class ValidatedFeeDistributionConfigurationClaimV2:
    """Controlled self-consistency result carrying no protocol authority."""

    body: FeeDistributionConfigurationBodyV2
    configuration_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _VALIDATED_FEE_CONFIGURATION_CLAIM_TOKEN_V2:
            raise TypeError("validated fee configuration claim requires verification")
        FeeDistributionConfigurationClaimV2(
            self.body,
            self.configuration_root,
        )


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionConfigurationVerificationRejectV2:
    code: FeeDistributionConfigurationVerificationCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FeeDistributionConfigurationVerificationCodeV2:
            raise TypeError("fee configuration verification code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("fee configuration rejection path must be exact")


FeeDistributionConfigurationVerificationResultV2: TypeAlias = (
    ValidatedFeeDistributionConfigurationClaimV2 | FeeDistributionConfigurationVerificationRejectV2
)


def _validated_fee_distribution_configuration_claim_v2(
    claim: FeeDistributionConfigurationClaimV2,
) -> ValidatedFeeDistributionConfigurationClaimV2:
    return ValidatedFeeDistributionConfigurationClaimV2(
        claim.body,
        claim.configuration_root,
        _VALIDATED_FEE_CONFIGURATION_CLAIM_TOKEN_V2,
    )


__all__ = (
    "FCISFeeDistributionConfigurationEnumTagV2",
    "FCISFeeDistributionConfigurationRecordTagV2",
    "FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2",
    "FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2",
    "FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2",
    "FeeDistributionConfigurationBodySourceV2",
    "FeeDistributionConfigurationBodyV2",
    "FeeDistributionConfigurationClaimSourceV2",
    "FeeDistributionConfigurationClaimV2",
    "FeeDistributionConfigurationVerificationCodeV2",
    "FeeDistributionConfigurationVerificationRejectV2",
    "FeeDistributionConfigurationVerificationResultV2",
    "FeeDistributionPolicySourceV2",
    "PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2",
    "SRGD_ALGORITHM_VERSION_V1",
    "VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2",
    "ValidatedFeeDistributionConfigurationClaimV2",
)
