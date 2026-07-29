from __future__ import annotations

import pytest

from src.core.fcis_fee_apportionment_values import (
    SRGD_ALGORITHM_VERSION_V1,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_distribution_configuration_codec import (
    canonical_fee_distribution_configuration_root_v2,
    canonical_fee_distribution_policy_root_v2,
)
from src.core.fcis_fee_distribution_configuration_content_validation import (
    validate_owned_fee_distribution_configuration_content_v2,
)
from src.core.fcis_fee_distribution_configuration_values import (
    PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
    FeeDistributionConfigurationVerificationCodeV2,
    FeeDistributionConfigurationVerificationRejectV2,
    ValidatedFeeDistributionConfigurationClaimV2,
)

ZERO = "0x" + ("0" * 64)


def _claim(
    *,
    algorithm_version: str = SRGD_ALGORITHM_VERSION_V1,
    accepted_language_version: str = PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
) -> FeeDistributionConfigurationClaimV2:
    policy = FeeDistributionPolicyV2(3_333, 3_333, 3_334, "buyback", "treasury", "rewards")
    body = FeeDistributionConfigurationBodyV2(
        "zenodex:testnet",
        8,
        "protocol-fees",
        canonical_fee_distribution_policy_root_v2(policy),
        policy,
        12,
        algorithm_version,
        accepted_language_version,
    )
    return FeeDistributionConfigurationClaimV2(
        body,
        canonical_fee_distribution_configuration_root_v2(body),
    )


def _reject(value: object) -> FeeDistributionConfigurationVerificationRejectV2:
    assert type(value) is FeeDistributionConfigurationVerificationRejectV2
    return value


def test_valid_content_is_reconstructed_and_semantically_revalidated() -> None:
    claim = _claim()
    result = validate_owned_fee_distribution_configuration_content_v2(claim)

    assert type(result) is ValidatedFeeDistributionConfigurationClaimV2
    assert result.body == claim.body
    assert result.body is not claim.body
    assert result.body.policy == claim.body.policy
    assert result.body.policy is not claim.body.policy
    assert result.configuration_root == claim.configuration_root


@pytest.mark.parametrize(
    ("algorithm", "language", "code"),
    (
        (
            "OTHER_ALGORITHM",
            PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
            FeeDistributionConfigurationVerificationCodeV2.ALGORITHM_VERSION_MISMATCH,
        ),
        (
            SRGD_ALGORITHM_VERSION_V1,
            "OTHER_LANGUAGE",
            FeeDistributionConfigurationVerificationCodeV2.ACCEPTED_LANGUAGE_VERSION_MISMATCH,
        ),
    ),
)
def test_command_root_cannot_make_wrong_algorithm_or_language_valid(
    algorithm: str,
    language: str,
    code: FeeDistributionConfigurationVerificationCodeV2,
) -> None:
    result = validate_owned_fee_distribution_configuration_content_v2(
        _claim(algorithm_version=algorithm, accepted_language_version=language)
    )
    assert _reject(result).code is code


def test_recomputed_outer_root_cannot_hide_wrong_policy_root() -> None:
    claim = _claim()
    object.__setattr__(claim.body, "policy_root", ZERO)
    object.__setattr__(
        claim,
        "configuration_root",
        canonical_fee_distribution_configuration_root_v2(claim.body),
    )

    result = validate_owned_fee_distribution_configuration_content_v2(claim)
    assert _reject(result).code is (
        FeeDistributionConfigurationVerificationCodeV2.POLICY_ROOT_MISMATCH
    )


def test_wrong_embedded_configuration_root_rejects() -> None:
    claim = _claim()
    object.__setattr__(claim, "configuration_root", ZERO)

    result = validate_owned_fee_distribution_configuration_content_v2(claim)
    assert _reject(result).code is (
        FeeDistributionConfigurationVerificationCodeV2.CONFIGURATION_ROOT_MISMATCH
    )


def test_wrong_top_level_type_never_becomes_validated_content() -> None:
    result = validate_owned_fee_distribution_configuration_content_v2(object())
    assert _reject(result).code is FeeDistributionConfigurationVerificationCodeV2.WRONG_EXACT_TYPE
