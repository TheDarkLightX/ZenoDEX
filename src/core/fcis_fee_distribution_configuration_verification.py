"""Pure self-consistency validation for unmounted fee-configuration claims."""

from __future__ import annotations

from .fcis_fee_apportionment_values import SRGD_ALGORITHM_VERSION_V1
from .fcis_fee_distribution_configuration_codec import (
    canonical_fee_distribution_configuration_root_v2,
    canonical_fee_distribution_policy_root_v2,
)
from .fcis_fee_distribution_configuration_values import (
    PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    FeeDistributionConfigurationClaimV2,
    FeeDistributionConfigurationVerificationCodeV2,
    FeeDistributionConfigurationVerificationRejectV2,
    FeeDistributionConfigurationVerificationResultV2,
    ValidatedFeeDistributionConfigurationClaimV2,
    _validated_fee_distribution_configuration_claim_v2,
)


def _reject_v2(
    code: FeeDistributionConfigurationVerificationCodeV2,
    *path: str,
) -> FeeDistributionConfigurationVerificationRejectV2:
    return FeeDistributionConfigurationVerificationRejectV2(code, path)


def validate_fee_distribution_configuration_claim_v2(
    claim: object,
) -> FeeDistributionConfigurationVerificationResultV2:
    """Recompute self-consistency without creating protocol authority."""

    if type(claim) is not FeeDistributionConfigurationClaimV2:
        return _reject_v2(
            FeeDistributionConfigurationVerificationCodeV2.WRONG_EXACT_TYPE,
            "configuration",
        )
    try:
        claim.__post_init__()
    except (TypeError, ValueError):
        return _reject_v2(
            FeeDistributionConfigurationVerificationCodeV2.INVALID_CLAIM,
            "configuration",
        )
    body = claim.body
    if body.algorithm_version != SRGD_ALGORITHM_VERSION_V1:
        return _reject_v2(
            FeeDistributionConfigurationVerificationCodeV2.ALGORITHM_VERSION_MISMATCH,
            "configuration",
            "body",
            "algorithm_version",
        )
    if body.accepted_language_version != PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2:
        return _reject_v2(
            FeeDistributionConfigurationVerificationCodeV2.ACCEPTED_LANGUAGE_VERSION_MISMATCH,
            "configuration",
            "body",
            "accepted_language_version",
        )
    if body.policy_root != canonical_fee_distribution_policy_root_v2(body.policy):
        return _reject_v2(
            FeeDistributionConfigurationVerificationCodeV2.POLICY_ROOT_MISMATCH,
            "configuration",
            "body",
            "policy_root",
        )
    if claim.configuration_root != canonical_fee_distribution_configuration_root_v2(body):
        return _reject_v2(
            FeeDistributionConfigurationVerificationCodeV2.CONFIGURATION_ROOT_MISMATCH,
            "configuration",
            "configuration_root",
        )
    return _validated_fee_distribution_configuration_claim_v2(claim)


def revalidate_fee_distribution_configuration_claim_v2(
    value: object,
) -> bool:
    """Defensively re-run self-consistency at a later validation boundary."""

    if type(value) is not ValidatedFeeDistributionConfigurationClaimV2:
        return False
    try:
        claim = FeeDistributionConfigurationClaimV2(
            value.body,
            value.configuration_root,
        )
    except (TypeError, ValueError):
        return False
    result = validate_fee_distribution_configuration_claim_v2(claim)
    return type(result) is ValidatedFeeDistributionConfigurationClaimV2


__all__ = (
    "revalidate_fee_distribution_configuration_claim_v2",
    "validate_fee_distribution_configuration_claim_v2",
)
