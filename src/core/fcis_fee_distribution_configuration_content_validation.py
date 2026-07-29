"""Fresh-owned B1A semantic validation for untrusted configuration content.

The helper composes an already admitted exact configuration claim with the
existing B1A semantic verifier.  It returns a newly owned validated claim or the
original closed B1A rejection.  It creates no deployment, state, transition,
publication, or mount authority.
"""

from __future__ import annotations

from .fcis_fee_apportionment_values import FeeDistributionPolicyV2
from .fcis_fee_distribution_configuration_values import (
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
    FeeDistributionConfigurationVerificationResultV2,
    ValidatedFeeDistributionConfigurationClaimV2,
)
from .fcis_fee_distribution_configuration_verification import (
    revalidate_fee_distribution_configuration_claim_v2,
    validate_fee_distribution_configuration_claim_v2,
)


def _fresh_owned_claim_v2(
    value: ValidatedFeeDistributionConfigurationClaimV2,
) -> FeeDistributionConfigurationClaimV2:
    body = value.body
    policy = body.policy
    fresh_policy = FeeDistributionPolicyV2(
        policy.buyback_bps,
        policy.treasury_bps,
        policy.rewards_bps,
        policy.buyback_destination,
        policy.treasury_destination,
        policy.rewards_destination,
    )
    fresh_body = FeeDistributionConfigurationBodyV2(
        body.chain_deployment_id,
        body.configuration_version,
        body.fee_distribution_domain_id,
        body.policy_root,
        fresh_policy,
        body.activation_sequence,
        body.algorithm_version,
        body.accepted_language_version,
    )
    return FeeDistributionConfigurationClaimV2(
        fresh_body,
        value.configuration_root,
    )


def validate_owned_fee_distribution_configuration_content_v2(
    claim: object,
) -> FeeDistributionConfigurationVerificationResultV2:
    """Validate semantics, reconstruct ownership, and validate again.

    Structural admission remains a separate decode-edge phase.  This helper is
    the mandatory semantic phase before any independently expected root may
    treat configuration content as the meaning of that root.
    """

    first = validate_fee_distribution_configuration_claim_v2(claim)
    if type(first) is not ValidatedFeeDistributionConfigurationClaimV2:
        return first
    fresh_claim = _fresh_owned_claim_v2(first)
    second = validate_fee_distribution_configuration_claim_v2(fresh_claim)
    if type(second) is not ValidatedFeeDistributionConfigurationClaimV2:
        return second
    if not revalidate_fee_distribution_configuration_claim_v2(second):
        raise ValueError("fresh-owned configuration validation was not stable")
    return second


__all__ = ("validate_owned_fee_distribution_configuration_content_v2",)
