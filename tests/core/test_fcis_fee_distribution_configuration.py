from __future__ import annotations

import pytest

from src.core import fcis_fee_distribution_configuration_values as configuration_values
from src.core.fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_distribution_configuration_codec import (
    canonical_fee_distribution_configuration_root_v2,
    canonical_fee_distribution_policy_root_v2,
    encode_fee_distribution_configuration_v2,
)
from src.core.fcis_fee_distribution_configuration_values import (
    PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
    FeeDistributionConfigurationVerificationCodeV2,
    FeeDistributionConfigurationVerificationRejectV2,
    ValidatedFeeDistributionConfigurationClaimV2,
)
from src.core.fcis_fee_distribution_configuration_verification import (
    revalidate_fee_distribution_configuration_claim_v2,
    validate_fee_distribution_configuration_claim_v2,
)

ZERO_DIGEST = "0x" + ("0" * 64)


def _policy() -> FeeDistributionPolicyV2:
    return FeeDistributionPolicyV2(
        3_333,
        3_333,
        3_334,
        "buyback",
        "treasury",
        "rewards",
    )


def _claim(
    *,
    algorithm_version: str = SRGD_ALGORITHM_VERSION_V1,
    accepted_language_version: str = PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    activation_sequence: int = MAX_FEE_AMOUNT_V2,
    policy: FeeDistributionPolicyV2 | None = None,
    chain_deployment_id: str = "zenodex:testnet:α",
    fee_distribution_domain_id: str = "protocol-fees",
) -> FeeDistributionConfigurationClaimV2:
    selected_policy = _policy() if policy is None else policy
    body = FeeDistributionConfigurationBodyV2(
        chain_deployment_id=chain_deployment_id,
        configuration_version=7,
        fee_distribution_domain_id=fee_distribution_domain_id,
        policy_root=canonical_fee_distribution_policy_root_v2(selected_policy),
        policy=selected_policy,
        activation_sequence=activation_sequence,
        algorithm_version=algorithm_version,
        accepted_language_version=accepted_language_version,
    )
    return FeeDistributionConfigurationClaimV2(
        body,
        canonical_fee_distribution_configuration_root_v2(body),
    )


def _reject(
    result: object,
) -> FeeDistributionConfigurationVerificationRejectV2:
    assert type(result) is FeeDistributionConfigurationVerificationRejectV2
    return result


def test_valid_claim_returns_one_controlled_non_authoritative_validation() -> None:
    claim = _claim()

    result = validate_fee_distribution_configuration_claim_v2(claim)

    assert type(result) is ValidatedFeeDistributionConfigurationClaimV2
    assert result.body == claim.body
    assert result.configuration_root == claim.configuration_root
    assert revalidate_fee_distribution_configuration_claim_v2(result)
    assert encode_fee_distribution_configuration_v2(
        VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        result,
    )


def test_direct_validated_construction_is_rejected() -> None:
    claim = _claim()

    with pytest.raises(TypeError, match="requires verification"):
        ValidatedFeeDistributionConfigurationClaimV2(
            claim.body,
            claim.configuration_root,
            object(),
        )


def test_self_consistent_attacker_claim_remains_explicitly_non_authoritative() -> None:
    attacker_policy = FeeDistributionPolicyV2(
        10_000,
        0,
        0,
        "mallory",
        "unused-treasury",
        "unused-rewards",
    )
    claim = _claim(
        policy=attacker_policy,
        chain_deployment_id="attacker:deployment",
        fee_distribution_domain_id="attacker-domain",
    )

    result = validate_fee_distribution_configuration_claim_v2(claim)

    assert type(result) is ValidatedFeeDistributionConfigurationClaimV2
    assert result.body.policy.buyback_destination == "mallory"
    assert not hasattr(
        configuration_values,
        "AuthenticatedFeeDistributionConfigurationV2",
    )


@pytest.mark.parametrize(
    ("field", "expected_code"),
    (
        (
            "algorithm",
            FeeDistributionConfigurationVerificationCodeV2.ALGORITHM_VERSION_MISMATCH,
        ),
        (
            "accepted_language",
            FeeDistributionConfigurationVerificationCodeV2.ACCEPTED_LANGUAGE_VERSION_MISMATCH,
        ),
        (
            "policy_root",
            FeeDistributionConfigurationVerificationCodeV2.POLICY_ROOT_MISMATCH,
        ),
        (
            "configuration_root",
            FeeDistributionConfigurationVerificationCodeV2.CONFIGURATION_ROOT_MISMATCH,
        ),
    ),
)
def test_each_semantic_substitution_fails_at_its_intended_check(
    field: str,
    expected_code: FeeDistributionConfigurationVerificationCodeV2,
) -> None:
    claim = _claim(
        algorithm_version="OTHER_ALGORITHM" if field == "algorithm" else SRGD_ALGORITHM_VERSION_V1,
        accepted_language_version=(
            "OTHER_LANGUAGE"
            if field == "accepted_language"
            else PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2
        ),
    )
    if field == "policy_root":
        object.__setattr__(claim.body, "policy_root", ZERO_DIGEST)
        object.__setattr__(
            claim,
            "configuration_root",
            canonical_fee_distribution_configuration_root_v2(claim.body),
        )
    elif field == "configuration_root":
        object.__setattr__(claim, "configuration_root", ZERO_DIGEST)

    result = validate_fee_distribution_configuration_claim_v2(claim)

    assert _reject(result).code is expected_code


def test_hostile_nested_mutation_is_caught_by_revalidation() -> None:
    validated = validate_fee_distribution_configuration_claim_v2(_claim())
    assert type(validated) is ValidatedFeeDistributionConfigurationClaimV2
    object.__setattr__(validated.body.policy, "buyback_bps", 3_334)

    assert not revalidate_fee_distribution_configuration_claim_v2(validated)


def test_wrong_top_level_type_and_invalid_claim_fail_closed() -> None:
    assert _reject(validate_fee_distribution_configuration_claim_v2(object())).code is (
        FeeDistributionConfigurationVerificationCodeV2.WRONG_EXACT_TYPE
    )
    claim = _claim()
    object.__setattr__(claim.body, "configuration_version", True)

    assert _reject(validate_fee_distribution_configuration_claim_v2(claim)).code is (
        FeeDistributionConfigurationVerificationCodeV2.INVALID_CLAIM
    )
