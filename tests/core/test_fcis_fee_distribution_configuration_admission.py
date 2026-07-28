from __future__ import annotations

from src.core.fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    FeeDistributionPolicySourceV2,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_distribution_configuration_admission import admit
from src.core.fcis_fee_distribution_configuration_codec import (
    canonical_fee_distribution_configuration_root_v2,
    canonical_fee_distribution_policy_root_v2,
)
from src.core.fcis_fee_distribution_configuration_values import (
    FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
    PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    FeeDistributionConfigurationBodySourceV2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimSourceV2,
    FeeDistributionConfigurationClaimV2,
)
from src.state.snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)


def _limits() -> ValidatedAdmissionLimitsV1:
    result = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=64,
            max_nodes=20_000,
            max_canonical_bytes=1_000_000,
            max_collection_items=20_000,
        )
    )
    if type(result) is not ValidatedAdmissionLimitsV1:
        raise AssertionError("test limits must be valid")
    return result


def _source(*, configuration_version: object = 7) -> FeeDistributionConfigurationClaimSourceV2:
    policy = FeeDistributionPolicyV2(
        3_333,
        3_333,
        3_334,
        "buyback",
        "treasury",
        "rewards",
    )
    body = FeeDistributionConfigurationBodyV2(
        "zenodex:testnet",
        7,
        "protocol-fees",
        canonical_fee_distribution_policy_root_v2(policy),
        policy,
        MAX_FEE_AMOUNT_V2,
        SRGD_ALGORITHM_VERSION_V1,
        PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    )
    return FeeDistributionConfigurationClaimSourceV2(
        FeeDistributionConfigurationBodySourceV2(
            body.chain_deployment_id,
            configuration_version,
            body.fee_distribution_domain_id,
            body.policy_root,
            FeeDistributionPolicySourceV2(
                policy.buyback_bps,
                policy.treasury_bps,
                policy.rewards_bps,
                policy.buyback_destination,
                policy.treasury_destination,
                policy.rewards_destination,
            ),
            body.activation_sequence,
            body.algorithm_version,
            body.accepted_language_version,
        ),
        canonical_fee_distribution_configuration_root_v2(body),
    )


def test_closed_admission_constructs_non_authoritative_claim() -> None:
    result = admit(
        FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        _limits(),
        _source(),
    )

    assert type(result) is AdmitOk
    assert type(result.value) is FeeDistributionConfigurationClaimV2


def test_boolean_version_and_broad_mapping_reject() -> None:
    boolean = admit(
        FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        _limits(),
        _source(configuration_version=True),
    )
    assert boolean == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("body", "configuration_version"),
    )

    broad = admit(
        FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        _limits(),
        {},
    )
    assert broad == AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())


def test_u256_overflow_rejects_before_semantic_verification() -> None:
    result = admit(
        FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        _limits(),
        _source(configuration_version=MAX_FEE_AMOUNT_V2 + 1),
    )

    assert result == AdmitReject(
        AdmitCode.OUT_OF_RANGE,
        ("body", "configuration_version"),
    )
