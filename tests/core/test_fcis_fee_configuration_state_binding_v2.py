from __future__ import annotations

import pytest

from src.core.fcis_b1b_authority_values import FCISAuthorityHeaderV2
from src.core.fcis_fee_apportionment_values import (
    SRGD_ALGORITHM_VERSION_V1,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_configuration_state_binding_v2 import (
    ExactFeeAuthorityStateProjectionV2,
    FeeConfigurationStateBindingRejectCodeV2,
    FeeConfigurationStateBindingRejectV2,
    StateBoundActiveFeeConfigurationV2,
    bind_fee_configuration_to_state_projection_v2,
    revalidate_state_bound_active_fee_configuration_v2,
)
from src.core.fcis_fee_distribution_configuration_codec import (
    canonical_fee_distribution_configuration_root_v2,
    canonical_fee_distribution_policy_root_v2,
)
from src.core.fcis_fee_distribution_configuration_values import (
    PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
    ValidatedFeeDistributionConfigurationClaimV2,
)
from src.core.fcis_fee_distribution_configuration_verification import (
    validate_fee_distribution_configuration_claim_v2,
)

DEPLOYMENT = "zenodex:testnet"
GLOBAL_STATE_ROOT = "0x" + ("a1" * 32)
ZUSD_STATE_ROOT = "0x" + ("b2" * 32)
SCALAR_CLAIM_ROOT = "0x" + ("c3" * 32)
ROLE_CLAIM_ROOT = "0x" + ("d4" * 32)
APPORTIONMENT_STATE_ROOT = "0x" + ("e5" * 32)
DEPLOYMENT_CONFIG_ROOT = "f6" * 32
ZUSD_ASSET_ID = "0x" + ("07" * 32)
CLAIM_CUSTODY = "0x" + ("08" * 48)
BUYBACK = "0x" + ("11" * 48)
TREASURY = "0x" + ("22" * 48)
REWARDS = "0x" + ("33" * 48)


def _validated_configuration(
    *,
    deployment: str = DEPLOYMENT,
    activation_sequence: int = 4,
    weights: tuple[int, int, int] = (2_500, 2_500, 5_000),
) -> ValidatedFeeDistributionConfigurationClaimV2:
    policy = FeeDistributionPolicyV2(
        *weights,
        BUYBACK,
        TREASURY,
        REWARDS,
    )
    body = FeeDistributionConfigurationBodyV2(
        chain_deployment_id=deployment,
        configuration_version=1,
        fee_distribution_domain_id="protocol-fees:zusd",
        policy_root=canonical_fee_distribution_policy_root_v2(policy),
        policy=policy,
        activation_sequence=activation_sequence,
        algorithm_version=SRGD_ALGORITHM_VERSION_V1,
        accepted_language_version=PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    )
    result = validate_fee_distribution_configuration_claim_v2(
        FeeDistributionConfigurationClaimV2(
            body,
            canonical_fee_distribution_configuration_root_v2(body),
        )
    )
    assert type(result) is ValidatedFeeDistributionConfigurationClaimV2
    return result


def _projection(
    configuration: ValidatedFeeDistributionConfigurationClaimV2,
    *,
    deployment: str = DEPLOYMENT,
    sequence: int = 7,
) -> ExactFeeAuthorityStateProjectionV2:
    return ExactFeeAuthorityStateProjectionV2(
        global_state_root=GLOBAL_STATE_ROOT,
        zusd_state_root=ZUSD_STATE_ROOT,
        protocol_fee_claim_state_root=SCALAR_CLAIM_ROOT,
        protocol_fee_role_claim_state_root=ROLE_CLAIM_ROOT,
        fee_apportionment_state_root=APPORTIONMENT_STATE_ROOT,
        deployment_config_root=DEPLOYMENT_CONFIG_ROOT,
        authority_epoch_index=2,
        zusd_asset_id=ZUSD_ASSET_ID,
        protocol_fee_claim_custody_pubkey=CLAIM_CUSTODY,
        authority_header=FCISAuthorityHeaderV2(
            chain_deployment_id=deployment,
            sequence=sequence,
            fee_distribution_configuration_root=configuration.configuration_root,
        ),
    )


def _assert_reject(
    value: object,
    code: FeeConfigurationStateBindingRejectCodeV2,
) -> FeeConfigurationStateBindingRejectV2:
    assert type(value) is FeeConfigurationStateBindingRejectV2
    assert value.code is code
    return value


def test_binding_derives_one_controlled_value_from_exact_sources() -> None:
    configuration = _validated_configuration()
    projection = _projection(configuration)

    result = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=projection,
        validated_configuration=configuration,
    )

    assert type(result) is StateBoundActiveFeeConfigurationV2
    assert result.exact_state_projection is projection
    assert result.validated_configuration is configuration
    assert result.configuration_root == configuration.configuration_root
    assert result.chain_deployment_id == DEPLOYMENT
    assert result.activation_sequence == 4
    assert result.state_projection_root == projection.state_projection_root
    assert result.exact_state_projection.zusd_state_root == ZUSD_STATE_ROOT
    assert result.exact_state_projection.zusd_asset_id == ZUSD_ASSET_ID
    assert revalidate_state_bound_active_fee_configuration_v2(result)


def test_valid_but_unauthorized_configuration_is_rejected() -> None:
    committed = _validated_configuration(weights=(2_500, 2_500, 5_000))
    unauthorized = _validated_configuration(weights=(5_000, 2_500, 2_500))
    projection = _projection(committed)

    result = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=projection,
        validated_configuration=unauthorized,
    )

    _assert_reject(
        result,
        FeeConfigurationStateBindingRejectCodeV2.CONFIGURATION_ROOT_MISMATCH,
    )


def test_binding_rejects_deployment_and_future_activation_crosses() -> None:
    configuration = _validated_configuration()
    wrong_deployment = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=_projection(configuration, deployment="zenodex:other"),
        validated_configuration=configuration,
    )
    future = _validated_configuration(activation_sequence=8)
    future_activation = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=_projection(future, sequence=7),
        validated_configuration=future,
    )

    _assert_reject(
        wrong_deployment,
        FeeConfigurationStateBindingRejectCodeV2.DEPLOYMENT_MISMATCH,
    )
    _assert_reject(
        future_activation,
        FeeConfigurationStateBindingRejectCodeV2.ACTIVATION_SEQUENCE_IN_FUTURE,
    )


def test_binding_revalidates_hostile_mutation_at_point_of_use() -> None:
    configuration = _validated_configuration()
    projection = _projection(configuration)
    object.__setattr__(projection.authority_header, "sequence", True)

    result = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=projection,
        validated_configuration=configuration,
    )

    _assert_reject(
        result,
        FeeConfigurationStateBindingRejectCodeV2.INVALID_STATE_PROJECTION,
    )


def test_controlled_binding_cannot_be_publicly_constructed_or_reused_after_mutation() -> None:
    configuration = _validated_configuration()
    projection = _projection(configuration)
    with pytest.raises(TypeError, match="requires state binding"):
        StateBoundActiveFeeConfigurationV2(
            exact_state_projection=projection,
            validated_configuration=configuration,
            binding_root="0x" + ("00" * 32),
        )

    result = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=projection,
        validated_configuration=configuration,
    )
    assert type(result) is StateBoundActiveFeeConfigurationV2
    object.__setattr__(configuration, "configuration_root", "0x" + ("00" * 32))
    assert not revalidate_state_bound_active_fee_configuration_v2(result)
