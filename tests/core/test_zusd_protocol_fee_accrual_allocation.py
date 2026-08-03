from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.fcis_fee_apportionment_values import (
    SRGD_ALGORITHM_VERSION_V1,
    CommittedFeeApportionmentStateV2,
    FeeDistributionPolicyV2,
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
from src.core.zusd_protocol_fee_accrual_allocation import (
    ZUSDProtocolFeeAccrualAllocationCandidateV1,
    ZUSDProtocolFeeAccrualAllocationRejectCodeV1,
    ZUSDProtocolFeeAccrualAllocationRejectV1,
    ZUSDProtocolFeeAccrualAllocationSourceV1,
    derive_zusd_protocol_fee_accrual_allocation_v1,
    verify_zusd_protocol_fee_accrual_allocation_v1,
)
from src.core.zusd_protocol_fee_claim import (
    ZUSDProtocolFeeClaimV1,
    empty_zusd_protocol_fee_claim_v1,
)
from src.core.zusd_protocol_fee_role_claims import (
    ZUSDProtocolFeeRoleClaimStateV1,
    empty_zusd_protocol_fee_role_claim_state_v1,
)

ASSET = "0x" + "aa" * 32
OTHER_ASSET = "0x" + "dd" * 32
ESCROW = "0x" + "bb" * 48
OTHER_ESCROW = "0x" + "cc" * 48
BUYBACK = "0x" + "11" * 48
TREASURY = "0x" + "22" * 48
REWARDS = "0x" + "33" * 48
ALT_BUYBACK = "0x" + "44" * 48
ALT_TREASURY = "0x" + "55" * 48
ALT_REWARDS = "0x" + "66" * 48
DEPLOYMENT = "zenodex:testnet"
DOMAIN = "protocol-fees:zusd"


def _validated_configuration(
    *,
    weights: tuple[int, int, int] = (2_500, 2_500, 5_000),
    destinations: tuple[str, str, str] = (BUYBACK, TREASURY, REWARDS),
) -> ValidatedFeeDistributionConfigurationClaimV2:
    policy = FeeDistributionPolicyV2(*weights, *destinations)
    body = FeeDistributionConfigurationBodyV2(
        chain_deployment_id=DEPLOYMENT,
        configuration_version=1,
        fee_distribution_domain_id=DOMAIN,
        policy_root=canonical_fee_distribution_policy_root_v2(policy),
        policy=policy,
        activation_sequence=0,
        algorithm_version=SRGD_ALGORITHM_VERSION_V1,
        accepted_language_version=PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    )
    claim = FeeDistributionConfigurationClaimV2(
        body,
        canonical_fee_distribution_configuration_root_v2(body),
    )
    validated = validate_fee_distribution_configuration_claim_v2(claim)
    assert type(validated) is ValidatedFeeDistributionConfigurationClaimV2
    return validated


def _source(
    *,
    amount_e8: object,
    scalar_claim: object | None = None,
    role_claims: object | None = None,
    apportionment_state: object | None = None,
    configuration: object | None = None,
) -> ZUSDProtocolFeeAccrualAllocationSourceV1:
    exact_apportionment_state = (
        CommittedFeeApportionmentStateV2(SRGD_ALGORITHM_VERSION_V1, ())
        if apportionment_state is None
        else apportionment_state
    )
    return ZUSDProtocolFeeAccrualAllocationSourceV1(
        pre_scalar_claim=(
            empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
            if scalar_claim is None
            else scalar_claim
        ),
        pre_role_claims=(
            empty_zusd_protocol_fee_role_claim_state_v1(
                fee_distribution_domain_id=DOMAIN,
                asset_id=ASSET,
                scalar_claim_custody_pubkey=ESCROW,
                apportionment_state=exact_apportionment_state,
            )
            if role_claims is None
            else role_claims
        ),
        pre_apportionment_state=exact_apportionment_state,
        validated_configuration=(
            _validated_configuration() if configuration is None else configuration
        ),
        amount_e8=amount_e8,
    )


def test_accrual_allocation_binds_one_scalar_occurrence_to_one_srgd_transition() -> None:
    source = _source(amount_e8=3)

    result = derive_zusd_protocol_fee_accrual_allocation_v1(source)

    assert type(result) is ZUSDProtocolFeeAccrualAllocationCandidateV1
    assert result.scalar_claim_transition.kind == "accrue"
    assert result.scalar_claim_transition.amount_e8 == 3
    assert result.occurrence_root == result.scalar_claim_transition.transition_root
    assert result.fee_contribution.amount == 3
    assert result.fee_contribution.key.fee_distribution_domain_id == DOMAIN
    assert result.allocation.amounts == (1, 1, 1)
    assert result.post_role_claims.outstanding_e8 == (1, 1, 1)
    assert result.post_role_claims.accrued_cumulative_e8 == (1, 1, 1)
    assert result.post_role_claims.outstanding_total_e8 == 3
    assert result.post_role_claims.accrued_cumulative_total_e8 == 3
    assert result.scalar_claim_transition.post_state.outstanding_e8 == 3

    verified = verify_zusd_protocol_fee_accrual_allocation_v1(
        source=source,
        candidate=result,
    )
    assert verified is result


def test_accrual_allocation_preserves_split_occurrence_boundaries_and_lineage() -> None:
    one_event = derive_zusd_protocol_fee_accrual_allocation_v1(_source(amount_e8=3))
    assert type(one_event) is ZUSDProtocolFeeAccrualAllocationCandidateV1

    first = derive_zusd_protocol_fee_accrual_allocation_v1(_source(amount_e8=1))
    assert type(first) is ZUSDProtocolFeeAccrualAllocationCandidateV1
    second = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(
            amount_e8=2,
            scalar_claim=first.scalar_claim_transition.post_state,
            role_claims=first.post_role_claims,
            apportionment_state=first.apportionment_transition.state,
        )
    )
    assert type(second) is ZUSDProtocolFeeAccrualAllocationCandidateV1

    assert one_event.post_role_claims.outstanding_e8 == (1, 1, 1)
    assert second.post_role_claims.outstanding_e8 == (1, 0, 2)
    assert one_event.post_role_claims.outstanding_total_e8 == 3
    assert second.post_role_claims.outstanding_total_e8 == 3
    assert first.occurrence_root != second.occurrence_root
    assert one_event.occurrence_root != second.occurrence_root


def test_accrual_allocation_rejects_zero_bool_and_overflow_occurrences() -> None:
    maximum = (1 << 256) - 1
    full_buyback = _validated_configuration(weights=(10_000, 0, 0))
    maximum_result = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(amount_e8=maximum, configuration=full_buyback)
    )
    assert type(maximum_result) is ZUSDProtocolFeeAccrualAllocationCandidateV1

    cases = (
        (False, None, None, ZUSDProtocolFeeAccrualAllocationRejectCodeV1.WRONG_EXACT_TYPE),
        (0, None, None, ZUSDProtocolFeeAccrualAllocationRejectCodeV1.ZERO_AMOUNT),
        (
            1,
            maximum_result.scalar_claim_transition.post_state,
            maximum_result.post_role_claims,
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.SCALAR_CLAIM_TRANSITION,
        ),
    )
    for amount_e8, scalar_claim, role_claims, expected_code in cases:
        result = derive_zusd_protocol_fee_accrual_allocation_v1(
            _source(
                amount_e8=amount_e8,
                scalar_claim=scalar_claim,
                role_claims=role_claims,
                apportionment_state=(
                    maximum_result.apportionment_transition.state
                    if scalar_claim is not None
                    else None
                ),
                configuration=(full_buyback if scalar_claim is not None else None),
            )
        )
        assert type(result) is ZUSDProtocolFeeAccrualAllocationRejectV1
        assert result.code is expected_code
        assert not hasattr(result, "post_role_claims")
        assert not hasattr(result, "apportionment_transition")


def test_accrual_allocation_rejects_unvalidated_or_hostile_configuration() -> None:
    validated = _validated_configuration()
    raw = FeeDistributionConfigurationClaimV2(
        validated.body,
        validated.configuration_root,
    )
    hostile = _validated_configuration()
    object.__setattr__(hostile.body, "fee_distribution_domain_id", "mallory")

    for configuration in (raw, hostile):
        result = derive_zusd_protocol_fee_accrual_allocation_v1(
            _source(amount_e8=1, configuration=configuration)
        )
        assert result == ZUSDProtocolFeeAccrualAllocationRejectV1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_CONFIGURATION,
            ("validated_configuration",),
        )


def test_accrual_allocation_rejects_crossed_role_identity_and_scalar_partition() -> None:
    crossed_identity = empty_zusd_protocol_fee_role_claim_state_v1(
        fee_distribution_domain_id=DOMAIN,
        asset_id=OTHER_ASSET,
        scalar_claim_custody_pubkey=ESCROW,
        apportionment_state=CommittedFeeApportionmentStateV2(
            SRGD_ALGORITHM_VERSION_V1,
            (),
        ),
    )
    nonempty_scalar = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    object.__setattr__(nonempty_scalar, "outstanding_e8", 1)
    object.__setattr__(nonempty_scalar, "accrued_cumulative_e8", 1)

    identity_result = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(amount_e8=1, role_claims=crossed_identity)
    )
    partition_result = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(amount_e8=1, scalar_claim=nonempty_scalar)
    )

    assert identity_result == ZUSDProtocolFeeAccrualAllocationRejectV1(
        ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
        ("role_claim_identity",),
    )
    assert partition_result == ZUSDProtocolFeeAccrualAllocationRejectV1(
        ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_PRESTATE_PARTITION,
        ("claim_partition",),
    )


def test_accrual_allocation_rejects_crossed_scalar_custody_identity() -> None:
    crossed_scalar = empty_zusd_protocol_fee_claim_v1(
        asset_id=ASSET,
        custody_pubkey=OTHER_ESCROW,
    )

    result = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(amount_e8=1, scalar_claim=crossed_scalar)
    )

    assert result == ZUSDProtocolFeeAccrualAllocationRejectV1(
        ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
        ("role_claim_custody",),
    )


def test_accrual_allocation_rejects_apportionment_history_reset() -> None:
    first = derive_zusd_protocol_fee_accrual_allocation_v1(_source(amount_e8=1))
    assert type(first) is ZUSDProtocolFeeAccrualAllocationCandidateV1
    reset_state = CommittedFeeApportionmentStateV2(SRGD_ALGORITHM_VERSION_V1, ())

    result = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(
            amount_e8=1,
            scalar_claim=first.scalar_claim_transition.post_state,
            role_claims=first.post_role_claims,
            apportionment_state=reset_state,
        )
    )

    assert result == ZUSDProtocolFeeAccrualAllocationRejectV1(
        ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
        ("apportionment_state_lineage",),
    )


def test_accrual_allocation_verifier_rejects_crossed_instance_and_mutation() -> None:
    source = _source(amount_e8=3)
    result = derive_zusd_protocol_fee_accrual_allocation_v1(source)
    assert type(result) is ZUSDProtocolFeeAccrualAllocationCandidateV1

    crossed = verify_zusd_protocol_fee_accrual_allocation_v1(
        source=_source(amount_e8=2),
        candidate=result,
    )
    assert crossed == ZUSDProtocolFeeAccrualAllocationRejectV1(
        ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
        ("instance",),
    )

    with pytest.raises(TypeError, match="controlled derivation"):
        replace(result, post_role_claims=result.pre_role_claims)

    object.__setattr__(result.post_role_claims, "outstanding_entries", ())
    hostile = verify_zusd_protocol_fee_accrual_allocation_v1(
        source=source,
        candidate=result,
    )
    assert hostile == ZUSDProtocolFeeAccrualAllocationRejectV1(
        ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_CANDIDATE,
        ("candidate",),
    )


def test_accrual_allocation_carries_no_balance_or_publication_authority() -> None:
    result = derive_zusd_protocol_fee_accrual_allocation_v1(_source(amount_e8=3))

    assert type(result) is ZUSDProtocolFeeAccrualAllocationCandidateV1
    assert not hasattr(result, "balances")
    assert not hasattr(result, "balance_patch")
    assert not hasattr(result, "authority_header")
    assert not hasattr(result, "pre_state_root")
    assert not hasattr(result, "receipt")
    assert not hasattr(result, "outbox")
    assert not hasattr(result, "publication_authority")


def test_role_claim_state_requires_controlled_derivation() -> None:
    with pytest.raises(TypeError, match="controlled derivation"):
        ZUSDProtocolFeeRoleClaimStateV1(
            fee_distribution_domain_id=DOMAIN,
            asset_id=ASSET,
            scalar_claim_custody_pubkey=ESCROW,
            apportionment_state_digest="0x" + "00" * 32,
            outstanding_entries=(),
            accrued_buyback_cumulative_e8=0,
            accrued_treasury_cumulative_e8=0,
            accrued_rewards_cumulative_e8=0,
        )


def test_accrual_allocation_bounded_sequences_preserve_role_partition() -> None:
    for weights in ((0, 0, 10_000), (2_500, 2_500, 5_000), (3_333, 3_333, 3_334)):
        scalar: ZUSDProtocolFeeClaimV1 = empty_zusd_protocol_fee_claim_v1(
            asset_id=ASSET,
            custody_pubkey=ESCROW,
        )
        roles: ZUSDProtocolFeeRoleClaimStateV1 = empty_zusd_protocol_fee_role_claim_state_v1(
            fee_distribution_domain_id=DOMAIN,
            asset_id=ASSET,
            scalar_claim_custody_pubkey=ESCROW,
            apportionment_state=CommittedFeeApportionmentStateV2(
                SRGD_ALGORITHM_VERSION_V1,
                (),
            ),
        )
        apportionment = CommittedFeeApportionmentStateV2(SRGD_ALGORITHM_VERSION_V1, ())
        configuration = _validated_configuration(weights=weights)
        total = 0
        for amount_e8 in (1, 2, 3, 4):
            result = derive_zusd_protocol_fee_accrual_allocation_v1(
                _source(
                    amount_e8=amount_e8,
                    scalar_claim=scalar,
                    role_claims=roles,
                    apportionment_state=apportionment,
                    configuration=configuration,
                )
            )
            assert type(result) is ZUSDProtocolFeeAccrualAllocationCandidateV1
            total += amount_e8
            assert sum(result.allocation.amounts) == amount_e8
            assert result.post_role_claims.outstanding_total_e8 == total
            assert (
                result.scalar_claim_transition.post_state.outstanding_e8
                == result.post_role_claims.outstanding_total_e8
            )
            assert (
                result.scalar_claim_transition.post_state.accrued_cumulative_e8
                == result.post_role_claims.accrued_cumulative_total_e8
            )
            scalar = result.scalar_claim_transition.post_state
            roles = result.post_role_claims
            apportionment = result.apportionment_transition.state


def test_accrual_allocation_retains_destination_identity_across_policy_rotation() -> None:
    first_configuration = _validated_configuration()
    first = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(amount_e8=3, configuration=first_configuration)
    )
    assert type(first) is ZUSDProtocolFeeAccrualAllocationCandidateV1

    second_configuration = _validated_configuration(
        destinations=(ALT_BUYBACK, ALT_TREASURY, ALT_REWARDS)
    )
    second = derive_zusd_protocol_fee_accrual_allocation_v1(
        _source(
            amount_e8=3,
            scalar_claim=first.scalar_claim_transition.post_state,
            role_claims=first.post_role_claims,
            apportionment_state=first.apportionment_transition.state,
            configuration=second_configuration,
        )
    )
    assert type(second) is ZUSDProtocolFeeAccrualAllocationCandidateV1

    roots_and_destinations = {
        (entry.configuration_root, entry.destination)
        for entry in second.post_role_claims.outstanding_entries
    }
    assert (first_configuration.configuration_root, BUYBACK) in roots_and_destinations
    assert (first_configuration.configuration_root, TREASURY) in roots_and_destinations
    assert (first_configuration.configuration_root, REWARDS) in roots_and_destinations
    for destination, amount in zip(
        (ALT_BUYBACK, ALT_TREASURY, ALT_REWARDS),
        second.allocation.amounts,
        strict=True,
    ):
        assert (
            (second_configuration.configuration_root, destination) in roots_and_destinations
        ) is (amount > 0)
