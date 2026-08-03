from __future__ import annotations

import pytest

from src.core.fcis_b1b_authority_values import FCISAuthorityHeaderV2
from src.core.fcis_fee_apportionment_codec import canonical_sha256_fcis_fee_apportionment_v2
from src.core.fcis_fee_apportionment_values import (
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    SRGD_ALGORITHM_VERSION_V1,
    CommittedFeeApportionmentStateV2,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_configuration_state_binding_v2 import (
    ExactFeeAuthorityStateProjectionV2,
    StateBoundActiveFeeConfigurationV2,
    bind_fee_configuration_to_state_projection_v2,
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
from src.core.fcis_m6_e01_request_identity import (
    E01CommandFamilyV1,
    E01RequestIdentityV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.zusd import E8, ZUSDState
from src.core.zusd_authenticated_borrow_fee_occurrence_v1 import (
    ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    canonical_zusd_borrow_command_root_v1,
    canonical_zusd_state_root_v1,
    derive_zusd_authenticated_borrow_fee_occurrence_v1,
)
from src.core.zusd_protocol_fee_claim import (
    ZUSDProtocolFeeClaimV1,
    empty_zusd_protocol_fee_claim_v1,
)
from src.core.zusd_protocol_fee_role_claims import (
    ZUSDProtocolFeeRoleClaimStateV1,
    empty_zusd_protocol_fee_role_claim_state_v1,
)
from src.core.zusd_state_bound_fee_accrual_allocation_v2 import (
    ZUSDStateBoundFeeAccrualAllocationRejectCodeV2,
    ZUSDStateBoundFeeAccrualAllocationRejectV2,
    ZUSDStateBoundFeeAccrualAllocationSourceV2,
    ZUSDStateBoundFeeAccrualAllocationV2,
    derive_zusd_state_bound_fee_accrual_allocation_v2,
    revalidate_zusd_state_bound_fee_accrual_allocation_v2,
    verify_zusd_state_bound_fee_accrual_allocation_v2,
)

DEPLOYMENT = "zenodex:testnet"
DEPLOYMENT_CONFIG_ROOT = "1" * 64
AUTHENTICATION_PROFILE_ROOT = "2" * 64
AUTHENTICATION_EVIDENCE_ROOT = "3" * 64
GLOBAL_STATE_ROOT = "0x" + ("a1" * 32)
ASSET = "0x" + ("aa" * 32)
FOREIGN_ASSET = "0x" + ("dd" * 32)
ESCROW = "0x" + ("bb" * 48)
FOREIGN_ESCROW = "0x" + ("cc" * 48)
BUYBACK = "0x" + ("11" * 48)
TREASURY = "0x" + ("22" * 48)
REWARDS = "0x" + ("33" * 48)
DOMAIN = "protocol-fees:zusd"


def _pre_state(*, cumulative_fee_e8: int = 0) -> ZUSDState:
    return ZUSDState(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=3 * E8,
        borrow_fee_floor_bps=100,
        borrow_fee_max_bps=100,
        protocol_revenue_zusd_cum_e8=cumulative_fee_e8,
    )


def _validated_configuration(
    *,
    domain: str = DOMAIN,
) -> ValidatedFeeDistributionConfigurationClaimV2:
    policy = FeeDistributionPolicyV2(
        2_500,
        2_500,
        5_000,
        BUYBACK,
        TREASURY,
        REWARDS,
    )
    body = FeeDistributionConfigurationBodyV2(
        chain_deployment_id=DEPLOYMENT,
        configuration_version=1,
        fee_distribution_domain_id=domain,
        policy_root=canonical_fee_distribution_policy_root_v2(policy),
        policy=policy,
        activation_sequence=4,
        algorithm_version=SRGD_ALGORITHM_VERSION_V1,
        accepted_language_version=PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    )
    validated = validate_fee_distribution_configuration_claim_v2(
        FeeDistributionConfigurationClaimV2(
            body,
            canonical_fee_distribution_configuration_root_v2(body),
        )
    )
    assert type(validated) is ValidatedFeeDistributionConfigurationClaimV2
    return validated


def _occurrence(
    *,
    pre_state: ZUSDState,
    principal_e8: int = 100 * E8,
    expected_sequence: int = 7,
    deployment_config_root: str = DEPLOYMENT_CONFIG_ROOT,
    authority_epoch_index: int = 2,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceV1:
    command_root = canonical_zusd_borrow_command_root_v1(
        borrower_id="alice",
        principal_e8=principal_e8,
        pre_state=pre_state,
    )
    authenticated = _mint_authenticated_command_v1(
        command_root=command_root,
        sender_id="alice",
        command_family=E01CommandFamilyV1.STATE_CHANGE,
        nonce=9,
        authentication_profile_root=AUTHENTICATION_PROFILE_ROOT,
        authentication_evidence_root=AUTHENTICATION_EVIDENCE_ROOT,
    )
    identity: E01RequestIdentityV1 = derive_request_identity_v1(
        authenticated_command=authenticated,
        deployment_config_root=deployment_config_root,
        expected_sequence=expected_sequence,
        authority_epoch_index=authority_epoch_index,
    )
    result = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1(
            request_identity=identity,
            pre_state=pre_state,
            principal_e8=principal_e8,
        )
    )
    assert type(result) is ZUSDAuthenticatedBorrowFeeOccurrenceV1
    return result


def _claims(
    *,
    asset_id: str = ASSET,
    custody_pubkey: str = ESCROW,
) -> tuple[
    ZUSDProtocolFeeClaimV1,
    ZUSDProtocolFeeRoleClaimStateV1,
    CommittedFeeApportionmentStateV2,
]:
    apportionment = CommittedFeeApportionmentStateV2(
        SRGD_ALGORITHM_VERSION_V1,
        (),
    )
    scalar = empty_zusd_protocol_fee_claim_v1(
        asset_id=asset_id,
        custody_pubkey=custody_pubkey,
    )
    roles = empty_zusd_protocol_fee_role_claim_state_v1(
        fee_distribution_domain_id=DOMAIN,
        asset_id=asset_id,
        scalar_claim_custody_pubkey=custody_pubkey,
        apportionment_state=apportionment,
    )
    return scalar, roles, apportionment


def _apportionment_root(state: CommittedFeeApportionmentStateV2) -> str:
    return canonical_sha256_fcis_fee_apportionment_v2(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        state,
    )


def _source(
    *,
    pre_state: ZUSDState | None = None,
    principal_e8: int = 100 * E8,
    expected_sequence: int = 7,
    projection_sequence: int = 7,
    identity_deployment_root: str = DEPLOYMENT_CONFIG_ROOT,
    projection_deployment_root: str = DEPLOYMENT_CONFIG_ROOT,
    identity_epoch: int = 2,
    projection_epoch: int = 2,
    projection_zusd_state_root: str | None = None,
    projection_scalar_root: str | None = None,
    asset_id: str = ASSET,
    projection_asset_id: str = ASSET,
    custody_pubkey: str = ESCROW,
    projection_custody_pubkey: str = ESCROW,
    configuration_domain: str = DOMAIN,
) -> ZUSDStateBoundFeeAccrualAllocationSourceV2:
    exact_pre_state = _pre_state() if pre_state is None else pre_state
    occurrence = _occurrence(
        pre_state=exact_pre_state,
        principal_e8=principal_e8,
        expected_sequence=expected_sequence,
        deployment_config_root=identity_deployment_root,
        authority_epoch_index=identity_epoch,
    )
    scalar, roles, apportionment = _claims(
        asset_id=asset_id,
        custody_pubkey=custody_pubkey,
    )
    configuration = _validated_configuration(domain=configuration_domain)
    projection = ExactFeeAuthorityStateProjectionV2(
        global_state_root=GLOBAL_STATE_ROOT,
        zusd_state_root=(
            canonical_zusd_state_root_v1(exact_pre_state)
            if projection_zusd_state_root is None
            else projection_zusd_state_root
        ),
        protocol_fee_claim_state_root=(
            scalar.state_root if projection_scalar_root is None else projection_scalar_root
        ),
        protocol_fee_role_claim_state_root=roles.state_root,
        fee_apportionment_state_root=_apportionment_root(apportionment),
        deployment_config_root=projection_deployment_root,
        authority_epoch_index=projection_epoch,
        zusd_asset_id=projection_asset_id,
        protocol_fee_claim_custody_pubkey=projection_custody_pubkey,
        authority_header=FCISAuthorityHeaderV2(
            chain_deployment_id=DEPLOYMENT,
            sequence=projection_sequence,
            fee_distribution_configuration_root=configuration.configuration_root,
        ),
    )
    bound = bind_fee_configuration_to_state_projection_v2(
        exact_state_projection=projection,
        validated_configuration=configuration,
    )
    assert type(bound) is StateBoundActiveFeeConfigurationV2
    return ZUSDStateBoundFeeAccrualAllocationSourceV2(
        state_bound_configuration=bound,
        authenticated_occurrence=occurrence,
        pre_scalar_claim=scalar,
        pre_role_claims=roles,
        pre_apportionment_state=apportionment,
    )


def _assert_reject(
    value: object,
    code: ZUSDStateBoundFeeAccrualAllocationRejectCodeV2,
) -> ZUSDStateBoundFeeAccrualAllocationRejectV2:
    assert type(value) is ZUSDStateBoundFeeAccrualAllocationRejectV2
    assert value.code is code
    return value


def test_composition_derives_fee_and_configuration_from_controlled_sources() -> None:
    source = _source()

    result = derive_zusd_state_bound_fee_accrual_allocation_v2(source)

    assert type(result) is ZUSDStateBoundFeeAccrualAllocationV2
    assert result.authenticated_occurrence.fee_e8 == E8
    assert result.accrual_allocation.scalar_claim_transition.amount_e8 == E8
    assert result.accrual_allocation.allocation.amounts == (
        E8 // 4,
        E8 // 4,
        E8 // 2,
    )
    assert (
        result.accrual_allocation.validated_configuration
        is result.state_bound_configuration.validated_configuration
    )
    assert result.authenticated_occurrence_root != result.scalar_occurrence_root
    assert revalidate_zusd_state_bound_fee_accrual_allocation_v2(result)
    assert (
        verify_zusd_state_bound_fee_accrual_allocation_v2(
            source=source,
            candidate=result,
        )
        is result
    )


@pytest.mark.parametrize(
    ("source", "code"),
    (
        (
            _source(expected_sequence=8),
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.REQUEST_SEQUENCE_MISMATCH,
        ),
        (
            _source(identity_deployment_root="4" * 64),
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.DEPLOYMENT_CONFIG_ROOT_MISMATCH,
        ),
        (
            _source(identity_epoch=3),
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.AUTHORITY_EPOCH_MISMATCH,
        ),
    ),
)
def test_composition_rejects_crossed_request_context(
    source: ZUSDStateBoundFeeAccrualAllocationSourceV2,
    code: ZUSDStateBoundFeeAccrualAllocationRejectCodeV2,
) -> None:
    _assert_reject(derive_zusd_state_bound_fee_accrual_allocation_v2(source), code)


def test_composition_rejects_crossed_zusd_and_component_roots() -> None:
    wrong_zusd = derive_zusd_state_bound_fee_accrual_allocation_v2(
        _source(projection_zusd_state_root="0x" + ("01" * 32))
    )
    wrong_claim = derive_zusd_state_bound_fee_accrual_allocation_v2(
        _source(projection_scalar_root="0x" + ("02" * 32))
    )

    _assert_reject(
        wrong_zusd,
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.ZUSD_STATE_ROOT_MISMATCH,
    )
    _assert_reject(
        wrong_claim,
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.STATE_COMPONENT_ROOT_MISMATCH,
    )


def test_composition_rejects_foreign_asset_and_claim_custody() -> None:
    foreign_asset = derive_zusd_state_bound_fee_accrual_allocation_v2(
        _source(asset_id=FOREIGN_ASSET)
    )
    foreign_custody = derive_zusd_state_bound_fee_accrual_allocation_v2(
        _source(custody_pubkey=FOREIGN_ESCROW)
    )

    _assert_reject(
        foreign_asset,
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.MANAGED_ASSET_MISMATCH,
    )
    _assert_reject(
        foreign_custody,
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.CLAIM_CUSTODY_MISMATCH,
    )


def test_composition_rejects_foreign_domain_and_crossed_cumulative_history() -> None:
    foreign_domain = derive_zusd_state_bound_fee_accrual_allocation_v2(
        _source(configuration_domain="protocol-fees:other")
    )
    crossed_history = derive_zusd_state_bound_fee_accrual_allocation_v2(
        _source(pre_state=_pre_state(cumulative_fee_e8=E8))
    )

    _assert_reject(
        foreign_domain,
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.FEE_DISTRIBUTION_DOMAIN_MISMATCH,
    )
    _assert_reject(
        crossed_history,
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.CUMULATIVE_FEE_HISTORY_MISMATCH,
    )


def test_composition_is_controlled_and_rejects_post_derivation_mutation() -> None:
    source = _source()
    with pytest.raises(TypeError, match="requires controlled composition"):
        ZUSDStateBoundFeeAccrualAllocationV2(
            state_bound_configuration=source.state_bound_configuration,  # type: ignore[arg-type]
            authenticated_occurrence=source.authenticated_occurrence,  # type: ignore[arg-type]
            accrual_allocation=None,  # type: ignore[arg-type]
            composition_root="0x" + ("00" * 32),
        )

    result = derive_zusd_state_bound_fee_accrual_allocation_v2(source)
    assert type(result) is ZUSDStateBoundFeeAccrualAllocationV2
    object.__setattr__(result, "composition_root", "0x" + ("00" * 32))
    assert not revalidate_zusd_state_bound_fee_accrual_allocation_v2(result)
    _assert_reject(
        verify_zusd_state_bound_fee_accrual_allocation_v2(
            source=source,
            candidate=result,
        ),
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.INVALID_CANDIDATE,
    )


def test_verifier_rejects_a_different_authenticated_fee_occurrence() -> None:
    source = _source()
    result = derive_zusd_state_bound_fee_accrual_allocation_v2(source)
    assert type(result) is ZUSDStateBoundFeeAccrualAllocationV2
    crossed = _source(principal_e8=200 * E8)

    _assert_reject(
        verify_zusd_state_bound_fee_accrual_allocation_v2(
            source=crossed,
            candidate=result,
        ),
        ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.CANDIDATE_MISMATCH,
    )
