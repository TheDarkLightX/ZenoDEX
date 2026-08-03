from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.fcis_m6_e01_request_identity import (
    E01CommandFamilyV1,
    E01RequestIdentityV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.zusd import E8, ZUSDState
from src.core.zusd_authenticated_borrow_fee_occurrence_v1 import (
    ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    canonical_zusd_borrow_command_root_v1,
    derive_zusd_authenticated_borrow_fee_occurrence_v1,
    revalidate_zusd_authenticated_borrow_fee_occurrence_v1,
    verify_zusd_authenticated_borrow_fee_occurrence_v1,
)

DEPLOYMENT_CONFIG_ROOT = "1" * 64
AUTHENTICATION_PROFILE_ROOT = "2" * 64
AUTHENTICATION_EVIDENCE_ROOT = "3" * 64
SENDER = "alice"


def _pre_state(*, fee_bps: int = 100) -> ZUSDState:
    return ZUSDState(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=2 * E8,
        borrow_fee_floor_bps=fee_bps,
        borrow_fee_max_bps=fee_bps,
    )


def _identity(
    *,
    pre_state: ZUSDState,
    principal_e8: int,
    command_family: E01CommandFamilyV1 = E01CommandFamilyV1.STATE_CHANGE,
    command_root: str | None = None,
) -> E01RequestIdentityV1:
    derived_root = canonical_zusd_borrow_command_root_v1(
        borrower_id=SENDER,
        principal_e8=principal_e8,
        pre_state=pre_state,
    )
    authenticated = _mint_authenticated_command_v1(
        command_root=derived_root if command_root is None else command_root,
        sender_id=SENDER,
        command_family=command_family,
        nonce=9,
        authentication_profile_root=AUTHENTICATION_PROFILE_ROOT,
        authentication_evidence_root=AUTHENTICATION_EVIDENCE_ROOT,
    )
    return derive_request_identity_v1(
        authenticated_command=authenticated,
        deployment_config_root=DEPLOYMENT_CONFIG_ROOT,
        expected_sequence=7,
        authority_epoch_index=2,
    )


def _source(
    *,
    pre_state: ZUSDState | None = None,
    principal_e8: object = 100 * E8,
    identity: object | None = None,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1:
    exact_pre = _pre_state() if pre_state is None else pre_state
    exact_identity = (
        _identity(pre_state=exact_pre, principal_e8=int(principal_e8))
        if identity is None and type(principal_e8) is int
        else identity
    )
    return ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1(
        request_identity=exact_identity,
        pre_state=exact_pre,
        principal_e8=principal_e8,
    )


def _assert_reject(
    value: object,
    code: ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    assert type(value) is ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1
    assert value.code is code
    return value


def test_occurrence_is_reconstructed_from_authenticated_request_and_core_step() -> None:
    source = _source()

    result = derive_zusd_authenticated_borrow_fee_occurrence_v1(source)

    assert type(result) is ZUSDAuthenticatedBorrowFeeOccurrenceV1
    assert result.request_identity is source.request_identity
    assert result.principal_e8 == 100 * E8
    assert result.fee_e8 == 1 * E8
    assert result.fee_bps == 100
    assert result.debt_delta_e8 == 101 * E8
    assert result.post_state.debt_e8 - result.pre_state.debt_e8 == result.debt_delta_e8
    assert (
        result.post_state.protocol_revenue_zusd_cum_e8
        - result.pre_state.protocol_revenue_zusd_cum_e8
        == result.fee_e8
    )
    assert revalidate_zusd_authenticated_borrow_fee_occurrence_v1(result)
    assert (
        verify_zusd_authenticated_borrow_fee_occurrence_v1(
            source=source,
            candidate=result,
        )
        is result
    )


def test_occurrence_rejects_principal_or_pre_state_substitution() -> None:
    pre = _pre_state()
    identity = _identity(pre_state=pre, principal_e8=100 * E8)
    changed_principal = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        _source(pre_state=pre, principal_e8=101 * E8, identity=identity)
    )
    changed_state = replace(pre, collateral_e8=3 * E8)
    crossed_state = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        _source(pre_state=changed_state, principal_e8=100 * E8, identity=identity)
    )

    _assert_reject(
        changed_principal,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.COMMAND_ROOT_MISMATCH,
    )
    _assert_reject(
        crossed_state,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.COMMAND_ROOT_MISMATCH,
    )


def test_occurrence_rejects_wrong_family_bool_and_zero_fee() -> None:
    pre = _pre_state()
    wrong_family = _identity(
        pre_state=pre,
        principal_e8=100 * E8,
        command_family=E01CommandFamilyV1.RECOVERY,
    )
    family_result = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        _source(pre_state=pre, identity=wrong_family)
    )
    valid_identity = _identity(pre_state=pre, principal_e8=100 * E8)
    bool_result = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1(
            request_identity=valid_identity,
            pre_state=pre,
            principal_e8=True,
        )
    )
    no_fee_state = _pre_state(fee_bps=0)
    no_fee = derive_zusd_authenticated_borrow_fee_occurrence_v1(_source(pre_state=no_fee_state))

    _assert_reject(
        family_result,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.WRONG_COMMAND_FAMILY,
    )
    _assert_reject(
        bool_result,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.INVALID_PRINCIPAL,
    )
    _assert_reject(
        no_fee,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.ZERO_FEE,
    )


def test_occurrence_rejects_forged_or_mutated_request_identity() -> None:
    pre = _pre_state()
    identity = _identity(pre_state=pre, principal_e8=100 * E8)
    object.__setattr__(identity, "nonce", 10)

    result = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        _source(pre_state=pre, identity=identity)
    )

    _assert_reject(
        result,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.INVALID_REQUEST_IDENTITY,
    )


def test_occurrence_candidate_rejects_hostile_post_derivation_mutation() -> None:
    source = _source()
    result = derive_zusd_authenticated_borrow_fee_occurrence_v1(source)
    assert type(result) is ZUSDAuthenticatedBorrowFeeOccurrenceV1
    object.__setattr__(result, "fee_e8", result.fee_e8 + 1)

    assert not revalidate_zusd_authenticated_borrow_fee_occurrence_v1(result)
    verified = verify_zusd_authenticated_borrow_fee_occurrence_v1(
        source=source,
        candidate=result,
    )
    _assert_reject(
        verified,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.CANDIDATE_MISMATCH,
    )


def test_occurrence_public_constructor_cannot_mint_controlled_evidence() -> None:
    result = derive_zusd_authenticated_borrow_fee_occurrence_v1(_source())
    assert type(result) is ZUSDAuthenticatedBorrowFeeOccurrenceV1

    with pytest.raises(TypeError, match="requires replay"):
        ZUSDAuthenticatedBorrowFeeOccurrenceV1(
            request_identity=result.request_identity,
            pre_state=result.pre_state,
            post_state=result.post_state,
            principal_e8=result.principal_e8,
            fee_e8=result.fee_e8,
            fee_bps=result.fee_bps,
            debt_delta_e8=result.debt_delta_e8,
            occurrence_root=result.occurrence_root,
        )


def test_occurrence_root_is_deterministic_and_sensitive_to_authenticated_lineage() -> None:
    first = derive_zusd_authenticated_borrow_fee_occurrence_v1(_source())
    second = derive_zusd_authenticated_borrow_fee_occurrence_v1(_source())
    assert type(first) is ZUSDAuthenticatedBorrowFeeOccurrenceV1
    assert type(second) is ZUSDAuthenticatedBorrowFeeOccurrenceV1
    assert first.occurrence_root == second.occurrence_root

    pre = _pre_state()
    changed_identity = _identity(pre_state=pre, principal_e8=100 * E8)
    object.__setattr__(changed_identity, "request_identity_root", "4" * 64)
    changed = derive_zusd_authenticated_borrow_fee_occurrence_v1(
        _source(pre_state=pre, identity=changed_identity)
    )
    _assert_reject(
        changed,
        ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.INVALID_REQUEST_IDENTITY,
    )
