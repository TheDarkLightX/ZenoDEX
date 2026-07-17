from __future__ import annotations

from dataclasses import FrozenInstanceError
from itertools import product

import pytest

from src.core.zusd_generic_token_admission import (
    MAX_TOKEN_UNITS,
    CanonicalZUSDCustodyClass,
    CanonicalZUSDCustodyRegistry,
    CanonicalZUSDSupplyState,
    GenericTokenAction,
    GenericTokenAdmissionCode,
    GenericTokenAdmissionCommand,
    ReservedCanonicalZUSDCustodyPrincipal,
    TokenAssetClass,
    TokenWriterRole,
    evaluate_generic_token_admission,
    evaluate_generic_token_admission_transition,
)


def _expected_code(
    action: GenericTokenAction,
    *,
    asset_class: TokenAssetClass,
    writer_role: TokenWriterRole,
    custody_class: CanonicalZUSDCustodyClass,
) -> GenericTokenAdmissionCode:
    if writer_role is TokenWriterRole.ZUSD_MONETARY_AUTHORITY:
        return GenericTokenAdmissionCode.ROUTE_TO_ZUSD_MONETARY_KERNEL
    if asset_class is TokenAssetClass.OTHER:
        return GenericTokenAdmissionCode.ADMITTED
    if action is GenericTokenAction.MINT:
        return GenericTokenAdmissionCode.CANONICAL_ZUSD_MINT_REQUIRES_MONETARY_AUTHORITY
    if action is GenericTokenAction.BURN:
        return GenericTokenAdmissionCode.CANONICAL_ZUSD_BURN_REQUIRES_MONETARY_AUTHORITY
    if custody_class.is_reserved_internal_custody:
        return (
            GenericTokenAdmissionCode.CANONICAL_ZUSD_RESERVED_CUSTODY_REQUIRES_MONETARY_AUTHORITY
        )
    return GenericTokenAdmissionCode.ADMITTED


def test_authority_policy_is_exhaustive_over_all_typed_cases() -> None:
    cases = list(
        product(
            GenericTokenAction,
            TokenAssetClass,
            TokenWriterRole,
            CanonicalZUSDCustodyClass,
        )
    )
    assert len(cases) == 108

    for action, asset_class, writer_role, custody_class in cases:
        command = GenericTokenAdmissionCommand(
            action=action,
            asset_class=asset_class,
            writer_role=writer_role,
            recipient_custody_class=custody_class,
        )
        decision = evaluate_generic_token_admission(command)
        expected = _expected_code(
            action,
            asset_class=asset_class,
            writer_role=writer_role,
            custody_class=custody_class,
        )
        assert decision.code is expected
        assert decision.admitted is (expected is GenericTokenAdmissionCode.ADMITTED)
        assert decision.requires_zusd_monetary_kernel is (
            expected is GenericTokenAdmissionCode.ROUTE_TO_ZUSD_MONETARY_KERNEL
        )
        assert decision.canonical_zusd_supply_delta == 0


@pytest.mark.parametrize("action", GenericTokenAction)
@pytest.mark.parametrize("asset_class", TokenAssetClass)
@pytest.mark.parametrize("custody_class", CanonicalZUSDCustodyClass)
def test_monetary_authority_is_routed_to_its_separate_kernel(
    action: GenericTokenAction,
    asset_class: TokenAssetClass,
    custody_class: CanonicalZUSDCustodyClass,
) -> None:
    decision = evaluate_generic_token_admission(
        GenericTokenAdmissionCommand(
            action,
            asset_class,
            TokenWriterRole.ZUSD_MONETARY_AUTHORITY,
            custody_class,
        )
    )
    assert decision.code is GenericTokenAdmissionCode.ROUTE_TO_ZUSD_MONETARY_KERNEL
    assert decision.admitted is False
    assert decision.requires_zusd_monetary_kernel is True


@pytest.mark.parametrize("custody_class", CanonicalZUSDCustodyClass)
@pytest.mark.parametrize("action", (GenericTokenAction.MINT, GenericTokenAction.BURN))
def test_generic_writer_cannot_change_canonical_zusd_supply_authority(
    action: GenericTokenAction,
    custody_class: CanonicalZUSDCustodyClass,
) -> None:
    decision = evaluate_generic_token_admission(
        GenericTokenAdmissionCommand(
            action=action,
            asset_class=TokenAssetClass.CANONICAL_ZUSD,
            writer_role=TokenWriterRole.GENERIC_TOKEN_WRITER,
            recipient_custody_class=custody_class,
        )
    )
    assert decision.admitted is False
    assert decision.canonical_zusd_supply_delta == 0


@pytest.mark.parametrize(
    "custody_class",
    tuple(
        custody_class
        for custody_class in CanonicalZUSDCustodyClass
        if custody_class.is_reserved_internal_custody
    ),
)
def test_every_reserved_custody_role_rejects_generic_canonical_transfer(
    custody_class: CanonicalZUSDCustodyClass,
) -> None:
    decision = evaluate_generic_token_admission(
        GenericTokenAdmissionCommand(
            action=GenericTokenAction.TRANSFER,
            asset_class=TokenAssetClass.CANONICAL_ZUSD,
            writer_role=TokenWriterRole.GENERIC_TOKEN_WRITER,
            recipient_custody_class=custody_class,
        )
    )
    assert decision.code is (
        GenericTokenAdmissionCode.CANONICAL_ZUSD_RESERVED_CUSTODY_REQUIRES_MONETARY_AUTHORITY
    )


@pytest.mark.parametrize("supply", (0, 1, MAX_TOKEN_UNITS))
def test_ordinary_canonical_zusd_transfer_is_admitted_and_supply_preserving(
    supply: int,
) -> None:
    state = CanonicalZUSDSupplyState(supply)
    transition = evaluate_generic_token_admission_transition(
        state,
        GenericTokenAdmissionCommand(
            action=GenericTokenAction.TRANSFER,
            asset_class=TokenAssetClass.CANONICAL_ZUSD,
            writer_role=TokenWriterRole.GENERIC_TOKEN_WRITER,
            recipient_custody_class=CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT,
        ),
    )
    assert transition.decision.admitted is True
    assert transition.decision.canonical_zusd_supply_delta == 0
    assert transition.post_state is state
    assert transition.state_unchanged is True


@pytest.mark.parametrize("supply", (0, 17, MAX_TOKEN_UNITS))
def test_every_policy_rejection_is_an_identity_transition(supply: int) -> None:
    state = CanonicalZUSDSupplyState(supply)
    rejected_commands = (
        GenericTokenAdmissionCommand(
            GenericTokenAction.MINT,
            TokenAssetClass.CANONICAL_ZUSD,
            TokenWriterRole.GENERIC_TOKEN_WRITER,
            CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT,
        ),
        GenericTokenAdmissionCommand(
            GenericTokenAction.BURN,
            TokenAssetClass.CANONICAL_ZUSD,
            TokenWriterRole.GENERIC_TOKEN_WRITER,
            CanonicalZUSDCustodyClass.HOST_FEE_POOL_LEDGER,
        ),
        GenericTokenAdmissionCommand(
            GenericTokenAction.TRANSFER,
            TokenAssetClass.CANONICAL_ZUSD,
            TokenWriterRole.GENERIC_TOKEN_WRITER,
            CanonicalZUSDCustodyClass.STABILITY_POOL_ESCROW,
        ),
    )
    for command in rejected_commands:
        transition = evaluate_generic_token_admission_transition(state, command)
        assert transition.decision.admitted is False
        assert transition.pre_state is state
        assert transition.post_state is state
        assert transition.state_unchanged is True


def test_reserved_custody_registry_is_immutable_sorted_and_exact() -> None:
    stability_pool = ReservedCanonicalZUSDCustodyPrincipal(
        "0x01", CanonicalZUSDCustodyClass.STABILITY_POOL_ESCROW
    )
    bridge = ReservedCanonicalZUSDCustodyPrincipal(
        "0x02", CanonicalZUSDCustodyClass.BRIDGE_ESCROW
    )
    registry = CanonicalZUSDCustodyRegistry((stability_pool, bridge))
    assert registry.classify("0x01") is CanonicalZUSDCustodyClass.STABILITY_POOL_ESCROW
    assert registry.classify("0x02") is CanonicalZUSDCustodyClass.BRIDGE_ESCROW
    assert registry.classify("0x03") is CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT

    with pytest.raises(ValueError, match="strictly sorted"):
        CanonicalZUSDCustodyRegistry((bridge, stability_pool))
    with pytest.raises(ValueError, match="strictly sorted"):
        CanonicalZUSDCustodyRegistry((stability_pool, stability_pool))
    with pytest.raises(ValueError, match="ordinary accounts"):
        ReservedCanonicalZUSDCustodyPrincipal(
            "0x03", CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT
        )


def test_inputs_and_outputs_are_strictly_typed_and_immutable() -> None:
    with pytest.raises(TypeError, match="action"):
        GenericTokenAdmissionCommand(  # type: ignore[arg-type]
            "transfer",
            TokenAssetClass.CANONICAL_ZUSD,
            TokenWriterRole.GENERIC_TOKEN_WRITER,
            CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT,
        )
    with pytest.raises(TypeError, match="asset_class"):
        GenericTokenAdmissionCommand(  # type: ignore[arg-type]
            GenericTokenAction.TRANSFER,
            "canonical_zusd",
            TokenWriterRole.GENERIC_TOKEN_WRITER,
            CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT,
        )
    with pytest.raises(TypeError, match="writer_role"):
        GenericTokenAdmissionCommand(  # type: ignore[arg-type]
            GenericTokenAction.TRANSFER,
            TokenAssetClass.CANONICAL_ZUSD,
            "generic_token_writer",
            CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT,
        )
    with pytest.raises(TypeError, match="recipient_custody_class"):
        GenericTokenAdmissionCommand(  # type: ignore[arg-type]
            GenericTokenAction.TRANSFER,
            TokenAssetClass.CANONICAL_ZUSD,
            TokenWriterRole.GENERIC_TOKEN_WRITER,
            "ordinary_account",
        )
    with pytest.raises(TypeError, match="total_supply_units"):
        CanonicalZUSDSupplyState(True)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="total_supply_units"):
        CanonicalZUSDSupplyState(MAX_TOKEN_UNITS + 1)

    command = GenericTokenAdmissionCommand(
        GenericTokenAction.TRANSFER,
        TokenAssetClass.CANONICAL_ZUSD,
        TokenWriterRole.GENERIC_TOKEN_WRITER,
        CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT,
    )
    with pytest.raises(FrozenInstanceError):
        command.asset_class = TokenAssetClass.OTHER  # type: ignore[misc]
