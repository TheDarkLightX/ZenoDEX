from __future__ import annotations

import pytest

from src.core.generic_token_authority import (
    U32_MAX,
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
    GenericTokenSupplyAction,
    GenericTokenSupplyCommand,
    GenericTokenSupplyRejectCode,
    apply_generic_token_supply_command,
)

ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ACTOR_A = "0x" + "aa" * 48
ACTOR_B = "0x" + "bb" * 48


def _state(*, supply_a: int = 0, authority_a: str | None = ACTOR_A) -> GenericTokenAuthorityState:
    return GenericTokenAuthorityState(
        assets=(
            GenericTokenAssetAuthority(ASSET_A, supply_a, authority_a),
            GenericTokenAssetAuthority(ASSET_B, 9, None),
        )
    )


def _command(
    action: GenericTokenSupplyAction,
    *,
    asset: str = ASSET_A,
    actor: str = ACTOR_A,
    amount: int = 1,
) -> GenericTokenSupplyCommand:
    return GenericTokenSupplyCommand(action, asset, actor, amount)


def test_authority_state_is_canonical_and_structurally_immutable() -> None:
    state = _state(supply_a=3)

    assert state.get_asset(ASSET_A) == GenericTokenAssetAuthority(ASSET_A, 3, ACTOR_A)
    assert state.get_asset("0x" + "33" * 32) is None
    with pytest.raises(ValueError, match="strictly sorted"):
        GenericTokenAuthorityState(assets=tuple(reversed(state.assets)))
    with pytest.raises(TypeError, match="tuple"):
        GenericTokenAuthorityState(assets=list(state.assets))  # type: ignore[arg-type]


def test_mint_requires_the_exact_committed_per_asset_authority() -> None:
    initial = _state(supply_a=7)
    accepted = apply_generic_token_supply_command(
        initial,
        _command(GenericTokenSupplyAction.MINT, amount=5),
    )
    rejected = apply_generic_token_supply_command(
        initial,
        _command(GenericTokenSupplyAction.MINT, actor=ACTOR_B, amount=5),
    )

    assert accepted.accepted is True
    assert accepted.next_state is not None
    assert accepted.next_state.get_asset(ASSET_A).total_supply_units == 12
    assert accepted.next_state.get_asset(ASSET_B) == initial.get_asset(ASSET_B)
    assert rejected == apply_generic_token_supply_command(
        initial,
        _command(GenericTokenSupplyAction.MINT, actor=ACTOR_B, amount=5),
    )
    assert rejected.reject_code is GenericTokenSupplyRejectCode.UNAUTHORIZED_MINT
    assert rejected.next_state is None
    assert initial.get_asset(ASSET_A).total_supply_units == 7


def test_burn_to_zero_preserves_registration_and_mint_authority() -> None:
    initial = _state(supply_a=7)
    decision = apply_generic_token_supply_command(
        initial,
        _command(GenericTokenSupplyAction.BURN, actor=ACTOR_B, amount=7),
    )

    assert decision.accepted is True
    assert decision.next_state is not None
    registered = decision.next_state.get_asset(ASSET_A)
    assert registered is not None
    assert registered.total_supply_units == 0
    assert registered.mint_authority_pubkey == ACTOR_A


def test_registered_transfer_preserves_exact_authority_state() -> None:
    state = _state(supply_a=7)
    command = GenericTokenSupplyCommand(
        action=GenericTokenSupplyAction.TRANSFER,
        asset_id=ASSET_A,
        actor_pubkey=ACTOR_A,
        recipient_pubkey=ACTOR_B,
        amount_units=3,
    )

    decision = apply_generic_token_supply_command(state, command)

    assert decision.accepted is True
    assert decision.next_state is state


def test_transfer_rejects_missing_recipient_and_self_transfer() -> None:
    state = _state(supply_a=7)
    missing = apply_generic_token_supply_command(
        state,
        GenericTokenSupplyCommand(
            action=GenericTokenSupplyAction.TRANSFER,
            asset_id=ASSET_A,
            actor_pubkey=ACTOR_A,
            amount_units=1,
        ),
    )
    aliased = apply_generic_token_supply_command(
        state,
        GenericTokenSupplyCommand(
            action=GenericTokenSupplyAction.TRANSFER,
            asset_id=ASSET_A,
            actor_pubkey=ACTOR_A,
            recipient_pubkey=ACTOR_A,
            amount_units=1,
        ),
    )

    assert missing.reject_code is GenericTokenSupplyRejectCode.RECIPIENT_REQUIRED
    assert aliased.reject_code is GenericTokenSupplyRejectCode.SELF_TRANSFER


@pytest.mark.parametrize(
    ("state", "command", "code"),
    (
        (
            _state(supply_a=U32_MAX),
            _command(GenericTokenSupplyAction.MINT),
            GenericTokenSupplyRejectCode.SUPPLY_OVERFLOW,
        ),
        (
            _state(supply_a=0),
            _command(GenericTokenSupplyAction.BURN),
            GenericTokenSupplyRejectCode.SUPPLY_UNDERFLOW,
        ),
        (
            _state(),
            _command(GenericTokenSupplyAction.MINT, asset="0x" + "33" * 32),
            GenericTokenSupplyRejectCode.UNREGISTERED_ASSET,
        ),
        (
            _state(authority_a=None),
            _command(GenericTokenSupplyAction.MINT),
            GenericTokenSupplyRejectCode.MINT_DISABLED,
        ),
        (
            _state(),
            _command(GenericTokenSupplyAction.MINT, amount=0),
            GenericTokenSupplyRejectCode.INVALID_AMOUNT,
        ),
    ),
)
def test_rejections_are_typed_and_carry_no_candidate_state(
    state: GenericTokenAuthorityState,
    command: GenericTokenSupplyCommand,
    code: GenericTokenSupplyRejectCode,
) -> None:
    before = state.assets
    decision = apply_generic_token_supply_command(state, command)

    assert decision.accepted is False
    assert decision.next_state is None
    assert decision.reject_code is code
    assert state.assets is before


def test_boundary_mint_reaches_exact_u32_maximum() -> None:
    decision = apply_generic_token_supply_command(
        _state(supply_a=U32_MAX - 1),
        _command(GenericTokenSupplyAction.MINT),
    )

    assert decision.accepted is True
    assert decision.next_state is not None
    assert decision.next_state.get_asset(ASSET_A).total_supply_units == U32_MAX


@pytest.mark.parametrize("amount", (-1, 0, True, U32_MAX + 1))
def test_amount_domain_rejects_ambiguous_or_out_of_range_values(amount: object) -> None:
    decision = apply_generic_token_supply_command(
        _state(supply_a=1),
        _command(GenericTokenSupplyAction.BURN, amount=amount),  # type: ignore[arg-type]
    )

    assert decision.reject_code is GenericTokenSupplyRejectCode.INVALID_AMOUNT
    assert decision.next_state is None
