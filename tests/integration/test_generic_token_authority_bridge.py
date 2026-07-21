from __future__ import annotations

from copy import deepcopy

import pytest

from src.core.generic_token_authority import (
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
)
from src.integration.generic_token_authority_bridge import (
    generic_token_authority_from_obj,
    generic_token_authority_to_obj,
)

ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ACTOR = "0x" + "aa" * 48


def _state() -> GenericTokenAuthorityState:
    return GenericTokenAuthorityState(
        assets=(
            GenericTokenAssetAuthority(ASSET_A, 0, ACTOR),
            GenericTokenAssetAuthority(ASSET_B, 7, None),
        )
    )


def test_authority_round_trip_preserves_zero_supply_registration() -> None:
    state = _state()
    encoded = generic_token_authority_to_obj(state)

    assert generic_token_authority_from_obj(encoded) == state
    assert encoded["assets"] == [
        {
            "asset_id": ASSET_A,
            "total_supply_units": 0,
            "mint_authority_pubkey": ACTOR,
        },
        {
            "asset_id": ASSET_B,
            "total_supply_units": 7,
            "mint_authority_pubkey": None,
        },
    ]


@pytest.mark.parametrize(
    "mutation",
    (
        lambda obj: obj.update({"unknown": 1}),
        lambda obj: obj["assets"].reverse(),
        lambda obj: obj["assets"][0].update({"asset_id": ASSET_A.upper()}),
        lambda obj: obj["assets"][0].update({"total_supply_units": True}),
        lambda obj: obj["assets"][0].update({"mint_authority_pubkey": 1}),
        lambda obj: obj.update({"assets": None}),
    ),
)
def test_decoder_rejects_noncanonical_or_ambiguous_wire_data(mutation) -> None:
    bad = deepcopy(generic_token_authority_to_obj(_state()))
    mutation(bad)

    with pytest.raises((TypeError, ValueError)):
        generic_token_authority_from_obj(bad)


def test_decoded_authority_owns_input_data() -> None:
    encoded = generic_token_authority_to_obj(_state())
    decoded = generic_token_authority_from_obj(encoded)

    encoded["assets"][0]["total_supply_units"] = 123
    assert decoded.get_asset(ASSET_A).total_supply_units == 0
