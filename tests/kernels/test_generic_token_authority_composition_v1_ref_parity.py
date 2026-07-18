from __future__ import annotations

import hashlib
import importlib.util
import re
import sys
from pathlib import Path
from types import ModuleType

from src.core.generic_token_authority import (
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
    GenericTokenSupplyAction,
    GenericTokenSupplyCommand,
    apply_generic_token_supply_command,
)

EXPECTED_IR_HASH = (
    "sha256:93724fb62b0c15b77e0cec37d21e7f0a76a1dacb0bb26e0bd22527169b4947a8"
)
EXPECTED_MODEL_SOURCE_SHA256 = (
    "61d3b7f130f26bf24ca9577fcffaf4a8470d095bae7e607cee6911de28c03a96"
)

ASSET = "11" * 32
AUTHORITY = "22" * 48
OTHER_ACTOR = "33" * 48
RECIPIENT = "44" * 48


def _paths() -> tuple[Path, Path]:
    root = Path(__file__).resolve().parents[2]
    model = (
        root
        / "src"
        / "kernels"
        / "dex"
        / "generic_token_authority_composition_v1.yaml"
    )
    reference = (
        root
        / "generated"
        / "generic_token_authority_composition_v1"
        / "python_ref"
        / "generic_token_authority_composition_v1_ref.py"
    )
    return model, reference


def _load_reference() -> ModuleType:
    _, reference = _paths()
    module_name = (
        "generated.generic_token_authority_composition_v1.python_ref.reference"
    )
    spec = importlib.util.spec_from_file_location(module_name, reference)
    if spec is None or spec.loader is None:
        raise AssertionError("could not load generated ESSO Python reference")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _authority_state(supply: int) -> GenericTokenAuthorityState:
    return GenericTokenAuthorityState(
        assets=(
            GenericTokenAssetAuthority(
                asset_id=ASSET,
                total_supply_units=supply,
                mint_authority_pubkey=AUTHORITY,
            ),
        )
    )


def test_generated_reference_is_hash_bound_to_validated_esso_ir() -> None:
    model, reference = _paths()
    source = reference.read_text(encoding="utf-8")
    match = re.search(r"^IR hash: (sha256:[0-9a-f]{64})$", source, re.MULTILINE)

    assert match is not None
    assert hashlib.sha256(model.read_bytes()).hexdigest() == (
        EXPECTED_MODEL_SOURCE_SHA256
    )
    assert match.group(1) == EXPECTED_IR_HASH


def test_generated_reference_matches_supply_core_on_bounded_legal_actions() -> None:
    reference = _load_reference()
    for supply in (0, 1, 2):
        for amount in (1, 2):
            if supply + amount <= 2:
                core_mint = apply_generic_token_supply_command(
                    _authority_state(supply),
                    GenericTokenSupplyCommand(
                        action=GenericTokenSupplyAction.MINT,
                        asset_id=ASSET,
                        actor_pubkey=AUTHORITY,
                        amount_units=amount,
                        recipient_pubkey=RECIPIENT,
                    ),
                )
                model_mint = reference.step(
                    reference.State(
                        active_stake_units=0,
                        mint_authority_code=0,
                        pending_stake_units=0,
                        perps_units=0,
                        pool_units=0,
                        registered=1,
                        supply_units=supply,
                        token_nonce=0,
                        wallet_units=supply,
                    ),
                    reference.Command(
                        tag="mint",
                        args={"actor_code": 0, "amount_units": amount},
                    ),
                )
                assert core_mint.accepted is True
                assert core_mint.next_state is not None
                assert model_mint.ok is True
                assert model_mint.state is not None
                assert model_mint.effects is not None
                assert model_mint.effects["accepted"] is True
                assert model_mint.effects["rejection_noop"] is False
                minted_asset = core_mint.next_state.get_asset(ASSET)
                assert minted_asset is not None
                assert model_mint.state.supply_units == minted_asset.total_supply_units

            if amount <= supply:
                core_burn = apply_generic_token_supply_command(
                    _authority_state(supply),
                    GenericTokenSupplyCommand(
                        action=GenericTokenSupplyAction.BURN,
                        asset_id=ASSET,
                        actor_pubkey=AUTHORITY,
                        amount_units=amount,
                    ),
                )
                model_burn = reference.step(
                    reference.State(
                        active_stake_units=0,
                        mint_authority_code=0,
                        pending_stake_units=0,
                        perps_units=0,
                        pool_units=0,
                        registered=1,
                        supply_units=supply,
                        token_nonce=0,
                        wallet_units=supply,
                    ),
                    reference.Command(
                        tag="burn",
                        args={"amount_units": amount},
                    ),
                )
                assert core_burn.accepted is True
                assert core_burn.next_state is not None
                assert model_burn.ok is True
                assert model_burn.state is not None
                assert model_burn.effects is not None
                assert model_burn.effects["accepted"] is True
                assert model_burn.effects["rejection_noop"] is False
                burned_asset = core_burn.next_state.get_asset(ASSET)
                assert burned_asset is not None
                assert model_burn.state.supply_units == burned_asset.total_supply_units


def test_generated_reference_matches_unauthorized_mint_rejection_noop() -> None:
    reference = _load_reference()
    prestate = _authority_state(1)
    core = apply_generic_token_supply_command(
        prestate,
        GenericTokenSupplyCommand(
            action=GenericTokenSupplyAction.MINT,
            asset_id=ASSET,
            actor_pubkey=OTHER_ACTOR,
            amount_units=1,
            recipient_pubkey=RECIPIENT,
        ),
    )
    model_prestate = reference.State(
        active_stake_units=0,
        mint_authority_code=0,
        pending_stake_units=0,
        perps_units=0,
        pool_units=0,
        registered=1,
        supply_units=1,
        token_nonce=0,
        wallet_units=1,
    )
    model = reference.step(
        model_prestate,
        reference.Command(
            tag="reject_unauthorized_mint",
            args={"actor_code": 1, "amount_units": 1},
        ),
    )

    assert core.accepted is False
    assert core.next_state is None
    assert model.ok is True
    assert model.state == model_prestate
    assert model.effects is not None
    assert model.effects["accepted"] is False
    assert model.effects["rejection_noop"] is True


def test_generated_reference_location_trace_preserves_supply() -> None:
    reference = _load_reference()
    state = reference.init_state()
    trace = (
        ("faucet_mint", {"actor_code": 0, "amount_units": 2}),
        ("wallet_to_pool", {"amount_units": 1}),
        ("pool_to_wallet", {"amount_units": 1}),
        ("wallet_to_perps", {"amount_units": 1}),
        ("perps_to_wallet", {"amount_units": 1}),
        ("wallet_to_pending_stake", {"amount_units": 1}),
        ("activate_stake", {"amount_units": 1}),
        ("unstake", {"amount_units": 1}),
    )

    for tag, args in trace:
        result = reference.step(state, reference.Command(tag=tag, args=args))
        assert result.ok is True, result.error
        assert result.state is not None
        assert result.effects is not None
        assert result.effects["accepted"] is True
        assert result.effects["rejection_noop"] is False
        state = result.state
        assert reference.check_invariants(state) == (True, None)
        assert state.supply_units == 2

    assert state.wallet_units == 2
    assert state.pool_units == 0
    assert state.perps_units == 0
    assert state.pending_stake_units == 0
    assert state.active_stake_units == 0
