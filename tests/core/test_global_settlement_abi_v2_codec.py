from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.asset_transfer_types_v1 import AssetTransferCommandV1
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetClassV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferStateV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_abi_v2_codec import (
    GlobalSettlementCodecErrorV2,
    decode_asset_transfer_command_v2,
    decode_asset_transfer_context_v2,
    decode_asset_transfer_state_v2,
    encode_asset_transfer_command_v2,
    encode_asset_transfer_context_v2,
    encode_asset_transfer_state_v2,
)
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1
from src.core.global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)


def _root(label: str) -> str:
    return hash_global_v2("codec-test-root-v2", {"label": label})


def _command() -> AssetTransferCommandV2:
    return AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset="USD",
        sender="alice",
        recipient="bob",
        amount_atoms=25,
        max_fee_atoms=2,
        asset_origin_root=_root("origin:USD"),
    )


def _occurrence(command: AssetTransferCommandV2) -> EconomicCommandOccurrenceV2:
    return EconomicCommandOccurrenceV2(
        chain_id="zeno-codec-test",
        deployment_root=_root("deployment"),
        height=11,
        tx_index=2,
        op_index=1,
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        route_release_id=_root("route-release"),
        subject_id=command.sender,
        grant_root=_root("grant"),
        nonce=17,
        profile_root=_root("profile"),
        pre_state_root=_root("global-pre-state"),
        consumed_object_ids=(),
    )


def _context(command: AssetTransferCommandV2) -> AssetTransferContextV2:
    occurrence = _occurrence(command)
    return AssetTransferContextV2(
        writer_epoch=4,
        module_release_id=_root("module-release"),
        global_pre_state_root=occurrence.pre_state_root,
        occurrence=occurrence,
    )


def _state() -> AssetTransferStateV2:
    return AssetTransferStateV2(
        module_release_id=_root("module-release"),
        policies=(
            AssetTransferPolicyV2(
                asset="USD",
                fee_owner="treasury",
                transfer_fee_atoms=2,
                enabled=True,
                asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
                asset_origin_root=_root("origin:USD"),
                atom_decimals=ASSET_ATOM_DECIMALS_V2,
            ),
        ),
        balances=(EconomicAmountV2("alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 100),),
        supplies=(AssetSupplyV2("USD", 100),),
    )


def test_command_context_and_state_round_trip_exact_canonical_bytes() -> None:
    command = _command()
    context = _context(command)
    state = _state()

    assert decode_asset_transfer_command_v2(encode_asset_transfer_command_v2(command)) == command
    assert decode_asset_transfer_context_v2(encode_asset_transfer_context_v2(context)) == context
    assert decode_asset_transfer_state_v2(encode_asset_transfer_state_v2(state)) == state


def test_codec_rejects_duplicate_unknown_and_noncanonical_fields() -> None:
    command = _command()
    canonical = encode_asset_transfer_command_v2(command)
    duplicate = canonical.replace(
        b'"amount_atoms":25',
        b'"amount_atoms":25,"amount_atoms":25',
    )
    with pytest.raises(GlobalSettlementCodecErrorV2, match="duplicate field"):
        decode_asset_transfer_command_v2(duplicate)

    unknown = command.to_canonical() | {"unknown": True}
    with pytest.raises(GlobalSettlementCodecErrorV2, match="field set"):
        decode_asset_transfer_command_v2(canonical_global_bytes_v2(unknown))

    with pytest.raises(GlobalSettlementCodecErrorV2, match="canonical"):
        decode_asset_transfer_command_v2(canonical + b"\n")


def test_codec_rejects_float_boolean_and_cross_version_command() -> None:
    command = _command()
    floating = encode_asset_transfer_command_v2(command).replace(
        b'"amount_atoms":25',
        b'"amount_atoms":25.0',
    )
    with pytest.raises(GlobalSettlementCodecErrorV2, match="floating-point"):
        decode_asset_transfer_command_v2(floating)

    boolean_alias = command.to_canonical() | {"amount_atoms": True}
    with pytest.raises(GlobalSettlementCodecErrorV2, match="non-negative integer"):
        decode_asset_transfer_command_v2(canonical_global_bytes_v2(boolean_alias))

    old_command = AssetTransferCommandV1(
        command_kind="asset_transfer",
        asset="USD",
        sender="alice",
        recipient="bob",
        amount_atoms=25,
        max_fee_atoms=2,
    )
    with pytest.raises(GlobalSettlementCodecErrorV2, match="field set"):
        decode_asset_transfer_command_v2(canonical_global_bytes_v1(old_command))


def test_context_decoder_requires_v2_occurrence_schema_and_closed_fields() -> None:
    command = _command()
    context = _context(command)
    body = context.to_canonical()
    occurrence = context.occurrence
    assert occurrence is not None

    old_schema_occurrence = occurrence.to_canonical() | {
        "schema": "zenodex/global-settlement-abi/v1"
    }
    with pytest.raises(GlobalSettlementCodecErrorV2, match="occurrence schema"):
        decode_asset_transfer_context_v2(
            canonical_global_bytes_v2(body | {"occurrence": old_schema_occurrence})
        )

    unknown_occurrence = occurrence.to_canonical() | {"unknown": "field"}
    with pytest.raises(GlobalSettlementCodecErrorV2, match="occurrence field set"):
        decode_asset_transfer_context_v2(
            canonical_global_bytes_v2(body | {"occurrence": unknown_occurrence})
        )


def test_missing_occurrence_is_an_explicit_typed_context_value() -> None:
    context = replace(_context(_command()), occurrence=None)

    assert decode_asset_transfer_context_v2(encode_asset_transfer_context_v2(context)) == context


def test_state_decoder_rejects_cross_version_schema_and_unknown_nested_fields() -> None:
    state = _state()
    body = state.to_canonical()
    with pytest.raises(GlobalSettlementCodecErrorV2, match="state schema"):
        decode_asset_transfer_state_v2(
            canonical_global_bytes_v2(body | {"schema": "zenodex/asset-transfer-module/v1"})
        )

    policy = state.policies[0].to_canonical() | {"unknown": True}
    with pytest.raises(GlobalSettlementCodecErrorV2, match="policy field set"):
        decode_asset_transfer_state_v2(canonical_global_bytes_v2(body | {"policies": [policy]}))

    occurrence = _occurrence(_command())
    assert occurrence.to_canonical()["schema"] == GLOBAL_SETTLEMENT_ABI_V2
