"""Complete joint replay and transport limits; these tests grant no proof authority."""

from dataclasses import replace

import pytest

from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_transfer_types_v2 import ACCOUNT_CUSTODY_DOMAIN_V2
from src.core.global_settlement_types_v2 import EconomicAmountV2, canonical_global_bytes_v2
from src.core.global_settlement_wire_codec_v2 import _load_canonical_object_v2
from src.core.perps_margin_receipt_v2 import encode_perps_margin_frame_v2
from src.core.perps_margin_state_v2 import PerpsMarginStateV2
from src.core.perps_margin_types_v1 import PerpsMarginAccountStatusV1, PerpsMarginAccountV1
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration.custody_publication_record_v2 import (
    JOINT_MARGIN_FRAME_MAGIC_V2,
    decode_joint_margin_genesis_v2,
    encode_joint_margin_genesis_v2,
    frame_joint_margin_publication_v2,
    replay_joint_margin_publication_v2,
)
from tests.core.test_perps_margin_global_v2 import DEPOSIT, _command, _initial, _occurrence


def test_joint_genesis_preserves_each_existing_component_byte_capacity():
    assets, margin, _ = _initial()
    # Each principal uses 160 admitted ASCII bytes, including JSON escapes.
    # The individually valid asset component fits by 97 bytes; the old combined
    # JSON envelope exceeded its decoder's 1 MiB bound when margin was added.
    count = 2698
    rows = tuple(EconomicAmountV2(
        f'{index:04d}' + '"' * 156, "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 1,
    ) for index in range(count))
    leaf = replace(assets.transfer_state, balances=rows, supplies=tuple(
        replace(row, amount_atoms=count) for row in assets.transfer_state.supplies
    ))
    assets = AssetLaneCustodyStateV2(leaf, assets.origin_registry, assets.managed_policies, ())
    accounts = tuple(PerpsMarginAccountV1(
        f"a{index:02d}", "alice", 0, 0, 0, 0, PerpsMarginAccountStatusV1.OPEN,
    ) for index in range(64))
    margin = PerpsMarginStateV2(replace(margin.economic_state, accounts=accounts), ())
    asset_raw, margin_raw = canonical_global_bytes_v2(assets), canonical_global_bytes_v2(margin)
    assert len(asset_raw) == 1_048_479
    assert len(margin_raw) == 8091
    old_envelope = canonical_global_bytes_v2({
        "schema": "zenodex/isolated-joint-margin-genesis/v2", "assets": assets, "margin": margin,
    })
    with pytest.raises(ValueError, match="byte bound"):
        _load_canonical_object_v2(old_envelope)
    decoded_assets, decoded_margin = decode_joint_margin_genesis_v2(
        encode_joint_margin_genesis_v2(assets, margin)
    )
    assert canonical_global_bytes_v2(decoded_assets) == asset_raw
    assert canonical_global_bytes_v2(decoded_margin) == margin_raw


@pytest.mark.parametrize("fault", ["truncated", "trailing", "zero_length", "oversized", "foreign"])
def test_malformed_joint_genesis_is_never_an_admitted_snapshot(fault):
    assets, margin, _ = _initial()
    raw = encode_joint_margin_genesis_v2(assets, margin)
    if fault == "truncated":
        raw = raw[:-1]
    elif fault == "trailing":
        raw += b"x"
    elif fault == "zero_length":
        raw = raw[:6] + b"\x00" * 4 + raw[10:]
    elif fault == "oversized":
        raw = raw[:6] + (1_048_577).to_bytes(4, "little") + raw[10:]
    else:
        raw = b"ZDJG1\x00" + raw[6:]
    with pytest.raises(ValueError):
        decode_joint_margin_genesis_v2(raw)


def test_margin_replay_binds_actual_account_custody_liability_and_both_lanes():
    assets, margin, state = _initial()
    command = _command(DEPOSIT, 30, 1)
    request = PerpsMarginRequestV2(command, _occurrence(state, command, 1))
    raw = frame_joint_margin_publication_v2(
        encode_perps_margin_frame_v2(assets, margin, state, request), None,
    )
    replay = replay_joint_margin_publication_v2(raw)
    assert replay.margin_pre.state_root == margin.state_root
    assert replay.margin_post.economic_state.accounts[0].collateral_atoms == 30
    assert replay.global_post.balances[0].amount_atoms == 70
    assert replay.global_post.custody[0].owner == command.account_id
    assert replay.global_post.custody[0].amount_atoms == 30
    assert replay.global_post.liabilities[0].owner == "alice"
    assert replay.global_post.liabilities[0].amount_atoms == 30
    assert replay.lane_post.state_root != assets.state_root
    assert replay.global_post.supplies == state.supplies
    assert replay.margin_post.claim_id(command.account_id) is not None
    assert len(replay.global_post.replay_state) == 1


@pytest.mark.parametrize("suffix", [b"", b"\x02", b"\x00", b"\x00" + b"\xff" * 4, b"\x01"])
def test_joint_frame_requires_an_exact_complete_supported_route(suffix):
    with pytest.raises(ValueError):
        replay_joint_margin_publication_v2(JOINT_MARGIN_FRAME_MAGIC_V2 + suffix)
