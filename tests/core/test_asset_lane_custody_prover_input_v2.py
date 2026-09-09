"""The proving input derives its successor without trusting a proposed state."""

import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

from src.core import asset_lane_custody_input_v2 as inputs
from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
from src.core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_transfer_types_v2 import AssetTransferRejectCodeV2
from src.core.global_settlement_abi_v2_codec import (
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from src.core.global_settlement_wire_codec_v2 import _decode_global_state_object_v2
from tests.core.test_asset_lane_coordinator_v2 import _root
from tests.core.test_asset_lane_custody_statement_v2 import _case


def test_predecessor_only_preparation_reproduces_all_five_independent_guest_frames():
    fixture = json.loads(
        (Path(__file__).parents[1] / "data/asset_lane_custody_statement_v2_golden.json").read_bytes()
    )
    for case in fixture["cases"]:
        context = inputs._decode_context(canonical_global_bytes_v2(case["context"]))
        lane = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(case["pre_state"]))
        decoder = (
            decode_asset_transfer_command_v2
            if case["route"] == "TRANSFER"
            else decode_managed_asset_lifecycle_command_v2
        )
        command = decoder(canonical_global_bytes_v2(case["command"]))
        before = _decode_global_state_object_v2(case["global_pre"])

        frame = inputs.prepare_asset_lane_custody_global_prover_input_v2(
            context, lane, command, before
        )

        assert type(frame) is bytes
        assert hashlib.sha256(frame).hexdigest() == case["frame_sha256"], case["name"]


@pytest.mark.parametrize("tamper", ("command", "subject"))
def test_rejected_command_produces_no_proving_input_or_state_change(tamper):
    context, lane, command, _, before, _ = _case()
    if tamper == "command":
        command = replace(command, sender="mallory")
        expected = AssetTransferRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH
    else:
        context = AssetLaneContextV2(
            context.writer_epoch, context.module_release_id, context.global_pre_state_root,
            replace(context.occurrence, subject_id="mallory"),
        )
        expected = AssetTransferRejectCodeV2.UNAUTHORIZED_SUBJECT
    captured = canonical_global_bytes_v2((context, lane, command, before))
    rejected = inputs.prepare_asset_lane_custody_global_prover_input_v2(
        context, lane, command, before
    )
    assert type(rejected) is AssetLaneRejectedV2
    assert rejected.code is expected
    assert rejected.effects.is_empty
    assert canonical_global_bytes_v2((context, lane, command, before)) == captured


def test_conserved_foreign_predecessor_cannot_be_framed_for_proving():
    context, lane, command, _, before, _ = _case()
    foreign = replace(before, history_root=_root("foreign-history"))
    captured = canonical_global_bytes_v2((lane, before, foreign))
    with pytest.raises(ValueError, match="occurrence context mismatch"):
        inputs.prepare_asset_lane_custody_global_prover_input_v2(context, lane, command, foreign)
    assert canonical_global_bytes_v2((lane, before, foreign)) == captured
