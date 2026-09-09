"""Exact cross-language statement vectors retain complete economic disclosures."""

import json

import pytest

from src.core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from src.core.asset_lane_custody_input_v2 import _decode_context
from src.core.asset_lane_custody_statement_v2 import prepare_asset_lane_custody_global_statement_v2
from src.core.global_settlement_abi_v2_codec import (
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from src.core.global_settlement_wire_codec_v2 import _decode_global_state_object_v2
from tools.render_asset_lane_custody_statement_v2_golden import FIXTURE, build_fixture

CASES = json.loads(FIXTURE.read_bytes())["cases"]


def typed_inputs(case):
    command_decoder = (
        decode_asset_transfer_command_v2
        if case["route"] == "TRANSFER"
        else decode_managed_asset_lifecycle_command_v2
    )
    return (
        _decode_context(canonical_global_bytes_v2(case["context"])),
        decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(case["pre_state"])),
        command_decoder(canonical_global_bytes_v2(case["command"])),
        _decode_global_state_object_v2(case["global_pre"]),
        _decode_global_state_object_v2(case["global_post"]),
    )


def test_statement_disclosures_and_independent_oracle_are_current():
    assert FIXTURE.read_bytes() == build_fixture()


@pytest.mark.parametrize("case", CASES, ids=lambda case: case["name"])
def test_actual_producer_matches_the_full_fixed_statement(case):
    produced = prepare_asset_lane_custody_global_statement_v2(*typed_inputs(case))
    assert type(produced) is bytes
    assert produced == canonical_global_bytes_v2(case["statement"])
    assert set(json.loads(produced)) == {
        "schema",
        "module_journal",
        "global_pre_state_root",
        "global_post_state_root",
    }
