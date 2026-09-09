"""Canonical input bytes must reach the actual custody transition and consumer."""

import json
from pathlib import Path

import pytest

import src.core.asset_lane_custody_input_v2 as ingress
from src.core.asset_lane_coordinator_values_v2 import AssetLaneRouteV2
from src.core.asset_lane_custody_coordinator_v2 import AssetLaneCustodyAcceptedV2
from src.core.asset_lane_custody_global_v2 import refine_asset_lane_custody_global_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.global_settlement_abi_v2_codec import GlobalSettlementCodecErrorV2
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from tests.core.test_asset_lane_coordinator_v2 import _transfer_command
from tests.core.test_asset_lane_custody_global_v2 import global_case

CASES = json.loads(
    (Path(__file__).parents[1] / "data/asset_lane_custody_v2_golden.json").read_text()
)["cases"]


def _inputs(case):
    return (
        AssetLaneRouteV2(case["command_type"]),
        *(canonical_global_bytes_v2(case[field]) for field in ("context", "pre_state", "command")),
    )


@pytest.mark.parametrize("case", CASES, ids=lambda case: case["name"])
def test_required_serialized_inputs_preserve_full_golden_outcomes(case):
    result = ingress.transition_asset_lane_custody_bytes_v2(*_inputs(case))
    if type(result) is AssetLaneCustodyAcceptedV2:
        output = {
            "status": "ACCEPTED",
            "route": result.route,
            "source_leaf_journal_root": result.source_leaf_journal_root,
            "source_leaf_receipt_root": result.source_leaf_receipt_root,
            "post_state": result.post_state,
            "effects": result.effects,
            "module_journal": result.module_journal,
        }
    else:
        output = {
            "status": "REJECTED",
            "route": result.route,
            "code": result.code,
            "pre_state_root": result.pre_state_root,
            "post_state_root": result.post_state_root,
            "effects": result.effects,
        }
    assert canonical_global_bytes_v2(output) == canonical_global_bytes_v2(case["output"])
    assert result.production_authority == "NONE"


def test_given_encoded_custody_transfer_then_actual_global_consumer_preserves_claimants():
    lane, expected, before, after, occurrence = global_case()
    context = AssetLaneContextV2(
        before.writer_epoch, lane.transfer_state.module_release_id, before.state_root, occurrence
    )
    accepted = ingress.transition_asset_lane_custody_bytes_v2(
        AssetLaneRouteV2.TRANSFER,
        canonical_global_bytes_v2(context),
        canonical_global_bytes_v2(lane),
        canonical_global_bytes_v2(_transfer_command(amount_atoms=10)),
    )
    assert isinstance(accepted, AssetLaneCustodyAcceptedV2)
    assert accepted.receipt_root == expected.receipt_root
    checked = refine_asset_lane_custody_global_v2(lane, accepted, before, after, occurrence)
    assert checked.post_state_root == after.state_root
    assert before.custody == after.custody
    assert before.liabilities == after.liabilities


@pytest.mark.parametrize("name", ("transfer_nonzero_custody", "issue_nonzero_custody"))
def test_selected_command_shape_retains_unknown_command_leaf_rejection(name):
    case = next(case for case in CASES if case["name"] == name)
    route, context, state, _ = _inputs(case)
    command = case["command"] | {"command_kind": "unknown_command"}
    result = ingress.transition_asset_lane_custody_bytes_v2(
        route,
        context,
        state,
        canonical_global_bytes_v2(command),
    )
    assert result.code.value == "UNKNOWN_COMMAND"
    assert result.route is route
    assert result.effects.is_empty
    assert result.pre_state_root == result.post_state_root


def test_context_then_state_then_command_failure_precedence():
    route, context, state, _ = _inputs(CASES[0])
    wrong_state = canonical_global_bytes_v2(CASES[0]["pre_state"] | {"schema": "wrong"})
    with pytest.raises(GlobalSettlementCodecErrorV2, match="invalid custody input encoding"):
        ingress.transition_asset_lane_custody_bytes_v2(route, b"{}", wrong_state, b"{")
    with pytest.raises(GlobalSettlementCodecErrorV2, match="custody lane state schema"):
        ingress.transition_asset_lane_custody_bytes_v2(route, context, wrong_state, b"{")
    with pytest.raises(GlobalSettlementCodecErrorV2, match="invalid JSON"):
        ingress.transition_asset_lane_custody_bytes_v2(route, context, state, b"{")


def test_economic_transition_faults_are_not_reclassified_as_decode_failures(monkeypatch):
    fault = ValueError("transition fault")

    def broken_transition(*_):
        raise fault

    monkeypatch.setattr(ingress, "transition_asset_lane_custody_v2", broken_transition)
    with pytest.raises(ValueError) as result:
        ingress.transition_asset_lane_custody_bytes_v2(*_inputs(CASES[0]))
    assert result.value is fault


@pytest.mark.parametrize("index", (1, 2, 3))
@pytest.mark.parametrize(
    "malformed",
    (
        b"{}",
        b'{"x":' + b"[" * 2048 + b"0" + b"]" * 2048 + b"}",
        b'{"x":' + b"9" * 5000 + b"}",
        b" " * 1_048_577,
        bytearray(b"{}"),
    ),
    ids=("wrong_fields", "deep_json", "huge_integer", "oversize", "mutable_bytes"),
)
def test_malformed_input_never_reaches_the_transition(monkeypatch, index, malformed):
    inputs = list(_inputs(CASES[0]))
    inputs[index] = malformed
    called = []

    def forbidden(*args):
        called.append(args)
        raise AssertionError("malformed bytes reached the economic transition")

    monkeypatch.setattr(ingress, "transition_asset_lane_custody_v2", forbidden)
    with pytest.raises(GlobalSettlementCodecErrorV2):
        ingress.transition_asset_lane_custody_bytes_v2(*inputs)
    assert called == []


@pytest.mark.parametrize("route", (AssetLaneRouteV2.COORDINATOR, "TRANSFER", None, 1))
def test_invalid_route_rejects_before_any_decode(monkeypatch, route):
    def forbidden(*_):
        raise AssertionError("invalid route reached a decoder")

    monkeypatch.setattr(ingress, "_decode_context", forbidden)
    with pytest.raises(GlobalSettlementCodecErrorV2, match="leaf route"):
        ingress.transition_asset_lane_custody_bytes_v2(route, b"{}", b"{}", b"{}")
