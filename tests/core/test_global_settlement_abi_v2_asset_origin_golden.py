from __future__ import annotations

import copy
import hashlib
import json
from dataclasses import replace
from typing import cast

import pytest

from src.core.asset_origin_registry_codec_v2 import (
    decode_asset_origin_registration_command_v2,
    decode_asset_origin_registration_context_v2,
    decode_asset_origin_registry_state_v2,
    encode_asset_origin_registration_command_v2,
    encode_asset_origin_registration_context_v2,
    encode_asset_origin_registry_state_v2,
)
from src.core.asset_origin_registry_types_v2 import (
    MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2,
    AssetOriginRegistrationAcceptedV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistrationRejectedV2,
)
from src.core.asset_origin_registry_v2 import transition_asset_origin_registration_v2
from src.core.global_settlement_abi_v2_codec import GlobalSettlementCodecErrorV2
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from tools.render_global_settlement_abi_v2_asset_origin_golden import (
    FIXTURE_PATH_V2,
    build_vectors_v2,
    render_vectors_v2,
)


def _mapping(value: object) -> dict[str, object]:
    return cast(dict[str, object], value)


def _vector_bytes(vector: object) -> bytes:
    fields = _mapping(vector)
    raw = canonical_global_bytes_v2(fields["canonical"])
    assert hashlib.sha256(raw).hexdigest() == fields["canonical_bytes_sha256"]
    return raw


def _fixture() -> dict[str, object]:
    return _mapping(json.loads(FIXTURE_PATH_V2.read_text(encoding="utf-8")))


def test_committed_asset_origin_fixture_matches_typed_renderer() -> None:
    fixture_text = FIXTURE_PATH_V2.read_text(encoding="utf-8")

    assert fixture_text == render_vectors_v2()
    assert json.loads(fixture_text) == build_vectors_v2()


def test_fixture_scope_reject_registry_and_nonclaims_are_exact() -> None:
    fixture = _fixture()

    assert fixture["authority"] == "NONE"
    assert fixture["profile_authentication"] == "SHADOW"
    assert fixture["reject_codes"] == [code.value for code in AssetOriginRegistrationRejectCodeV2]
    assert len(_mapping(fixture["rejections"])) == 13
    assert fixture["nonclaims"] == [
        "no RISC0 circuit or receipt",
        "no runtime mount or migration",
        "no UI, release, settlement, or production authority",
    ]


def test_strict_codecs_round_trip_the_accepted_transition() -> None:
    accepted = _mapping(_fixture()["accepted"])
    vectors = _mapping(accepted["vectors"])
    command = decode_asset_origin_registration_command_v2(_vector_bytes(vectors["command"]))
    context = decode_asset_origin_registration_context_v2(_vector_bytes(vectors["context"]))
    pre_state = decode_asset_origin_registry_state_v2(_vector_bytes(vectors["pre_state"]))

    result = transition_asset_origin_registration_v2(context, pre_state, command)

    assert isinstance(result, AssetOriginRegistrationAcceptedV2)
    assert encode_asset_origin_registration_command_v2(command) == _vector_bytes(vectors["command"])
    assert encode_asset_origin_registration_context_v2(context) == _vector_bytes(vectors["context"])
    assert encode_asset_origin_registry_state_v2(pre_state) == _vector_bytes(vectors["pre_state"])
    assert canonical_global_bytes_v2(result.post_state) == _vector_bytes(vectors["post_state"])
    assert canonical_global_bytes_v2(result.effects) == _vector_bytes(vectors["effect_plan"])
    assert canonical_global_bytes_v2(result.module_journal) == _vector_bytes(
        vectors["module_journal"]
    )
    assert result.module_journal.receipt_root == accepted["receipt_root"]
    assert result.production_authority == "NONE"


def test_all_adjacent_precedence_vectors_reject_as_exact_noops() -> None:
    rejections = _mapping(_fixture()["rejections"])

    for case_value in rejections.values():
        case = _mapping(case_value)
        context = decode_asset_origin_registration_context_v2(_vector_bytes(case["context"]))
        state = decode_asset_origin_registry_state_v2(_vector_bytes(case["pre_state"]))
        command = decode_asset_origin_registration_command_v2(_vector_bytes(case["command"]))

        result = transition_asset_origin_registration_v2(context, state, command)

        assert isinstance(result, AssetOriginRegistrationRejectedV2)
        assert result.code.value == case["expected_code"]
        assert result.pre_state_root == result.post_state_root == state.state_root
        assert result.effects.is_empty


def test_python_accepts_the_final_registry_slot_from_the_shared_capacity_vector() -> None:
    capacity = _mapping(_mapping(_fixture()["rejections"])["13_registry_capacity_exceeded"])
    context = decode_asset_origin_registration_context_v2(_vector_bytes(capacity["context"]))
    full_state = decode_asset_origin_registry_state_v2(_vector_bytes(capacity["pre_state"]))
    command = decode_asset_origin_registration_command_v2(_vector_bytes(capacity["command"]))
    state = replace(full_state, assets=full_state.assets[:-1])
    pre_state_root = state.state_root

    result = transition_asset_origin_registration_v2(context, state, command)

    assert isinstance(result, AssetOriginRegistrationAcceptedV2)
    assert len(state.assets) == MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2 - 1
    assert state.state_root == pre_state_root
    assert len(result.post_state.assets) == MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2
    assert result.post_state.record_for(command.asset) is not None
    assert result.effects.rows == ()
    assert result.effects.asset_conservation == ()
    assert result.effects.fee_conservation == ()
    assert len(result.effects.lane_writes) == 1
    assert result.effects.lane_writes[0].pre_root == pre_state_root
    assert result.effects.lane_writes[0].post_root == result.post_state.state_root
    assert result.effects.external_outbox_enqueue == ()
    assert result.production_authority == "NONE"


def test_command_decoder_rejects_field_shape_scalar_and_canonical_mutants() -> None:
    vectors = _mapping(_mapping(_fixture()["accepted"])["vectors"])
    canonical = _mapping(_mapping(vectors["command"])["canonical"])
    unknown = copy.deepcopy(canonical)
    unknown["unknown"] = True
    missing = copy.deepcopy(canonical)
    del missing["issue_policy_root"]
    bool_decimal = copy.deepcopy(canonical)
    bool_decimal["decimals"] = True
    numeric_string = copy.deepcopy(canonical)
    numeric_string["decimals"] = "8"
    wrong_enum = copy.deepcopy(canonical)
    wrong_enum["origin_kind"] = "tau_originated"
    uppercase_root = copy.deepcopy(canonical)
    uppercase_root["origin_root"] = cast(str, uppercase_root["origin_root"]).upper()

    for mutant in (unknown, missing, bool_decimal, numeric_string, wrong_enum, uppercase_root):
        with pytest.raises(GlobalSettlementCodecErrorV2):
            decode_asset_origin_registration_command_v2(canonical_global_bytes_v2(mutant))

    raw = _vector_bytes(vectors["command"])
    with pytest.raises(GlobalSettlementCodecErrorV2, match="duplicate field"):
        decode_asset_origin_registration_command_v2(b'{"asset":"USD",' + raw[1:])
    with pytest.raises(GlobalSettlementCodecErrorV2, match="not canonical"):
        decode_asset_origin_registration_command_v2(raw + b"\n")
    reordered = dict(reversed(list(canonical.items())))
    noncanonical = json.dumps(reordered, separators=(",", ":")).encode()
    with pytest.raises(GlobalSettlementCodecErrorV2, match="not canonical"):
        decode_asset_origin_registration_command_v2(noncanonical)


def test_state_and_context_decoders_reject_closed_shape_and_order_mutants() -> None:
    vectors = _mapping(_mapping(_fixture()["accepted"])["vectors"])
    state = _mapping(_mapping(vectors["post_state"])["canonical"])
    reversed_rows = copy.deepcopy(state)
    cast(list[object], reversed_rows["assets"]).reverse()
    old_schema = copy.deepcopy(state)
    old_schema["schema"] = "zenodex/asset-origin-registry/v1"
    context = _mapping(_mapping(vectors["context"])["canonical"])
    missing_occurrence = copy.deepcopy(context)
    del missing_occurrence["occurrence"]

    for mutant in (reversed_rows, old_schema):
        with pytest.raises(GlobalSettlementCodecErrorV2):
            decode_asset_origin_registry_state_v2(canonical_global_bytes_v2(mutant))
    oversized = copy.deepcopy(state)
    valid_row = cast(list[object], state["assets"])[0]
    oversized_rows = [
        copy.deepcopy(valid_row)
        for _ in range(MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2 + 1)
    ]
    _mapping(oversized_rows[0])["asset"] = ""
    oversized["assets"] = oversized_rows
    with pytest.raises(GlobalSettlementCodecErrorV2, match="256-item ceiling"):
        decode_asset_origin_registry_state_v2(canonical_global_bytes_v2(oversized))
    with pytest.raises(GlobalSettlementCodecErrorV2):
        decode_asset_origin_registration_context_v2(canonical_global_bytes_v2(missing_occurrence))
    nullable_occurrence = copy.deepcopy(context)
    nullable_occurrence["occurrence"] = None
    assert (
        decode_asset_origin_registration_context_v2(
            canonical_global_bytes_v2(nullable_occurrence)
        ).occurrence
        is None
    )


def test_command_decoder_preserves_u64_and_token_boundaries() -> None:
    vectors = _mapping(_mapping(_fixture()["accepted"])["vectors"])
    canonical = _mapping(_mapping(vectors["command"])["canonical"])
    max_u64 = copy.deepcopy(canonical)
    max_u64["decimals"] = (1 << 64) - 1
    over_u64 = copy.deepcopy(canonical)
    over_u64["decimals"] = 1 << 64
    max_token = copy.deepcopy(canonical)
    max_token["asset"] = "x" * 160
    over_token = copy.deepcopy(canonical)
    over_token["asset"] = "x" * 161

    assert (
        decode_asset_origin_registration_command_v2(canonical_global_bytes_v2(max_u64)).decimals
        == (1 << 64) - 1
    )
    assert (
        len(decode_asset_origin_registration_command_v2(canonical_global_bytes_v2(max_token)).asset)
        == 160
    )
    for mutant in (over_u64, over_token):
        with pytest.raises(GlobalSettlementCodecErrorV2):
            decode_asset_origin_registration_command_v2(canonical_global_bytes_v2(mutant))
