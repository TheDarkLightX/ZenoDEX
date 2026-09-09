"""Canonical boundary evidence for the frozen custody successor state."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, cast

import pytest

from src.core.asset_lane_custody_codec_v2 import (
    decode_asset_lane_custody_state_v2,
    encode_asset_lane_custody_state_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.global_settlement_abi_v2_codec import (
    MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2,
    GlobalSettlementCodecErrorV2,
)
from src.core.global_settlement_resource_limits_v2 import (
    MAX_ASSETS_PER_ASSET_STATE_V2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
)
from src.core.global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from tests.core.test_asset_lane_custody_v2 import custody_state

FIXTURE = Path(__file__).parents[1] / "data" / "asset_lane_custody_v2_golden.json"


def _golden_states() -> tuple[tuple[str, dict[str, Any]], ...]:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    states: list[tuple[str, dict[str, Any]]] = []
    for case in fixture["cases"]:
        states.append((f"{case['name']}:pre", case["pre_state"]))
        post = case["output"].get("post_state")
        if post is not None:
            states.append((f"{case['name']}:post", post))
    return tuple(states)


GOLDEN_STATES = _golden_states()


def _body(value: AssetLaneCustodyStateV2) -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(encode_asset_lane_custody_state_v2(value)))


@pytest.mark.parametrize(("name", "body"), GOLDEN_STATES, ids=[name for name, _ in GOLDEN_STATES])
def test_existing_custody_golden_states_round_trip_exact_canonical_bytes(
    name: str, body: dict[str, Any]
) -> None:
    raw = canonical_global_bytes_v2(body)
    decoded = decode_asset_lane_custody_state_v2(raw)

    assert json.loads(encode_asset_lane_custody_state_v2(decoded)) == body, name
    assert encode_asset_lane_custody_state_v2(decoded) == raw, name


@pytest.mark.parametrize(("accounts", "custody"), ((80, 20), (0, 0)))
def test_legal_nonzero_and_dormant_custody_states_are_exact_codec_fixed_points(
    accounts: int, custody: int
) -> None:
    state = custody_state(accounts, custody)
    raw = encode_asset_lane_custody_state_v2(state)

    assert decode_asset_lane_custody_state_v2(raw).to_canonical() == state.to_canonical()
    assert encode_asset_lane_custody_state_v2(decode_asset_lane_custody_state_v2(raw)) == raw


def test_encoder_rejects_nonexact_and_forged_custody_state_values() -> None:
    with pytest.raises(GlobalSettlementCodecErrorV2, match="exact V2"):
        encode_asset_lane_custody_state_v2(cast(AssetLaneCustodyStateV2, object()))

    forged = custody_state()
    object.__setattr__(forged, "_custody", (object(),))
    with pytest.raises(GlobalSettlementCodecErrorV2):
        encode_asset_lane_custody_state_v2(forged)


def test_decoded_state_does_not_retain_an_exposed_row_alias() -> None:
    raw = encode_asset_lane_custody_state_v2(custody_state())
    decoded = decode_asset_lane_custody_state_v2(raw)
    exposed = decoded.custody[0]
    object.__setattr__(exposed, "amount_atoms", MAX_ATOMS_V2)

    assert encode_asset_lane_custody_state_v2(decoded) == raw


@pytest.mark.parametrize(
    "raw",
    (
        b"not-json",
        b'{"schema":"zenodex/asset-lane-custody-state/v2","schema":"duplicate"}',
        b'{"schema":"\\ud800"}',
        b'{"schema":' + b"9" * 5_000 + b"}",
        b'{"schema":' + b"[" * 2_000 + b"0" + b"]" * 2_000 + b"}",
        b"{" + b" " * MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2 + b"}",
    ),
    ids=("malformed", "duplicate", "lone_surrogate", "huge_integer", "deep_json", "oversize"),
)
def test_untrusted_parser_failures_are_typed_codec_rejections(raw: bytes) -> None:
    with pytest.raises(GlobalSettlementCodecErrorV2):
        decode_asset_lane_custody_state_v2(raw)


def test_decoder_rejects_closed_field_schema_and_exact_numeric_type_mutants() -> None:
    body = _body(custody_state())
    unknown = copy.deepcopy(body)
    unknown["unknown"] = 1
    missing = copy.deepcopy(body)
    del missing["custody"]
    nested_unknown = copy.deepcopy(body)
    nested_unknown["custody"][0]["unknown"] = 1
    boolean_amount = copy.deepcopy(body)
    boolean_amount["custody"][0]["amount_atoms"] = True
    text_amount = copy.deepcopy(body)
    text_amount["custody"][0]["amount_atoms"] = "20"
    negative_amount = copy.deepcopy(body)
    negative_amount["custody"][0]["amount_atoms"] = -1
    overflow_amount = copy.deepcopy(body)
    overflow_amount["custody"][0]["amount_atoms"] = MAX_ATOMS_V2 + 1

    for mutant in (
        unknown,
        missing,
        nested_unknown,
        boolean_amount,
        text_amount,
        negative_amount,
        overflow_amount,
    ):
        with pytest.raises(GlobalSettlementCodecErrorV2):
            decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(mutant))

    historical = copy.deepcopy(body)
    historical["schema"] = "zenodex/asset-lane-custody-state/v1"
    with pytest.raises(GlobalSettlementCodecErrorV2, match="custody lane state schema"):
        decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(historical))


def test_decoder_rejects_reordered_custody_rows_and_preconstructs_row_ceilings() -> None:
    base = custody_state()
    split = base.to_canonical() | {
        "custody": (
            EconomicAmountV2("vault-a", "USD", "escrow", 10),
            EconomicAmountV2("vault-b", "USD", "escrow", 10),
        )
    }
    ordered = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(split))
    body = _body(ordered)
    reordered = copy.deepcopy(body)
    reordered["custody"].reverse()
    too_many_policies = copy.deepcopy(body)
    too_many_policies["managed_policies"] = [body["managed_policies"][0]] * (
        MAX_ASSETS_PER_ASSET_STATE_V2 + 1
    )
    too_many_transfer_policies = copy.deepcopy(body)
    too_many_transfer_policies["transfer_state"]["policies"] = [
        body["transfer_state"]["policies"][0]
    ] * (MAX_ASSETS_PER_ASSET_STATE_V2 + 1)
    too_many_transfer_balances = copy.deepcopy(body)
    too_many_transfer_balances["transfer_state"]["balances"] = [
        body["transfer_state"]["balances"][0]
    ] * (MAX_BALANCE_ROWS_PER_ASSET_STATE_V2 + 1)
    too_many_transfer_supplies = copy.deepcopy(body)
    too_many_transfer_supplies["transfer_state"]["supplies"] = [
        body["transfer_state"]["supplies"][0]
    ] * (MAX_ASSETS_PER_ASSET_STATE_V2 + 1)
    too_many_origin_assets = copy.deepcopy(body)
    too_many_origin_assets["origin_registry"]["assets"] = [body["origin_registry"]["assets"][0]] * (
        MAX_ASSETS_PER_ASSET_STATE_V2 + 1
    )
    too_many_custody_rows = copy.deepcopy(body)
    too_many_custody_rows["custody"] = [body["custody"][0]] * (
        MAX_BALANCE_ROWS_PER_ASSET_STATE_V2 + 1
    )

    with pytest.raises(GlobalSettlementCodecErrorV2):
        decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(reordered))
    for mutant, message in (
        (too_many_policies, "managed policies.*ceiling"),
        (too_many_transfer_policies, "transfer policies.*ceiling"),
        (too_many_transfer_balances, "transfer balances.*ceiling"),
        (too_many_transfer_supplies, "transfer supplies.*ceiling"),
        (too_many_origin_assets, "origin assets.*ceiling"),
        (too_many_custody_rows, "custody lane rows.*ceiling"),
    ):
        with pytest.raises(GlobalSettlementCodecErrorV2, match=message):
            decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(mutant))


def test_decoder_rejects_noncanonical_object_key_order() -> None:
    body = _body(custody_state())
    noncanonical = json.dumps(dict(reversed(tuple(body.items()))), separators=(",", ":")).encode(
        "utf-8"
    )

    assert noncanonical != canonical_global_bytes_v2(body)
    with pytest.raises(GlobalSettlementCodecErrorV2, match="not canonical"):
        decode_asset_lane_custody_state_v2(noncanonical)
