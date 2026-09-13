"""Focused evidence for the pure perps V2 wire, statement, and replay boundary."""

from __future__ import annotations

import json

import pytest

from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalRejectedV2,
    PerpsMarginOracleV2,
)
from src.core.perps_margin_receipt_v2 import (
    MAX_PERPS_MARGIN_FRAME_BYTES_V2,
    MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2,
    PERPS_MARGIN_FRAME_MAGIC_V2,
    PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2,
    encode_perps_margin_frame_v2,
    prepare_perps_margin_statement_v2,
    replay_perps_margin_frame_v2,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1 as CLOSE,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 as DEPOSIT,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1 as WITHDRAW,
)
from src.core.perps_margin_wire_v2 import (
    PerpsMarginRequestV2,
    decode_perps_margin_request_v2,
    decode_perps_margin_state_v2,
)
from tests.core.test_asset_lane_coordinator_v2 import _root
from tests.core.test_perps_margin_global_v2 import _command, _initial, _occurrence


def _request(inputs, kind, amount, account_nonce, outer_nonce, account="margin-a"):
    _, _, state = inputs
    command = _command(kind, amount, account_nonce, account)
    return PerpsMarginRequestV2(command, _occurrence(state, command, outer_nonce))


def _step(inputs, request):
    assets, margin, state = inputs
    statement = prepare_perps_margin_statement_v2(assets, margin, state, request)
    assert type(statement) is bytes
    frame = encode_perps_margin_frame_v2(assets, margin, state, request)
    replay = replay_perps_margin_frame_v2(frame)
    assert replay.statement == statement
    return (replay.result.post_assets, replay.result.post_margin, replay.result.post_state), replay


def _frame_parts(frame: bytes) -> tuple[bytes, ...]:
    assert frame.startswith(PERPS_MARGIN_FRAME_MAGIC_V2)
    cursor = len(PERPS_MARGIN_FRAME_MAGIC_V2)
    parts = []
    for _ in range(4):
        size = int.from_bytes(frame[cursor : cursor + 4], "little")
        cursor += 4
        parts.append(frame[cursor : cursor + size])
        cursor += size
    assert cursor == len(frame)
    return tuple(parts)


def _frame_from_parts(parts: tuple[bytes, ...]) -> bytes:
    return PERPS_MARGIN_FRAME_MAGIC_V2 + b"".join(
        len(part).to_bytes(4, "little") + part for part in parts
    )


def _request_frame(inputs, request):
    return encode_perps_margin_frame_v2(*inputs, request)


def test_connected_lifecycle_replays_deposit_drain_refill_and_close():
    inputs = _initial()
    history = (
        (DEPOSIT, 40, 1, 1),
        (WITHDRAW, 10, 2, 2),
        (WITHDRAW, 30, 3, 3),
        (DEPOSIT, 20, 4, 4),
        (WITHDRAW, 20, 5, 5),
        (CLOSE, 0, 6, 6),
    )
    replays = []
    for kind, amount, account_nonce, outer_nonce in history:
        inputs, replay = _step(
            inputs,
            _request(inputs, kind, amount, account_nonce, outer_nonce),
        )
        replays.append(replay)

    assert replays[2].result.post_margin.claim_id("margin-a") is None
    assert replays[3].result.post_margin.claim_id("margin-a") is not None
    assert inputs[1].economic_state.accounts[0].status.value == "CLOSED"
    assert len(inputs[2].terminal_obligations) == 2
    assert replays[0].result.statement_root != replays[3].result.statement_root


def test_statement_matches_retained_native_input_and_refinement_coordinates():
    inputs = _initial()
    request = _request(inputs, DEPOSIT, 1, 1, 1)
    statement = prepare_perps_margin_statement_v2(*inputs, request)
    assert type(statement) is bytes
    replay = replay_perps_margin_frame_v2(_request_frame(inputs, request))
    assert json.loads(statement) == {
        "schema": PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2,
        "input_root": replay.result.statement_root,
        "refinement_root": replay.result.refinement.refinement_root,
    }
    # Fixed outputs of the separately implemented Rust parity executable for
    # this one-atom deposit; the live producer cannot rewrite this oracle.
    assert json.loads(statement) == {
        "schema": "zenodex/perps-margin-global-statement/v2",
        "input_root": "0x385b48ccb7af76e0c3541ee8ad59891d6a6239728b49a4a91bb1cf2f7536a419",
        "refinement_root": "0x344718acf97d9b8d721dd081c07799eb7b3a86078aa2a3055d187059125ca3a2",
    }


def test_request_and_state_round_trip_preserve_v2_canonical_bytes_and_oracle():
    inputs = _initial()
    _, margin, state = inputs
    request = PerpsMarginRequestV2(
        _command(WITHDRAW, 1, 1),
        _occurrence(state, _command(WITHDRAW, 1, 1), 1),
        PerpsMarginOracleV2(_root("oracle-authority"), _root("oracle-occurrence"), 1),
    )
    state_raw = canonical_global_bytes_v2(margin)
    request_raw = canonical_global_bytes_v2(request)
    assert canonical_global_bytes_v2(decode_perps_margin_state_v2(state_raw)) == state_raw
    assert canonical_global_bytes_v2(decode_perps_margin_request_v2(request_raw)) == request_raw
    assert decode_perps_margin_request_v2(request_raw).oracle == request.oracle


def test_decoder_rejects_v1_state_and_request_schemas():
    _, margin, state = _initial()
    v1_state = canonical_global_bytes_v2(margin.economic_state)
    with pytest.raises(ValueError, match="schema|field set"):
        decode_perps_margin_state_v2(v1_state)

    command = _command(DEPOSIT, 1, 1)
    occurrence = _occurrence(state, command, 1)
    v1_request = canonical_global_bytes_v2(
        {
            "schema": "zenodex/perps-margin-module/v1",
            "command": command,
            "occurrence": occurrence,
            "oracle": None,
        }
    )
    with pytest.raises(ValueError, match="schema"):
        decode_perps_margin_request_v2(v1_request)


@pytest.mark.parametrize("mutate", ("unknown", "bool", "duplicate"))
def test_request_decoder_rejects_closed_field_and_scalar_mutants(mutate):
    inputs = _initial()
    request = _request(inputs, DEPOSIT, 1, 1, 1)
    raw = canonical_global_bytes_v2(request)
    if mutate == "unknown":
        payload = json.loads(raw)
        payload["extra"] = 1
        raw = canonical_global_bytes_v2(payload)
    elif mutate == "bool":
        payload = json.loads(raw)
        payload["command"]["amount_atoms"] = True
        raw = canonical_global_bytes_v2(payload)
    else:
        raw = raw.replace(
            b'"schema":"zenodex/perps-margin-request/v2"',
            b'"schema":"zenodex/perps-margin-request/v2","schema":"zenodex/perps-margin-request/v2"',
            1,
        )
    with pytest.raises(ValueError):
        decode_perps_margin_request_v2(raw)


@pytest.mark.parametrize(
    ("part_index", "mutation"),
    (
        (0, "asset"),
        (1, "margin"),
        (2, "height"),
        (2, "terminal"),
        (3, "command"),
        (3, "occurrence"),
    ),
)
def test_replay_rejects_command_body_occurrence_prestate_and_terminal_corruption(
    part_index, mutation
):
    initial = _initial()
    deposited, _ = _step(initial, _request(initial, DEPOSIT, 5, 1, 1))
    request = _request(deposited, WITHDRAW, 1, 2, 2)
    frame = _request_frame(deposited, request)
    parts = list(_frame_parts(frame))
    payload = json.loads(parts[part_index])
    if mutation == "asset":
        payload["transfer_state"]["balances"][0]["amount_atoms"] += 1
    elif mutation == "margin":
        payload["accounts"][0]["collateral_atoms"] += 1
    elif mutation == "height":
        payload["height"] += 1
    elif mutation == "terminal":
        payload["terminal_obligations"][0]["amount_atoms"] += 1
    elif mutation == "command":
        payload["command"]["amount_atoms"] += 1
    else:
        payload["occurrence"]["command_body_hash"] = _root("wrong-body")
    parts[part_index] = canonical_global_bytes_v2(payload)
    with pytest.raises(ValueError):
        replay_perps_margin_frame_v2(_frame_from_parts(tuple(parts)))


def test_rejected_economics_can_be_framed_but_cannot_replay_as_accepted():
    inputs = _initial()
    request = _request(inputs, DEPOSIT, 101, 1, 1)
    before = tuple(value.state_root for value in inputs)
    rejected = prepare_perps_margin_statement_v2(*inputs, request)
    assert type(rejected) is PerpsMarginGlobalRejectedV2
    assert rejected.effects.is_empty
    assert rejected.pre_state_root == rejected.post_state_root == inputs[2].state_root
    frame = encode_perps_margin_frame_v2(*inputs, request)
    assert frame
    with pytest.raises(ValueError, match="rejected"):
        replay_perps_margin_frame_v2(frame)
    assert tuple(value.state_root for value in inputs) == before


def test_frame_is_exactly_reencoded_and_rejects_truncation_trailing_or_lengths():
    inputs = _initial()
    request = _request(inputs, DEPOSIT, 1, 1, 1)
    frame = _request_frame(inputs, request)
    assert replay_perps_margin_frame_v2(frame).statement
    assert _frame_from_parts(_frame_parts(frame)) == frame
    with pytest.raises(ValueError):
        replay_perps_margin_frame_v2(frame[:-1])
    with pytest.raises(ValueError, match="trailing"):
        replay_perps_margin_frame_v2(frame + b"x")

    for length in (0, MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2 + 1):
        malformed = bytearray(frame)
        malformed[len(PERPS_MARGIN_FRAME_MAGIC_V2) : len(PERPS_MARGIN_FRAME_MAGIC_V2) + 4] = (
            length.to_bytes(4, "little")
        )
        with pytest.raises(ValueError):
            replay_perps_margin_frame_v2(bytes(malformed))
    with pytest.raises(ValueError):
        replay_perps_margin_frame_v2(b"x" * (MAX_PERPS_MARGIN_FRAME_BYTES_V2 + 1))
    with pytest.raises(ValueError):
        replay_perps_margin_frame_v2(bytearray(frame))


def test_request_and_frame_snapshot_caller_aliases():
    inputs = _initial()
    command = _command(DEPOSIT, 1, 1)
    request = PerpsMarginRequestV2(command, _occurrence(inputs[2], command, 1))
    request_raw = canonical_global_bytes_v2(request)
    frame = encode_perps_margin_frame_v2(*inputs, request)
    object.__setattr__(command, "amount_atoms", 99)
    assert canonical_global_bytes_v2(request) == request_raw
    assert encode_perps_margin_frame_v2(*inputs, request) == frame
