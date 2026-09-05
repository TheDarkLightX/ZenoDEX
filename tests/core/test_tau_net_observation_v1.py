"""Source-derived protocol vectors; these observations confer no economic authority."""

from __future__ import annotations

import dataclasses
import itertools
import json

import pytest

from src.core import tau_net_observation_v1 as core

TX = "a" * 64
BLOCK = "b" * 64
RULES = core.TauReadRequestV1(core.TauReadCommandV1.GET_TAU_STATE)
ACCOUNT = core.TauReadRequestV1(core.TauReadCommandV1.GET_ACCOUNT_STATE, "alice")
STATUS = core.TauReadRequestV1(core.TauReadCommandV1.GET_TX_STATUS, TX)
INVALID = core.TauObservationRejectCodeV1.INVALID_RESPONSE
RESOURCE = core.TauObservationRejectCodeV1.RESOURCE_LIMIT
MISMATCH = core.TauObservationRejectCodeV1.SUBJECT_MISMATCH


def wire(request: core.TauReadRequestV1, data: object) -> bytes:
    return json.dumps({"status": "ok", "command": request.command.value, "data": data}).encode()


def row(number: int, direction: str, amount: int, fee: int = 0) -> dict[str, object]:
    return {
        "hash": f"{number:064x}",
        "direction": direction,
        "amount": str(amount),
        "fee": str(fee),
        "status": "queued",
        "sequence_number": None,
        "tx_type": "user_tx",
        "received_at": "",
        "expires_at": "",
    }


def account(
    *,
    chain: int = 100,
    outgoing: int = 0,
    incoming: int = 0,
    fees: int = 0,
    available: int = 100,
    rows: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    return {
        "address": "alice",
        "chain_balance": str(chain),
        "pending_outgoing": str(outgoing),
        "pending_incoming": str(incoming),
        "pending_fees": str(fees),
        "available_balance": str(available),
        "pending_txs": [] if rows is None else rows,
    }


def queued() -> dict[str, object]:
    return {
        "tx_hash": TX,
        "status": "queued",
        "sender": None,
        "sequence_number": None,
        "received_at": "",
        "fee_limit": 0,
        "estimated_fee": 0,
        "expires_at": "",
    }


def confirmed() -> dict[str, object]:
    return {
        "tx_hash": TX,
        "status": "confirmed",
        "block_hash": BLOCK,
        "block_number": 0,
        "confirmations": 1,
    }


def decode(request: core.TauReadRequestV1, data: object) -> object:
    return core.decode_tau_read_response_v1(request, wire(request, data))


@pytest.mark.parametrize("command", ["getblocks", "sendtx", "checktx", "gettaustate", None, True])
def test_only_closed_read_command_enum_is_encodable(command: object) -> None:
    assert core.make_tau_read_request_v1(command) == core.TauObservationRejectV1(
        core.TauObservationRejectCodeV1.UNSUPPORTED_COMMAND
    )


def test_read_capability_registry_requires_review_for_every_new_command() -> None:
    assert {command.value for command in core.TauReadCommandV1} == {
        "gettaustate",
        "getaccountstate",
        "gettxstatus",
    }


@pytest.mark.parametrize(
    "argument",
    ["", "alice bob", "alice\ngetblocks", "alice\rgetblocks", "a\x00b", "é", "a" * 257, True],
)
def test_account_argument_cannot_create_another_command(argument: object) -> None:
    assert core.make_tau_read_request_v1(core.TauReadCommandV1.GET_ACCOUNT_STATE, argument) == (
        core.TauObservationRejectV1(core.TauObservationRejectCodeV1.INVALID_REQUEST)
    )


def test_request_bounds_and_canonical_digest() -> None:
    for size in (1, 256):
        made = core.make_tau_read_request_v1(core.TauReadCommandV1.GET_ACCOUNT_STATE, "a" * size)
        assert isinstance(made, core.TauReadRequestV1)
        assert core.encode_tau_read_request_v1(made) == b"getaccountstate " + b"a" * size
    supplied = core.TauReadRequestV1(core.TauReadCommandV1.GET_TX_STATUS, TX.upper())
    assert core.encode_tau_read_request_v1(supplied) == b"gettxstatus " + TX.encode()
    result = decode(supplied, {"tx_hash": TX, "status": "unknown"})
    assert isinstance(result, core.TauReadObservationV1)
    assert result.request == STATUS
    assert result.request is not supplied
    assert core.encode_tau_read_request_v1(RULES) == b"gettaustate"
    for size in (0, 63, 65):
        assert core.make_tau_read_request_v1(core.TauReadCommandV1.GET_TX_STATUS, "a" * size) == (
            core.TauObservationRejectV1(core.TauObservationRejectCodeV1.INVALID_REQUEST)
        )


def test_uninitialized_request_is_a_typed_rejection() -> None:
    forged = object.__new__(core.TauReadRequestV1)
    expected = core.TauObservationRejectV1(core.TauObservationRejectCodeV1.INVALID_REQUEST)
    assert core.encode_tau_read_request_v1(forged) == expected
    assert core.decode_tau_read_response_v1(forged, b"{}") == expected


@pytest.mark.parametrize(
    "raw",
    [
        b"ok version=1 env=testnet node=tau-node",
        b"ok version=2 env=testnet node=other",
        b"ok version=2 env=testnet node=tau-node\r\n",
        b"success",
        b"",
    ],
)
def test_handshake_requires_exact_unframed_version_two(raw: bytes) -> None:
    assert core.decode_tau_hello_v1(raw) == core.TauObservationRejectV1(
        core.TauObservationRejectCodeV1.HANDSHAKE_MISMATCH
    )


def test_handshake_and_rule_text_positive_bounds() -> None:
    assert core.decode_tau_hello_v1(
        b"ok version=2 env=testnet node=tau-node"
    ) == core.TauHelloObservationV1("testnet")
    assert core.decode_tau_hello_v1(b"x" * 129) == core.TauObservationRejectV1(RESOURCE)
    assert core.decode_tau_hello_v1(bytearray(b"hello")) == core.TauObservationRejectV1(
        core.TauObservationRejectCodeV1.INVALID_FRAME
    )
    for text in ("", "o1[t] = i1[t].", "é" * 32768):
        result = decode(RULES, {"rules_state": text})
        assert isinstance(result, core.TauReadObservationV1)
        assert result.body == core.TauRulesObservationV1(text)
    assert decode(RULES, {"rules_state": "é" * 32769}) == core.TauObservationRejectV1(RESOURCE)


@pytest.mark.parametrize(
    "raw",
    [
        b"",
        b"success rules",
        b"[]",
        b"null",
        b"\xff",
        b'{"status":"ok",',
        b'{"status":"ok","command":"gettaustate","data":{"rules_state":"\\ud800"}}',
    ],
)
def test_malformed_json_returns_typed_invalid_response(raw: bytes) -> None:
    assert core.decode_tau_read_response_v1(RULES, raw) == core.TauObservationRejectV1(INVALID)


@pytest.mark.parametrize("extra", [b'"status":"error",', b'"command":"sendtx",'])
def test_duplicate_envelope_keys_cannot_be_overwritten(extra: bytes) -> None:
    raw = b"{" + extra + b'"status":"ok","command":"gettaustate","data":{"rules_state":""}}'
    assert core.decode_tau_read_response_v1(RULES, raw) == core.TauObservationRejectV1(INVALID)


def test_exact_envelope_and_owned_opaque_remote_error() -> None:
    wrong = wire(ACCOUNT, account())
    assert core.decode_tau_read_response_v1(RULES, wrong) == core.TauObservationRejectV1(MISMATCH)
    wrong_context = wire(RULES, {"rules_state": ""}).replace(b"gettaustate", b"getaccountstate")
    assert core.decode_tau_read_response_v1(RULES, wrong_context) == core.TauObservationRejectV1(
        MISMATCH
    )
    extra = b'{"status":"ok","command":"gettaustate","data":{"rules_state":""},"verified":true}'
    assert core.decode_tau_read_response_v1(RULES, extra) == core.TauObservationRejectV1(INVALID)
    raw = b'{"status":"error","command":"gettaustate","error":{"code":"INTERNAL_ERROR","message":"down","details":{"b":[1,null,true],"a":"x"}}}'
    result = core.decode_tau_read_response_v1(RULES, raw)
    assert isinstance(result, core.TauReadObservationV1)
    assert result.body == core.TauRemoteErrorObservationV1(
        "INTERNAL_ERROR", "down", b'{"a":"x","b":[1,null,true]}'
    )
    assert result.raw_response_bytes == raw
    duplicate = raw.replace(b'"a":"x"', b'"a":"x","a":"y"')
    assert core.decode_tau_read_response_v1(RULES, duplicate) == core.TauObservationRejectV1(
        INVALID
    )


def test_opaque_error_details_cannot_expand_past_the_response_byte_ceiling() -> None:
    details = {str(i): "é" * 32768 for i in range(15)}
    raw = json.dumps(
        {
            "status": "error",
            "command": "gettaustate",
            "error": {
                "code": "E",
                "message": "",
                "details": details,
            },
        },
        ensure_ascii=False,
    ).encode("utf-8")
    assert len(raw) < core.MAX_TAU_OBSERVATION_BYTES_V1
    result = core.decode_tau_read_response_v1(RULES, raw)
    assert isinstance(result, core.TauReadObservationV1)
    assert isinstance(result.body, core.TauRemoteErrorObservationV1)
    assert result.body.details_json is not None
    assert len(result.body.details_json) < core.MAX_TAU_OBSERVATION_BYTES_V1
    assert json.loads(result.body.details_json) == details


def test_json_field_order_and_whitespace_preserve_owned_semantics() -> None:
    original = {"status": "ok", "command": "getaccountstate", "data": account()}
    expected = decode(ACCOUNT, account())
    assert isinstance(expected, core.TauReadObservationV1)
    for order in itertools.permutations(original):
        shuffled = {key: original[key] for key in order}
        for indent in (None, 2):
            raw = json.dumps(shuffled, indent=indent).encode()
            result = core.decode_tau_read_response_v1(ACCOUNT, raw)
            assert isinstance(result, core.TauReadObservationV1)
            assert result.body == expected.body
            assert result.raw_response_bytes == raw


def test_resource_bounds_precede_unbounded_observation_construction() -> None:
    assert core.decode_tau_read_response_v1(
        RULES, b" " * (core.MAX_TAU_OBSERVATION_BYTES_V1 + 1)
    ) == core.TauObservationRejectV1(RESOURCE)
    prefix = b'{"status":"error","command":"gettaustate","error":{"code":"E","message":"","details":{"x":'
    deeply_nested = prefix + b"[" * 1000 + b"0" + b"]" * 1000 + b"}}}"
    assert core.decode_tau_read_response_v1(RULES, deeply_nested) == core.TauObservationRejectV1(
        RESOURCE
    )
    many_nodes = prefix + b"[" + b"0," * 16384 + b"0]}}}"
    assert core.decode_tau_read_response_v1(RULES, many_nodes) == core.TauObservationRejectV1(
        RESOURCE
    )
    for raw in (bytearray(b"{}"), "{}", None):
        assert core.decode_tau_read_response_v1(RULES, raw) == core.TauObservationRejectV1(
            core.TauObservationRejectCodeV1.INVALID_FRAME
        )


def test_account_fixture_separates_incoming_from_spendable_and_owns_rows() -> None:
    # Upstream self row serializes amount_out=30, omitting amount_in=7.
    rows = [row(1, "outgoing", 20, 2), row(2, "incoming", 90), row(3, "self", 30, 3)]
    data = account(outgoing=50, incoming=97, fees=5, available=45, rows=rows)
    result = decode(ACCOUNT, data)
    assert isinstance(result, core.TauReadObservationV1)
    assert isinstance(result.body, core.TauAccountObservationV1)
    assert result.body.pending_incoming_atoms == 97
    assert result.body.available_balance_atoms == 45
    assert result.body.pending_txs[2].amount_atoms == 30
    rows[0]["amount"] = "999"
    assert result.body.pending_txs[0].amount_atoms == 20
    with pytest.raises(dataclasses.FrozenInstanceError):
        result.body.pending_txs[0].amount_atoms = 999  # type: ignore[misc]
    data["available_balance"] = "142"
    assert decode(ACCOUNT, data) == core.TauObservationRejectV1(INVALID)


def test_pending_aggregate_guards_reject_independent_one_atom_misstatements() -> None:
    for field in ("pending_outgoing", "pending_incoming", "pending_fees", "available_balance"):
        data = account(
            outgoing=10,
            incoming=20,
            fees=1,
            available=89,
            rows=[row(1, "outgoing", 10, 1), row(2, "incoming", 20)],
        )
        data[field] = str(int(str(data[field])) + 1)
        assert decode(ACCOUNT, data) == core.TauObservationRejectV1(INVALID), field
    mismatch = account()
    mismatch["address"] = "bob"
    assert decode(ACCOUNT, mismatch) == core.TauObservationRejectV1(MISMATCH)


def test_pending_self_direction_requires_positive_omitted_inflow() -> None:
    data = account(
        outgoing=3,
        incoming=7,
        available=97,
        rows=[row(1, "self", 1), row(2, "self", 2), row(3, "incoming", 5)],
    )
    assert isinstance(decode(ACCOUNT, data), core.TauReadObservationV1)
    for incoming in (5, 6):
        data["pending_incoming"] = str(incoming)
        assert decode(ACCOUNT, data) == core.TauObservationRejectV1(INVALID)
    for direction in ("self", "outgoing"):
        zero = account(incoming=1 if direction == "self" else 0, rows=[row(1, direction, 0)])
        assert decode(ACCOUNT, zero) == core.TauObservationRejectV1(INVALID)


def test_pending_balance_relation_differential_small_domain() -> None:
    # Independent exhaustive reservation oracle, including over-reserved chain state.
    for balance, spend, incoming, fee in itertools.product(range(3), repeat=4):
        reserved = spend + fee
        expected = 0 if reserved > balance else balance - reserved
        data = account(
            chain=balance,
            outgoing=spend,
            incoming=incoming,
            fees=fee,
            available=expected,
            rows=[
                row(1, "outgoing" if spend else "incoming", spend, fee),
                row(2, "incoming", incoming),
            ],
        )
        result = decode(ACCOUNT, data)
        assert isinstance(result, core.TauReadObservationV1), (balance, spend, incoming, fee)
        assert isinstance(result.body, core.TauAccountObservationV1)
        assert result.body.available_balance_atoms == expected


@pytest.mark.parametrize("bad", [0, True, -1, "-1", "01", "1.0", "+1", " 1", "١"])
def test_account_amounts_are_canonical_unsigned_decimal_strings(bad: object) -> None:
    data = account()
    data["chain_balance"] = bad
    assert decode(ACCOUNT, data) == core.TauObservationRejectV1(INVALID)


def test_integer_and_row_count_maximum_neighbors() -> None:
    maximum = core.MAX_TAU_OBSERVATION_INTEGER_V1
    assert isinstance(
        decode(ACCOUNT, account(chain=maximum, available=maximum)), core.TauReadObservationV1
    )
    assert decode(
        ACCOUNT, account(chain=maximum + 1, available=maximum + 1)
    ) == core.TauObservationRejectV1(RESOURCE)
    for count in (0, 1, 256, 257):
        result = decode(
            ACCOUNT, account(incoming=count, rows=[row(i, "incoming", 1) for i in range(count)])
        )
        if count <= 256:
            assert isinstance(result, core.TauReadObservationV1)
        else:
            assert result == core.TauObservationRejectV1(RESOURCE)
    assert decode(
        ACCOUNT, account(incoming=2, rows=[row(1, "incoming", 1)] * 2)
    ) == core.TauObservationRejectV1(INVALID)


def test_status_lifecycle_observes_reorg_and_forgetting_without_sticky_finality() -> None:
    history = [
        ({"tx_hash": TX, "status": "unknown"}, core.TauTxUnknownObservationV1),
        (queued(), core.TauTxMempoolObservationV1),
        (confirmed(), core.TauTxConfirmedObservationV1),
        (queued(), core.TauTxMempoolObservationV1),
        ({"tx_hash": TX, "status": "evicted", "dropped_at": ""}, core.TauTxDroppedObservationV1),
        ({"tx_hash": TX, "status": "unknown"}, core.TauTxUnknownObservationV1),
    ]
    for data, expected_type in history:
        result = decode(STATUS, data)
        assert isinstance(result, core.TauReadObservationV1)
        assert isinstance(result.body, expected_type)
        assert result.request == STATUS


def test_expired_status_retains_mempool_and_dropped_provenance() -> None:
    data = queued()
    data["status"] = "expired"
    mempool = decode(STATUS, data)
    assert isinstance(mempool, core.TauReadObservationV1)
    assert isinstance(mempool.body, core.TauTxMempoolObservationV1)
    assert mempool.body.status is core.TauMempoolStatusV1.EXPIRED
    dropped = decode(STATUS, {"tx_hash": TX, "status": "expired", "dropped_at": ""})
    assert isinstance(dropped, core.TauReadObservationV1)
    assert isinstance(dropped.body, core.TauTxDroppedObservationV1)
    data["dropped_at"] = ""
    assert decode(STATUS, data) == core.TauObservationRejectV1(INVALID)


@pytest.mark.parametrize("bad", [True, -1, 0.0, "0", None])
def test_status_numeric_fields_reject_json_type_confusion(bad: object) -> None:
    data = confirmed()
    data["block_number"] = bad
    assert decode(STATUS, data) == core.TauObservationRejectV1(INVALID)


@pytest.mark.parametrize("number", [b"-0", b"NaN", b"Infinity", b"1e2", b"1.0"])
def test_noncanonical_json_numbers_cannot_be_normalized_into_valid_counts(number: bytes) -> None:
    raw = wire(STATUS, confirmed()).replace(b'"block_number": 0', b'"block_number": ' + number)
    assert core.decode_tau_read_response_v1(STATUS, raw) == core.TauObservationRejectV1(INVALID)


def test_confirmation_and_subject_guards() -> None:
    data = confirmed()
    data["confirmations"] = 0
    assert decode(STATUS, data) == core.TauObservationRejectV1(INVALID)
    data = confirmed()
    data["tx_hash"] = "c" * 64
    assert decode(STATUS, data) == core.TauObservationRejectV1(MISMATCH)
    data = confirmed()
    data["block_hash"] = BLOCK.upper()
    assert decode(STATUS, data) == core.TauObservationRejectV1(INVALID)
    data = confirmed()
    data["block_number"] = core.MAX_TAU_OBSERVATION_INTEGER_V1 + 1
    assert decode(STATUS, data) == core.TauObservationRejectV1(RESOURCE)


def test_closed_data_and_status_variants_reject_each_missing_or_extra_field() -> None:
    for request, valid in (
        (RULES, {"rules_state": ""}),
        (ACCOUNT, account()),
        (STATUS, confirmed()),
        (STATUS, queued()),
    ):
        assert isinstance(decode(request, valid), core.TauReadObservationV1)
        for key in valid:
            changed = dict(valid)
            del changed[key]
            assert isinstance(decode(request, changed), core.TauObservationRejectV1), key
        changed = dict(valid)
        changed["proof_verified"] = True
        assert decode(request, changed) == core.TauObservationRejectV1(INVALID)
    assert decode(STATUS, {"tx_hash": TX, "status": "finalized"}) == core.TauObservationRejectV1(
        INVALID
    )
