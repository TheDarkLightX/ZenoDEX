"""Bounded, unauthenticated observations of Tau Testnet's JSON read protocol.

The schema follows upstream 0b038824c8583a1a902ef54369d3d0ecf3384cf5.
Decoding grants no state, policy, inclusion, finality, or publication authority.
Limits below are local observer resource ceilings, not Tau consensus parameters.
Opaque error details retain JSON bytes; they are never interpreted as evidence.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

MAX_TAU_OBSERVATION_BYTES_V1: Final = 1_048_576
MAX_TAU_HELLO_BYTES_V1: Final = 128
MAX_TAU_OBSERVATION_ROWS_V1: Final = 256
MAX_TAU_OBSERVATION_TEXT_BYTES_V1: Final = 65_536
MAX_TAU_OBSERVATION_INTEGER_V1: Final = (1 << 256) - 1


class TauReadCommandV1(Enum):
    GET_TAU_STATE = "gettaustate"
    GET_ACCOUNT_STATE = "getaccountstate"
    GET_TX_STATUS = "gettxstatus"


class TauObservationRejectCodeV1(Enum):
    INVALID_REQUEST = "INVALID_REQUEST"
    UNSUPPORTED_COMMAND = "UNSUPPORTED_COMMAND"
    INVALID_FRAME = "INVALID_FRAME"
    RESOURCE_LIMIT = "RESOURCE_LIMIT"
    INVALID_RESPONSE = "INVALID_RESPONSE"
    SUBJECT_MISMATCH = "SUBJECT_MISMATCH"
    HANDSHAKE_MISMATCH = "HANDSHAKE_MISMATCH"
    UNAVAILABLE = "UNAVAILABLE"
    TIMEOUT = "TIMEOUT"


@dataclass(frozen=True, slots=True)
class TauObservationRejectV1:
    """Failure to obtain an observation; never an economic rejection."""

    code: TauObservationRejectCodeV1


@dataclass(frozen=True, slots=True)
class TauReadRequestV1:
    command: TauReadCommandV1
    argument: str = ""


@dataclass(frozen=True, slots=True)
class TauHelloObservationV1:
    environment: str


@dataclass(frozen=True, slots=True)
class TauRulesObservationV1:
    rules_text: str


class TauPendingDirectionV1(Enum):
    INCOMING = "incoming"
    OUTGOING = "outgoing"
    SELF = "self"


@dataclass(frozen=True, slots=True)
class TauPendingTransferV1:
    tx_hash: str
    direction: TauPendingDirectionV1
    amount_atoms: int
    fee_atoms: int
    sequence_number: int | None
    tx_type: str
    received_at: str
    expires_at: str


@dataclass(frozen=True, slots=True)
class TauAccountObservationV1:
    address: str
    chain_balance_atoms: int
    pending_outgoing_atoms: int
    pending_incoming_atoms: int
    pending_fees_atoms: int
    available_balance_atoms: int
    pending_txs: tuple[TauPendingTransferV1, ...]


class TauMempoolStatusV1(Enum):
    QUEUED = "queued"
    EXPIRED = "expired"


class TauDroppedStatusV1(Enum):
    EXPIRED = "expired"
    EVICTED = "evicted"
    REJECTED = "rejected"


@dataclass(frozen=True, slots=True)
class TauTxMempoolObservationV1:
    tx_hash: str
    status: TauMempoolStatusV1
    sender: str | None
    sequence_number: int | None
    received_at: str
    fee_limit_atoms: int
    estimated_fee_atoms: int
    expires_at: str


@dataclass(frozen=True, slots=True)
class TauTxConfirmedObservationV1:
    """Reported canonical inclusion at one node; no finality guarantee."""

    tx_hash: str
    block_hash: str
    block_number: int
    confirmations: int


@dataclass(frozen=True, slots=True)
class TauTxDroppedObservationV1:
    tx_hash: str
    status: TauDroppedStatusV1
    dropped_at: str


@dataclass(frozen=True, slots=True)
class TauTxUnknownObservationV1:
    tx_hash: str


TauTxObservationV1: TypeAlias = (
    TauTxMempoolObservationV1
    | TauTxConfirmedObservationV1
    | TauTxDroppedObservationV1
    | TauTxUnknownObservationV1
)


@dataclass(frozen=True, slots=True)
class TauRemoteErrorObservationV1:
    code: str
    message: str
    details_json: bytes | None


TauObservationBodyV1: TypeAlias = (
    TauRulesObservationV1
    | TauAccountObservationV1
    | TauTxObservationV1
    | TauRemoteErrorObservationV1
)


@dataclass(frozen=True, slots=True)
class TauReadObservationV1:
    """Owned decoded data and original response bytes, with no authenticated context."""

    request: TauReadRequestV1
    body: TauObservationBodyV1
    raw_response_bytes: bytes


class _DecodeFault(ValueError):
    def __init__(self, code: TauObservationRejectCodeV1) -> None:
        self.code = code
        super().__init__(code.value)


def _need(condition: bool, code: TauObservationRejectCodeV1) -> None:
    if not condition:
        raise _DecodeFault(code)


def _text(value: object, limit: int = MAX_TAU_OBSERVATION_TEXT_BYTES_V1) -> str:
    _need(type(value) is str, TauObservationRejectCodeV1.INVALID_RESPONSE)
    result = cast(str, value)
    try:
        size = len(result.encode("utf-8"))
    except UnicodeEncodeError as exc:
        raise _DecodeFault(TauObservationRejectCodeV1.INVALID_RESPONSE) from exc
    _need(size <= limit, TauObservationRejectCodeV1.RESOURCE_LIMIT)
    return result


def _natural(value: object, minimum: int = 0) -> int:
    _need(type(value) is int, TauObservationRejectCodeV1.INVALID_RESPONSE)
    result = cast(int, value)
    _need(result >= minimum, TauObservationRejectCodeV1.INVALID_RESPONSE)
    _need(result <= MAX_TAU_OBSERVATION_INTEGER_V1, TauObservationRejectCodeV1.RESOURCE_LIMIT)
    return result


def _decimal(value: object) -> int:
    text = _text(value, 78)
    _need(
        re.fullmatch(r"0|[1-9][0-9]*", text) is not None,
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    return _natural(int(text))


def _optional_natural(value: object) -> int | None:
    return None if value is None else _natural(value)


def _digest(value: object) -> str:
    text = _text(value, 64)
    _need(
        re.fullmatch(r"[0-9a-f]{64}", text) is not None, TauObservationRejectCodeV1.INVALID_RESPONSE
    )
    return text


def _fields(value: object, expected: set[str]) -> dict[str, object]:
    _need(type(value) is dict, TauObservationRejectCodeV1.INVALID_RESPONSE)
    result = cast(dict[str, object], value)
    _need(set(result) == expected, TauObservationRejectCodeV1.INVALID_RESPONSE)
    return result


def make_tau_read_request_v1(
    command: object, argument: object = ""
) -> TauReadRequestV1 | TauObservationRejectV1:
    if type(command) is not TauReadCommandV1 or command not in (
        TauReadCommandV1.GET_TAU_STATE,
        TauReadCommandV1.GET_ACCOUNT_STATE,
        TauReadCommandV1.GET_TX_STATUS,
    ):
        return TauObservationRejectV1(TauObservationRejectCodeV1.UNSUPPORTED_COMMAND)
    if type(argument) is not str:
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_REQUEST)
    valid = False
    if command is TauReadCommandV1.GET_TAU_STATE:
        valid = argument == ""
    elif command is TauReadCommandV1.GET_ACCOUNT_STATE:
        valid = re.fullmatch(r"[\x21-\x7e]{1,256}", argument) is not None
    elif command is TauReadCommandV1.GET_TX_STATUS:
        valid = re.fullmatch(r"[0-9a-fA-F]{64}", argument) is not None
        if valid:
            argument = argument.lower()
    if not valid:
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_REQUEST)
    return TauReadRequestV1(command, argument)


def canonicalize_tau_read_request_v1(
    request: object,
) -> TauReadRequestV1 | TauObservationRejectV1:
    """Snapshot an exact request before encoding or acquiring external observations."""
    if type(request) is not TauReadRequestV1:
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_REQUEST)
    try:
        command, argument = request.command, request.argument
    except AttributeError:
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_REQUEST)
    return make_tau_read_request_v1(command, argument)


def encode_tau_read_request_v1(request: object) -> bytes | TauObservationRejectV1:
    checked = canonicalize_tau_read_request_v1(request)
    if isinstance(checked, TauObservationRejectV1):
        return checked
    suffix = " " + checked.argument if checked.argument else ""
    return (checked.command.value + suffix).encode("ascii")


def decode_tau_hello_v1(raw: object) -> TauHelloObservationV1 | TauObservationRejectV1:
    if type(raw) is not bytes:
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)
    if len(raw) > MAX_TAU_HELLO_BYTES_V1:
        return TauObservationRejectV1(TauObservationRejectCodeV1.RESOURCE_LIMIT)
    match = re.fullmatch(rb"ok version=2 env=([A-Za-z0-9_-]{1,32}) node=tau-node", raw)
    if match is None:
        return TauObservationRejectV1(TauObservationRejectCodeV1.HANDSHAKE_MISMATCH)
    return TauHelloObservationV1(match.group(1).decode("ascii"))


def _pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        _text(key)
        _need(key not in result, TauObservationRejectCodeV1.INVALID_RESPONSE)
        result[key] = value
    return result


def _json_integer(value: str) -> int:
    return _decimal(value)


def _no_float(_value: str) -> object:
    raise _DecodeFault(TauObservationRejectCodeV1.INVALID_RESPONSE)


def _json_object(raw: bytes) -> dict[str, object]:
    _need(len(raw) > 0, TauObservationRejectCodeV1.INVALID_RESPONSE)
    _need(len(raw) <= MAX_TAU_OBSERVATION_BYTES_V1, TauObservationRejectCodeV1.RESOURCE_LIMIT)
    value = json.loads(
        raw.decode("utf-8"),
        object_pairs_hook=_pairs,
        parse_int=_json_integer,
        parse_float=_no_float,
        parse_constant=_no_float,
    )
    pending: list[tuple[object, int]] = [(value, 0)]
    nodes = 0
    while pending:
        item, depth = pending.pop()
        nodes += 1
        _need(depth <= 32 and nodes <= 16_384, TauObservationRejectCodeV1.RESOURCE_LIMIT)
        if type(item) is dict:
            pending.extend((child, depth + 1) for child in item.values())
        elif type(item) is list:
            pending.extend((child, depth + 1) for child in item)
        elif type(item) is str:
            _text(item)
    _need(type(value) is dict, TauObservationRejectCodeV1.INVALID_RESPONSE)
    return cast(dict[str, object], value)


def _pending_transfer(value: object) -> TauPendingTransferV1:
    fields = _fields(
        value,
        {
            "hash",
            "direction",
            "amount",
            "fee",
            "status",
            "sequence_number",
            "tx_type",
            "received_at",
            "expires_at",
        },
    )
    _need(fields["status"] == "queued", TauObservationRejectCodeV1.INVALID_RESPONSE)
    direction = _text(fields["direction"], 16)
    _need(
        direction in {item.value for item in TauPendingDirectionV1},
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    amount = _decimal(fields["amount"])
    _need(
        direction == "incoming" or amount > 0,
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    return TauPendingTransferV1(
        _digest(fields["hash"]),
        TauPendingDirectionV1(direction),
        amount,
        _decimal(fields["fee"]),
        _optional_natural(fields["sequence_number"]),
        _text(fields["tx_type"], 64),
        _text(fields["received_at"], 64),
        _text(fields["expires_at"], 64),
    )


def _account(data: object, address: str) -> TauAccountObservationV1:
    fields = _fields(
        data,
        {
            "address",
            "chain_balance",
            "pending_outgoing",
            "pending_incoming",
            "pending_fees",
            "available_balance",
            "pending_txs",
        },
    )
    _need(_text(fields["address"], 256) == address, TauObservationRejectCodeV1.SUBJECT_MISMATCH)
    raw_rows = fields["pending_txs"]
    _need(type(raw_rows) is list, TauObservationRejectCodeV1.INVALID_RESPONSE)
    rows = cast(list[object], raw_rows)
    _need(len(rows) <= MAX_TAU_OBSERVATION_ROWS_V1, TauObservationRejectCodeV1.RESOURCE_LIMIT)
    pending = tuple(_pending_transfer(row) for row in rows)
    _need(
        len({row.tx_hash for row in pending}) == len(pending),
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    result = TauAccountObservationV1(
        address,
        _decimal(fields["chain_balance"]),
        _decimal(fields["pending_outgoing"]),
        _decimal(fields["pending_incoming"]),
        _decimal(fields["pending_fees"]),
        _decimal(fields["available_balance"]),
        pending,
    )
    _account_arithmetic(result)
    return result


def _account_arithmetic(account: TauAccountObservationV1) -> None:
    """Check only relations present in the upstream response; self inflow is omitted."""
    outgoing = sum(
        row.amount_atoms
        for row in account.pending_txs
        if row.direction in (TauPendingDirectionV1.OUTGOING, TauPendingDirectionV1.SELF)
    )
    incoming = sum(
        row.amount_atoms
        for row in account.pending_txs
        if row.direction is TauPendingDirectionV1.INCOMING
    )
    self_rows = sum(row.direction is TauPendingDirectionV1.SELF for row in account.pending_txs)
    _need(account.pending_outgoing_atoms == outgoing, TauObservationRejectCodeV1.INVALID_RESPONSE)
    _need(
        account.pending_fees_atoms == sum(row.fee_atoms for row in account.pending_txs),
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    _need(
        account.pending_incoming_atoms >= incoming + self_rows
        if self_rows
        else account.pending_incoming_atoms == incoming,
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    available = max(0, account.chain_balance_atoms - outgoing - account.pending_fees_atoms)
    _need(account.available_balance_atoms == available, TauObservationRejectCodeV1.INVALID_RESPONSE)


def _tx_status(data: object, tx_hash: str) -> TauTxObservationV1:
    _need(type(data) is dict, TauObservationRejectCodeV1.INVALID_RESPONSE)
    fields = cast(dict[str, object], data)
    _need(_digest(fields.get("tx_hash")) == tx_hash, TauObservationRejectCodeV1.SUBJECT_MISMATCH)
    status = _text(fields.get("status"), 16)
    if status == "unknown":
        _fields(fields, {"tx_hash", "status"})
        return TauTxUnknownObservationV1(tx_hash)
    if status == "confirmed":
        _fields(fields, {"tx_hash", "status", "block_hash", "block_number", "confirmations"})
        return TauTxConfirmedObservationV1(
            tx_hash,
            _digest(fields["block_hash"]),
            _natural(fields["block_number"]),
            _natural(fields["confirmations"], 1),
        )
    if status in {item.value for item in TauDroppedStatusV1} and "dropped_at" in fields:
        _fields(fields, {"tx_hash", "status", "dropped_at"})
        return TauTxDroppedObservationV1(
            tx_hash, TauDroppedStatusV1(status), _text(fields["dropped_at"], 64)
        )
    return _mempool_status(fields, tx_hash, status)


def _mempool_status(
    fields: dict[str, object], tx_hash: str, status: str
) -> TauTxMempoolObservationV1:
    _fields(
        fields,
        {
            "tx_hash",
            "status",
            "sender",
            "sequence_number",
            "received_at",
            "fee_limit",
            "estimated_fee",
            "expires_at",
        },
    )
    _need(
        status in {item.value for item in TauMempoolStatusV1},
        TauObservationRejectCodeV1.INVALID_RESPONSE,
    )
    sender = None if fields["sender"] is None else _text(fields["sender"], 256)
    return TauTxMempoolObservationV1(
        tx_hash,
        TauMempoolStatusV1(status),
        sender,
        _optional_natural(fields["sequence_number"]),
        _text(fields["received_at"], 64),
        _natural(fields["fee_limit"]),
        _natural(fields["estimated_fee"]),
        _text(fields["expires_at"], 64),
    )


def _remote_error(value: object) -> TauRemoteErrorObservationV1:
    _need(type(value) is dict, TauObservationRejectCodeV1.INVALID_RESPONSE)
    fields = cast(dict[str, object], value)
    _fields(fields, {"code", "message", "details"} if "details" in fields else {"code", "message"})
    details = None
    if "details" in fields:
        _need(type(fields["details"]) is dict, TauObservationRejectCodeV1.INVALID_RESPONSE)
        details = json.dumps(
            fields["details"],
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
        _need(
            len(details) <= MAX_TAU_OBSERVATION_BYTES_V1, TauObservationRejectCodeV1.RESOURCE_LIMIT
        )
    return TauRemoteErrorObservationV1(
        _text(fields["code"], 128), _text(fields["message"]), details
    )


def _response_body(request: TauReadRequestV1, value: dict[str, object]) -> TauObservationBodyV1:
    _need(
        value.get("command") == request.command.value, TauObservationRejectCodeV1.SUBJECT_MISMATCH
    )
    if value.get("status") == "error":
        _fields(value, {"status", "command", "error"})
        return _remote_error(value["error"])
    _need(value.get("status") == "ok", TauObservationRejectCodeV1.INVALID_RESPONSE)
    _fields(value, {"status", "command", "data"})
    if request.command is TauReadCommandV1.GET_TAU_STATE:
        return TauRulesObservationV1(_text(_fields(value["data"], {"rules_state"})["rules_state"]))
    if request.command is TauReadCommandV1.GET_ACCOUNT_STATE:
        return _account(value["data"], request.argument)
    if request.command is TauReadCommandV1.GET_TX_STATUS:
        return _tx_status(value["data"], request.argument)
    raise _DecodeFault(TauObservationRejectCodeV1.UNSUPPORTED_COMMAND)


def decode_tau_read_response_v1(
    request: object, raw: object
) -> TauReadObservationV1 | TauObservationRejectV1:
    """Own and validate a single unframed JSON response against its exact request."""
    owned_request = canonicalize_tau_read_request_v1(request)
    if isinstance(owned_request, TauObservationRejectV1):
        return owned_request
    if type(raw) is not bytes:
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)
    try:
        body = _response_body(owned_request, _json_object(raw))
    except _DecodeFault as exc:
        return TauObservationRejectV1(exc.code)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_RESPONSE)
    except RecursionError:
        return TauObservationRejectV1(TauObservationRejectCodeV1.RESOURCE_LIMIT)
    return TauReadObservationV1(owned_request, body, raw)
