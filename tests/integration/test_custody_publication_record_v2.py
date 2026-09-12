"""Pure replay and identity checks for complete isolated custody records.

The signature and receipt values are protocol fixtures retained by a record.
These tests establish record binding and replay semantics without claiming a
new cryptographic verifier or a publication authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from typing import Any, cast

import pytest

from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
from src.core.asset_lane_custody_frame_v2 import (
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2,
    decode_asset_lane_custody_global_frame_v2,
)
from src.core.asset_lane_custody_input_v2 import (
    prepare_asset_lane_custody_global_prover_input_v2,
)
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.economic_command_authentication_v2 import (
    _AUTHENTICATION_MESSAGE_DOMAIN_V2,
    prepare_isolated_economic_command_authentication_v2,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    MAX_COMMAND_SIGNATURE_BYTES_V1,
)
from src.core.global_settlement_primitives_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_U64_V2,
    canonical_global_bytes_v2,
)
from src.integration.custody_publication_record_v2 import (
    CustodyPublicationRecordV2,
    replay_custody_publication_frame_v2,
)
from src.integration.global_receipt_verifier_v1 import (
    MAX_JOURNAL_BYTES_V1,
    MAX_RECEIPT_BYTES_V1,
)
from src.state.canonical import domain_sep_bytes
from tests.core.test_asset_lane_custody_statement_parity_v2 import CASES
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import (
    _RECEIPT,
    _case,
)

_AUTH_MESSAGE_PREFIX = domain_sep_bytes(_AUTHENTICATION_MESSAGE_DOMAIN_V2, version=2)
_SOURCE_PUBLICATION_ID = "0x" + "11" * 32
_AUTHORITY_ROOT = "0x" + "22" * 32
_COMPONENTS = ("frame", "statement", "authentication_message", "signature", "receipt")
_STATEMENT_SHA256 = (
    "d8f38fa443cfc93451a0b01489a09c78670533a1e37dc5b8f8810fe5b2ed79bc",
    "2748a97af116ede183091d9095fe4c780018ca31f7be4657afa60f0f49d42fb4",
    "1a5114352d7f026bf4e88c3292326fe08e31a87811110eda1516d804b83b1212",
    "e2b429cc5bd41fe8ddef2787d6d7b5043851106553765c4f303d93f214cfdf87",
    "fd232533986c0a081ae115e8ba0102cd4416413d3cf73f1f32a09727e51c2e88",
)


_EXPECTED_ECONOMICS = (
    {
        "route": "TRANSFER",
        "command_kind": "asset_transfer",
        "amount_atoms": 10,
        "pre_height": 8,
        "post_height": 9,
        "pre_balances": (("alice", 80),),
        "post_balances": (("alice", 68), ("bob", 10), ("treasury", 2)),
        "pre_supplies": (("USD", 100),),
        "post_supplies": (("USD", 100),),
        "pre_custody": (("vault", 20),),
        "post_custody": (("vault", 20),),
        "pre_liabilities": (("alice", 20),),
        "post_liabilities": (("alice", 20),),
    },
    {
        "route": "MANAGED_LIFECYCLE",
        "command_kind": "managed_asset_issue",
        "amount_atoms": 7,
        "pre_height": 8,
        "post_height": 9,
        "pre_balances": (("alice", 80),),
        "post_balances": (("alice", 87),),
        "pre_supplies": (("USD", 100),),
        "post_supplies": (("USD", 107),),
        "pre_custody": (("vault", 20),),
        "post_custody": (("vault", 20),),
        "pre_liabilities": (("alice", 20),),
        "post_liabilities": (("alice", 20),),
    },
    {
        "route": "MANAGED_LIFECYCLE",
        "command_kind": "managed_asset_burn",
        "amount_atoms": 80,
        "pre_height": 8,
        "post_height": 9,
        "pre_balances": (("alice", 80),),
        "post_balances": (),
        "pre_supplies": (("USD", 100),),
        "post_supplies": (("USD", 20),),
        "pre_custody": (("vault", 20),),
        "post_custody": (("vault", 20),),
        "pre_liabilities": (("alice", 20),),
        "post_liabilities": (("alice", 20),),
    },
    {
        "route": "MANAGED_LIFECYCLE",
        "command_kind": "managed_asset_issue",
        "amount_atoms": 1,
        "pre_height": 8,
        "post_height": 9,
        "pre_balances": (),
        "post_balances": (("alice", 1),),
        "pre_supplies": (),
        "post_supplies": (("USD", 1),),
        "pre_custody": (),
        "post_custody": (),
        "pre_liabilities": (),
        "post_liabilities": (),
    },
    {
        "route": "MANAGED_LIFECYCLE",
        "command_kind": "managed_asset_burn",
        "amount_atoms": 1,
        "pre_height": 8,
        "post_height": 9,
        "pre_balances": (("alice", 1),),
        "post_balances": (),
        "pre_supplies": (("USD", 1),),
        "post_supplies": (),
        "pre_custody": (),
        "post_custody": (),
        "pre_liabilities": (),
        "post_liabilities": (),
    },
)


@dataclass(frozen=True)
class _AdmittedRecord:
    case: Any
    record: CustodyPublicationRecordV2


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _admitted_record(index: int) -> _AdmittedRecord:
    case = _case(index)
    context, lane, command, global_pre, _ = case.inputs
    frame = prepare_asset_lane_custody_global_prover_input_v2(
        context, lane, command, global_pre
    )
    if type(frame) is not bytes or type(case.expected) is not bytes:
        raise AssertionError("the retained vector must be accepted before record construction")
    _, _, message = prepare_isolated_economic_command_authentication_v2(case.candidate)
    return _AdmittedRecord(
        case,
        CustodyPublicationRecordV2(
            1,
            _SOURCE_PUBLICATION_ID,
            _AUTHORITY_ROOT,
            frame,
            case.expected,
            message,
            case.candidate.envelope.signature_bytes,
            _RECEIPT,
        ),
    )


@pytest.fixture(scope="module")
def admitted_records() -> tuple[_AdmittedRecord, ...]:
    return tuple(_admitted_record(index) for index in range(len(CASES)))


@pytest.fixture(scope="module")
def rejected_case():
    return _case(amount=1000)


@pytest.mark.parametrize(
    "index",
    range(len(CASES)),
    ids=[case["name"] for case in CASES],
)
def test_admitted_vector_replays_complete_pre_post_pair_and_exact_statement(
    admitted_records: tuple[_AdmittedRecord, ...], index: int
) -> None:
    item = admitted_records[index]
    replay = item.record.replay()
    context, lane, command, global_pre, global_post = item.case.inputs
    expected = _EXPECTED_ECONOMICS[index]
    route, *_ = decode_asset_lane_custody_global_frame_v2(item.record.frame)

    assert route.value == expected["route"]
    assert replay.context.to_canonical() == context.to_canonical()
    assert replay.command.to_canonical() == command.to_canonical()
    assert replay.lane_pre.to_canonical() == lane.to_canonical()
    assert replay.global_pre.to_canonical() == global_pre.to_canonical()
    assert replay.global_post.to_canonical() == global_post.to_canonical()
    assert replay.statement == item.case.expected
    assert hashlib.sha256(replay.statement).hexdigest() == _STATEMENT_SHA256[index]

    assert replay.command.command_kind == expected["command_kind"]
    assert replay.command.amount_atoms == expected["amount_atoms"]
    assert replay.global_pre.height == expected["pre_height"]
    assert replay.global_post.height == expected["post_height"]
    assert tuple((row.owner, row.amount_atoms) for row in replay.global_pre.balances) == expected[
        "pre_balances"
    ]
    assert tuple((row.owner, row.amount_atoms) for row in replay.global_post.balances) == expected[
        "post_balances"
    ]
    assert tuple((row.asset, row.amount_atoms) for row in replay.global_pre.supplies) == expected[
        "pre_supplies"
    ]
    assert tuple((row.asset, row.amount_atoms) for row in replay.global_post.supplies) == expected[
        "post_supplies"
    ]
    assert tuple((row.owner, row.amount_atoms) for row in replay.global_pre.custody) == expected[
        "pre_custody"
    ]
    assert tuple((row.owner, row.amount_atoms) for row in replay.global_post.custody) == expected[
        "post_custody"
    ]
    assert tuple(
        (row.owner, row.amount_atoms) for row in replay.global_pre.liabilities
    ) == expected["pre_liabilities"]
    assert tuple(
        (row.owner, row.amount_atoms) for row in replay.global_post.liabilities
    ) == expected["post_liabilities"]


def test_publication_id_matches_independent_canonical_commitment(
    admitted_records: tuple[_AdmittedRecord, ...],
) -> None:
    record = admitted_records[0].record
    expected_value = {
        "schema": "isolated-custody-publication-v2",
        "abi": GLOBAL_SETTLEMENT_ABI_V2,
        "sequence": record.sequence,
        "source_publication_id": record.source_publication_id,
        "authority_root": record.authority_root,
        "frame": "0x" + hashlib.sha256(record.frame).hexdigest(),
        "statement": "0x" + hashlib.sha256(record.statement).hexdigest(),
        "authentication_message": "0x" + hashlib.sha256(record.authentication_message).hexdigest(),
        "signature": "0x" + hashlib.sha256(record.signature).hexdigest(),
        "receipt": "0x" + hashlib.sha256(record.receipt).hexdigest(),
    }
    expected = hashlib.sha256(
        domain_sep_bytes("isolated-custody-publication-v2", version=2)
        + canonical_global_bytes_v2(expected_value)
    ).hexdigest()
    assert record.publication_id == "0x" + expected


@pytest.mark.parametrize(
    "field",
    ("sequence", "source_publication_id", "authority_root", *_COMPONENTS),
)
def test_publication_id_changes_for_each_committed_coordinate(
    admitted_records: tuple[_AdmittedRecord, ...], field: str
) -> None:
    record = admitted_records[0].record
    if field == "sequence":
        value: object = record.sequence + 1
    elif field == "source_publication_id":
        value = _root(33)
    elif field == "authority_root":
        value = _root(34)
    else:
        value = getattr(record, field) + b"x"
    variant = replace(record, **{field: value})
    assert variant.publication_id != record.publication_id


def test_record_request_parts_and_byte_count_are_exact(
    admitted_records: tuple[_AdmittedRecord, ...],
) -> None:
    record = admitted_records[0].record
    _, context_raw, _, command_raw, _, _ = decode_asset_lane_custody_global_frame_v2(record.frame)
    assert record.request_parts == (
        context_raw,
        command_raw,
        record.authentication_message,
        record.signature,
        record.receipt,
    )
    assert record.byte_count == sum(
        len(raw)
        for raw in (
            record.frame,
            record.statement,
            record.authentication_message,
            record.signature,
            record.receipt,
        )
    )


def test_rejected_economics_cannot_become_a_durable_record(rejected_case) -> None:
    context, lane, command, global_pre, _ = rejected_case.inputs
    result = prepare_asset_lane_custody_global_prover_input_v2(
        context, lane, command, global_pre
    )
    assert type(result) is AssetLaneRejectedV2
    assert result == rejected_case.expected
    assert result.pre_state_root == result.post_state_root == lane.state_root
    assert result.effects.is_empty
    with pytest.raises(ValueError, match="component exceeds"):
        CustodyPublicationRecordV2(
            1,
            _SOURCE_PUBLICATION_ID,
            _AUTHORITY_ROOT,
            cast(Any, result),
            b"statement",
            b"message",
            b"signature",
            b"receipt",
        )


def _mutated_authentication_record(item: _AdmittedRecord, kind: str) -> CustodyPublicationRecordV2:
    record = item.record
    message = record.authentication_message
    if not message.startswith(_AUTH_MESSAGE_PREFIX):
        raise AssertionError("the retained message must use the V2 authentication domain")
    payload = message[len(_AUTH_MESSAGE_PREFIX) :]
    if kind == "domain":
        message = bytes((message[0] ^ 1,)) + message[1:]
    elif kind == "duplicate":
        message = _AUTH_MESSAGE_PREFIX + payload[:-1] + (
            b',"schema":"zenodex/economic-command-authentication/v2"}'
        )
    else:
        value = cast(dict[str, Any], json.loads(payload))
        if kind == "intent":
            intent = cast(dict[str, Any], value["intent"])
            intent["nonce"] = int(intent["nonce"]) + 1
        else:
            value["command_body_bytes_digest"] = _root(99)
        message = _AUTH_MESSAGE_PREFIX + canonical_global_bytes_v2(value)
    return replace(record, authentication_message=message)


def _occurrence_mutated_record(item: _AdmittedRecord) -> CustodyPublicationRecordV2:
    record = item.record
    context, lane, command, global_pre, _ = item.case.inputs
    occurrence = context.occurrence
    if occurrence is None:
        raise AssertionError("the retained vector must carry an occurrence")
    altered_context = AssetLaneContextV2(
        context.writer_epoch,
        context.module_release_id,
        context.global_pre_state_root,
        replace(occurrence, nonce=occurrence.nonce + 1),
    )
    frame = prepare_asset_lane_custody_global_prover_input_v2(
        altered_context, lane, command, global_pre
    )
    if type(frame) is not bytes:
        raise AssertionError("the altered occurrence must still produce a frame")
    statement = replay_custody_publication_frame_v2(frame).statement
    return replace(record, frame=frame, statement=statement)


@pytest.mark.parametrize(
    "kind, message",
    (
        ("domain", "message domain mismatch"),
        ("duplicate", "duplicate field"),
        ("intent", "occurrence nonce mismatch"),
        ("occurrence", "occurrence nonce mismatch"),
        ("body_digest", "body digest mismatch"),
    ),
)
def test_authentication_domain_fields_and_occurrence_mutations_reject(
    admitted_records: tuple[_AdmittedRecord, ...], kind: str, message: str
) -> None:
    item = admitted_records[0]
    mutated = (
        _occurrence_mutated_record(item)
        if kind == "occurrence"
        else _mutated_authentication_record(item, kind)
    )
    with pytest.raises(ValueError, match=message):
        mutated.replay()


@pytest.mark.parametrize(
    "field, message",
    (
        ("statement", "statement differs"),
        ("frame", "trailing bytes"),
    ),
)
def test_altered_statement_or_frame_cannot_replay(
    admitted_records: tuple[_AdmittedRecord, ...], field: str, message: str
) -> None:
    record = admitted_records[0].record
    variant = replace(record, **{field: getattr(record, field) + b"x"})
    with pytest.raises(ValueError, match=message):
        variant.replay()


@pytest.mark.parametrize(
    "field, limit",
    (
        ("frame", MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2),
        ("statement", MAX_JOURNAL_BYTES_V1),
        ("authentication_message", MAX_JOURNAL_BYTES_V1),
        ("signature", MAX_COMMAND_SIGNATURE_BYTES_V1),
        ("receipt", MAX_RECEIPT_BYTES_V1),
    ),
)
def test_record_components_accept_exact_ceiling_and_reject_next_byte(
    admitted_records: tuple[_AdmittedRecord, ...], field: str, limit: int
) -> None:
    record = admitted_records[0].record
    accepted = replace(record, **{field: b"x" * limit})
    assert len(getattr(accepted, field)) == limit
    with pytest.raises(ValueError, match="component exceeds"):
        replace(record, **{field: b"x" * (limit + 1)})


@pytest.mark.parametrize("field", _COMPONENTS)
def test_record_components_require_nonempty_exact_bytes(
    admitted_records: tuple[_AdmittedRecord, ...], field: str
) -> None:
    record = admitted_records[0].record
    with pytest.raises(ValueError, match="component exceeds"):
        replace(record, **{field: b""})
    with pytest.raises(ValueError, match="component exceeds"):
        replace(record, **{field: cast(Any, bytearray(b"x"))})


@pytest.mark.parametrize("value", (0, -1, MAX_U64_V2 + 1, True, 1.0))
def test_sequence_requires_positive_unsigned_64_bit_integer(
    admitted_records: tuple[_AdmittedRecord, ...], value: object
) -> None:
    with pytest.raises((TypeError, ValueError)):
        replace(admitted_records[0].record, sequence=value)


def test_sequence_accepts_unsigned_64_bit_ceiling(
    admitted_records: tuple[_AdmittedRecord, ...],
) -> None:
    record = replace(admitted_records[0].record, sequence=MAX_U64_V2)
    assert record.sequence == MAX_U64_V2


@pytest.mark.parametrize("field", ("source_publication_id", "authority_root"))
@pytest.mark.parametrize("value", ("ordinary-token", "0x" + "00" * 32, "0X" + "11" * 32))
def test_record_identity_roots_require_nonzero_canonical_lowercase_roots(
    admitted_records: tuple[_AdmittedRecord, ...], field: str, value: str
) -> None:
    with pytest.raises((TypeError, ValueError)):
        replace(admitted_records[0].record, **{field: value})
