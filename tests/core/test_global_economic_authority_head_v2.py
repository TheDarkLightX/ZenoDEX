from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from typing import Any, cast

import pytest

from src.core.global_economic_authority_head_v2 import (
    GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V2,
    MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V2,
    GlobalEconomicAuthorityHeadV2,
    GlobalEconomicAuthorityStatusV2,
    decode_global_economic_authority_head_v2,
    require_global_economic_authority_successor_v2,
)
from src.core.global_settlement_primitives_v2 import GLOBAL_SETTLEMENT_ABI_V2
from src.state.canonical import canonical_json_bytes, domain_sep_bytes


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _head(**overrides: object) -> GlobalEconomicAuthorityHeadV2:
    values: dict[str, object] = {
        "generation": 3,
        "genesis_id": _root(10),
        "chain_id": "chain:testnet-v2",
        "deployment_root": _root(11),
        "epoch_store_root": _root(12),
        "profile_root": _root(13),
        "writer_epoch": 7,
        "guest_role_binding_root": _root(14),
        "signature_manifest_root": _root(15),
        "status": GlobalEconomicAuthorityStatusV2.ACTIVE,
    }
    values.update(overrides)
    return GlobalEconomicAuthorityHeadV2(**cast(Any, values))


def _payload_with(**changes: object) -> bytes:
    value = json.loads(_head().canonical_bytes)
    value.update(changes)
    return canonical_json_bytes(value)


def test_active_head_roundtrips_with_exact_bytes_and_root() -> None:
    head = _head()

    decoded = decode_global_economic_authority_head_v2(head.canonical_bytes)

    assert decoded == head
    assert decoded.canonical_bytes == head.canonical_bytes
    assert decoded.authority_root == head.authority_root


def test_authority_root_uses_independent_literal_canonical_record() -> None:
    head = _head()
    canonical = (
        b'{"abi":"zenodex/global-settlement-abi/v2","chain_id":"chain:testnet-v2",'
        b'"deployment_root":"0x000000000000000000000000000000000000000000000000000000000000000b",'
        b'"epoch_store_root":"0x000000000000000000000000000000000000000000000000000000000000000c",'
        b'"generation":3,"genesis_id":"0x000000000000000000000000000000000000000000000000000000000000000a",'
        b'"guest_role_binding_root":"0x000000000000000000000000000000000000000000000000000000000000000e",'
        b'"profile_root":"0x000000000000000000000000000000000000000000000000000000000000000d",'
        b'"schema":"global-economic-authority-head-v2",'
        b'"signature_manifest_root":"0x000000000000000000000000000000000000000000000000000000000000000f",'
        b'"status":"ACTIVE","writer_epoch":7}'
    )

    expected_root = "0x" + hashlib.sha256(
        domain_sep_bytes("global-economic-current-authority-v2", version=2)
        + canonical
    ).hexdigest()

    assert head.canonical_bytes == canonical
    assert head.authority_root == expected_root


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("generation", 4),
        ("genesis_id", _root(20)),
        ("chain_id", "chain:changed"),
        ("deployment_root", _root(21)),
        ("epoch_store_root", _root(22)),
        ("profile_root", _root(23)),
        ("writer_epoch", 8),
        ("guest_role_binding_root", _root(24)),
        ("signature_manifest_root", _root(25)),
        ("status", GlobalEconomicAuthorityStatusV2.REVOKED),
    ),
)
def test_each_authority_coordinate_changes_the_content_root(
    field: str,
    value: object,
) -> None:
    head = _head()

    mutated = replace(head, **cast(Any, {field: value}))

    assert mutated.authority_root != head.authority_root
    assert mutated.canonical_bytes != head.canonical_bytes


def test_revoked_successor_is_adjacent_coordinate_preserving_and_terminal() -> None:
    active = _head()

    revoked = active.revoked_successor()

    require_global_economic_authority_successor_v2(active, revoked)
    assert revoked.generation == active.generation + 1
    assert revoked.status is GlobalEconomicAuthorityStatusV2.REVOKED
    with pytest.raises(ValueError, match="terminal|revoked"):
        revoked.revoked_successor()
    with pytest.raises(ValueError, match="terminal"):
        require_global_economic_authority_successor_v2(
            revoked,
            replace(revoked, generation=revoked.generation + 1),
        )


@pytest.mark.parametrize(
    ("field", "value", "error"),
    (
        ("generation", False, TypeError),
        ("generation", -1, ValueError),
        ("generation", 1 << 64, ValueError),
        ("writer_epoch", True, TypeError),
        ("writer_epoch", -1, ValueError),
        ("genesis_id", True, TypeError),
        ("chain_id", 1, TypeError),
        ("deployment_root", True, TypeError),
        ("profile_root", "0x12", ValueError),
        ("status", "ACTIVE", TypeError),
    ),
)
def test_constructor_rejects_invalid_scalar_types_and_ranges(
    field: str,
    value: object,
    error: type[Exception],
) -> None:
    with pytest.raises(error):
        _head(**{field: value})


@pytest.mark.parametrize(
    ("changes", "error"),
    (
        ({"generation": False}, TypeError),
        ({"writer_epoch": True}, TypeError),
        ({"generation": -1}, ValueError),
        ({"generation": 1 << 64}, ValueError),
        ({"schema": "wrong-schema"}, ValueError),
        ({"abi": "wrong-abi"}, ValueError),
        ({"unknown": "field"}, ValueError),
        ({"genesis_id": 1}, TypeError),
        ({"genesis_id": "ordinary-token"}, ValueError),
        ({"genesis_id": _root(0)}, ValueError),
        ({"genesis_id": "0X" + "ab" * 32}, ValueError),
        ({"deployment_root": "0x12"}, ValueError),
        ({"status": "UNKNOWN"}, ValueError),
    ),
)
def test_decoder_rejects_invalid_scalars_schema_and_closed_fields(
    changes: dict[str, object],
    error: type[Exception],
) -> None:
    with pytest.raises(error):
        decode_global_economic_authority_head_v2(_payload_with(**changes))


def test_decoder_rejects_missing_fields_noncanonical_bytes_and_duplicate_keys() -> None:
    value = json.loads(_head().canonical_bytes)
    del value["profile_root"]
    with pytest.raises(ValueError, match="field set"):
        decode_global_economic_authority_head_v2(canonical_json_bytes(value))

    with pytest.raises(ValueError, match="canonical"):
        decode_global_economic_authority_head_v2(b" " + _head().canonical_bytes)

    duplicate = _head().canonical_bytes.replace(
        b'"status":"ACTIVE"',
        b'"status":"ACTIVE","status":"ACTIVE"',
    )
    with pytest.raises(ValueError, match="duplicate"):
        decode_global_economic_authority_head_v2(duplicate)


def test_decoder_rejects_wrong_input_type_size_and_deep_nesting() -> None:
    with pytest.raises(TypeError, match="exact bytes"):
        decode_global_economic_authority_head_v2(
            bytearray(_head().canonical_bytes),  # type: ignore[arg-type]
        )

    with pytest.raises(ValueError, match="outside the bound"):
        decode_global_economic_authority_head_v2(
            b"x" * (MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V2 + 1)
        )

    hostile = (b"[" * 1_500) + (b"]" * 1_500)
    assert len(hostile) < MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V2
    with pytest.raises(ValueError, match="nesting exceeds"):
        decode_global_economic_authority_head_v2(hostile)


@pytest.mark.parametrize(
    "field",
    (
        "genesis_id",
        "chain_id",
        "deployment_root",
        "epoch_store_root",
        "profile_root",
        "writer_epoch",
        "guest_role_binding_root",
        "signature_manifest_root",
    ),
)
def test_revocation_rejects_coordinate_changes(field: str) -> None:
    active = _head()
    revoked = active.revoked_successor()
    replacement: object = (
        active.writer_epoch + 1
        if field == "writer_epoch"
        else _root(100)
        if field == "genesis_id"
        else "changed:coordinate"
        if field == "chain_id"
        else _root(99)
    )

    with pytest.raises(ValueError, match="coordinates"):
        require_global_economic_authority_successor_v2(
            active,
            replace(revoked, **cast(Any, {field: replacement})),
        )


def test_successor_requires_adjacent_revocation_and_exact_types() -> None:
    active = _head()

    with pytest.raises(ValueError, match="adjacent"):
        require_global_economic_authority_successor_v2(
            active,
            replace(active, generation=active.generation + 2, status=GlobalEconomicAuthorityStatusV2.REVOKED),
        )
    with pytest.raises(ValueError, match="REVOKED|revocation"):
        require_global_economic_authority_successor_v2(
            active,
            replace(active, generation=active.generation + 1),
        )
    with pytest.raises(ValueError, match="cannot advance"):
        replace(active, generation=(1 << 64) - 1).revoked_successor()
    with pytest.raises(TypeError, match="type is not closed"):
        require_global_economic_authority_successor_v2(active, object())  # type: ignore[arg-type]


def test_schema_and_abi_literals_are_versioned() -> None:
    canonical = _head().to_canonical()

    assert canonical["schema"] == GLOBAL_ECONOMIC_AUTHORITY_HEAD_SCHEMA_V2
    assert canonical["abi"] == GLOBAL_SETTLEMENT_ABI_V2
