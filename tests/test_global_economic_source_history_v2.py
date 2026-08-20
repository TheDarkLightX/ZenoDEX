from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from tools.check_global_economic_delta_v2 import decode_delta_plan_bytes_v2
from tools.global_economic_source_history_v2 import (
    MAX_SOURCE_HISTORY_INPUT_BYTES_V2,
    U32_MAX,
    U64_MAX,
    SourceHistoryRejectCodeV2,
    SourceHistoryValidationErrorV2,
    decode_source_history_statement_bytes_v2,
    validate_source_history_statement_v2,
)

DATA = Path(__file__).parent / "data"
PLAN_PATH = DATA / "global_economic_delta_v2_plan.json"
STATEMENT_PATH = DATA / "global_economic_source_history_v2_statement.json"
STATEMENT_ROOT = "sha256:27218cf30e6dc87974e8190cf77510969472a3015b42b6fb9a59e16af55d3744"


def _plan():
    return decode_delta_plan_bytes_v2(PLAN_PATH.read_bytes())


def _statement() -> dict[str, object]:
    value = json.loads(STATEMENT_PATH.read_text(encoding="ascii"))
    assert isinstance(value, dict)
    return value


def _reject(
    statement: object, expected: SourceHistoryRejectCodeV2
) -> SourceHistoryValidationErrorV2:
    with pytest.raises(SourceHistoryValidationErrorV2) as captured:
        validate_source_history_statement_v2(_plan(), statement)
    assert captured.value.code is expected
    return captured.value


def test_python_shadow_matches_rust_canonical_statement_vector() -> None:
    # Arrange
    raw = STATEMENT_PATH.read_bytes()

    # Act
    checked = decode_source_history_statement_bytes_v2(_plan(), raw)

    # Assert
    assert checked.canonical_bytes == raw
    assert checked.root == STATEMENT_ROOT
    assert checked.delta_plan_root == _plan().root
    assert len(checked.source_availability_claims) == 3


@pytest.mark.parametrize(
    ("field", "replacement"),
    [
        ("source_kind", "ancestor_claim"),
        ("asset", "zusd"),
        ("amount_atoms", 6),
        ("source_root", "sha256:" + "12" * 32),
    ],
)
def test_exact_source_binding_mutants_are_rejected(
    field: str, replacement: object
) -> None:
    # Arrange
    statement = _statement()
    claims = statement["source_availability_claims"]
    assert isinstance(claims, list) and isinstance(claims[0], dict)
    claims[0][field] = replacement

    # Act / Assert
    _reject(statement, SourceHistoryRejectCodeV2.SOURCE_BINDING_MISMATCH)


def test_finality_bva_accepts_equal_heights_and_rejects_neighbors() -> None:
    # Arrange
    accepted = _statement()
    claim = accepted["source_availability_claims"][0]  # type: ignore[index]
    claim["source_height"] = 30
    claim["finalized_height"] = 30
    source_after = copy.deepcopy(accepted)
    source_after["source_availability_claims"][0]["source_height"] = 31  # type: ignore[index]
    finality_after = copy.deepcopy(accepted)
    finality_after["source_availability_claims"][0]["finalized_height"] = 31  # type: ignore[index]

    # Act / Assert
    assert validate_source_history_statement_v2(_plan(), accepted).history_height == 30
    for candidate in (source_after, finality_after):
        _reject(candidate, SourceHistoryRejectCodeV2.FINALITY_ORDER_INVALID)
    maximum = _statement()
    maximum["history_height"] = U64_MAX
    maximum["source_availability_claims"][0]["source_height"] = U64_MAX  # type: ignore[index]
    maximum["source_availability_claims"][0]["finalized_height"] = U64_MAX  # type: ignore[index]
    assert validate_source_history_statement_v2(_plan(), maximum).history_height == U64_MAX


def test_u32_coordinate_bva_accepts_max_and_rejects_max_plus_one() -> None:
    # Arrange
    accepted = _statement()
    accepted["source_availability_claims"][0]["tx_index"] = U32_MAX  # type: ignore[index]
    rejected = copy.deepcopy(accepted)
    rejected["source_availability_claims"][0]["tx_index"] = U32_MAX + 1  # type: ignore[index]

    # Act / Assert
    assert validate_source_history_statement_v2(_plan(), accepted)
    _reject(rejected, SourceHistoryRejectCodeV2.DECODE_INVALID)


def test_caller_unconsumed_flag_root_alias_and_duplicate_nullifier_reject() -> None:
    # Arrange
    caller_flag = _statement()
    caller_flag["source_availability_claims"][0]["unconsumed"] = True  # type: ignore[index]
    root_alias = _statement()
    root_alias["source_availability_claims"][0]["consumption_nullifier"] = (  # type: ignore[index]
        root_alias["source_availability_claims"][0]["source_root"]  # type: ignore[index]
    )
    duplicate_nullifier = _statement()
    duplicate_nullifier["source_availability_claims"][1][  # type: ignore[index]
        "consumption_nullifier"
    ] = duplicate_nullifier["source_availability_claims"][0][  # type: ignore[index]
        "consumption_nullifier"
    ]

    # Act / Assert
    _reject(caller_flag, SourceHistoryRejectCodeV2.DECODE_INVALID)
    _reject(root_alias, SourceHistoryRejectCodeV2.ROOT_ROLE_CONFLICT)
    _reject(
        duplicate_nullifier,
        SourceHistoryRejectCodeV2.DUPLICATE_CONSUMPTION_NULLIFIER,
    )


def test_checked_python_statement_owns_claims_and_is_read_only() -> None:
    # Arrange
    statement = _statement()
    checked = validate_source_history_statement_v2(_plan(), statement)
    original_root = checked.root

    # Act
    claims = statement["source_availability_claims"]
    assert isinstance(claims, list)
    claims.clear()

    # Assert
    assert checked.root == original_root
    with pytest.raises(TypeError):
        checked.source_availability_claims[0]["amount_atoms"] = 99  # type: ignore[index]


def test_malformed_bytes_and_input_limit_match_rust_reject_classes() -> None:
    # Arrange
    raw = STATEMENT_PATH.read_bytes()
    candidates = (
        b"\xef\xbb\xbf" + raw,
        raw.decode("ascii").encode("utf-16"),
        raw.replace(b'"writer_epoch":1', b'"writer_epoch":true', 1),
        raw.replace(b'"tx_index":0', f'"tx_index":{U32_MAX + 1}'.encode(), 1),
    )

    # Act / Assert
    for candidate in candidates:
        with pytest.raises(SourceHistoryValidationErrorV2) as captured:
            decode_source_history_statement_bytes_v2(_plan(), candidate)
        assert captured.value.code is SourceHistoryRejectCodeV2.DECODE_INVALID
    exact = raw + b" " * (MAX_SOURCE_HISTORY_INPUT_BYTES_V2 - len(raw))
    assert decode_source_history_statement_bytes_v2(_plan(), exact)
    with pytest.raises(SourceHistoryValidationErrorV2) as captured:
        decode_source_history_statement_bytes_v2(
            _plan(), b" " * (MAX_SOURCE_HISTORY_INPUT_BYTES_V2 + 1)
        )
    assert captured.value.code is SourceHistoryRejectCodeV2.INPUT_TOO_LARGE


def test_hostile_scalar_objects_cannot_forge_exact_equality() -> None:
    # Arrange
    class AlwaysEqual:
        def __eq__(self, _other: object) -> bool:
            return True

    statement = _statement()
    statement["delta_plan_root"] = AlwaysEqual()

    # Act / Assert
    _reject(statement, SourceHistoryRejectCodeV2.DECODE_INVALID)


def test_mapping_insertion_order_is_a_canonicalization_metamorphism() -> None:
    # Arrange
    ordinary = _statement()
    reordered = dict(reversed(tuple(ordinary.items())))

    # Act
    first = validate_source_history_statement_v2(_plan(), ordinary)
    second = validate_source_history_statement_v2(_plan(), reordered)

    # Assert
    assert second.canonical_bytes == first.canonical_bytes
    assert second.root == first.root
