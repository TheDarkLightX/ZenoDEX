from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
import sys
import types
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path

import pytest

from experiments.global_economic_object_nullifier_reference_v2 import (
    MAX_REFERENCE_ARCHIVE_BYTES_V2,
    MAX_REFERENCE_CLAIMS_PER_STEP_V2,
    MAX_REFERENCE_NULLIFIERS_V2,
    CanonicalReferenceNullifierArchiveV2,
    ReferenceAcceptedV2,
    ReferenceConsumptionClaimV2,
    ReferenceNullifierEntryV2,
    ReferenceObjectIdV2,
    ReferenceOccurrenceIdV2,
    ReferenceRejectCodeV2,
    ReferenceRejectedV2,
    apply_reference_object_nullifiers_v2,
    canonical_reference_archive_bytes_v2,
    reference_archive_digest_v2,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE_PATH = REPO_ROOT / "experiments/global_economic_object_nullifier_reference_v2.py"
GOLDEN_PATH = (
    REPO_ROOT
    / "tests/data/global_economic_object_nullifier_reference_v2_golden.json"
)


def _hex_id(number: int) -> str:
    return f"0x{number:064x}"


def _object_id(number: int) -> ReferenceObjectIdV2:
    return ReferenceObjectIdV2(_hex_id(number))


def _occurrence_id(number: int) -> ReferenceOccurrenceIdV2:
    return ReferenceOccurrenceIdV2(_hex_id(number))


def _claim(object_number: int, occurrence_number: int) -> ReferenceConsumptionClaimV2:
    return ReferenceConsumptionClaimV2(
        object_id=_object_id(object_number),
        consumed_by_occurrence_id=_occurrence_id(occurrence_number),
    )


def _entry(object_number: int, occurrence_number: int) -> ReferenceNullifierEntryV2:
    return ReferenceNullifierEntryV2(
        object_id=_object_id(object_number),
        first_consumed_by_occurrence_id=_occurrence_id(occurrence_number),
    )


def _archive(size: int) -> CanonicalReferenceNullifierArchiveV2:
    return CanonicalReferenceNullifierArchiveV2(
        entries=tuple(_entry(index, 10_000 + index) for index in range(1, size + 1))
    )


def _independent_model(
    pre: dict[str, str],
    claims: tuple[tuple[str, str], ...],
) -> tuple[str, str | None, dict[str, str] | None]:
    """Independent grade-3 set model; it does not call the reference transition."""

    if len(claims) > 64:
        return "rejected", "REFERENCE_STEP_LIMIT_EXCEEDED", None
    object_ids = tuple(object_id for object_id, _ in claims)
    if len(set(object_ids)) != len(object_ids):
        return "rejected", "REFERENCE_DUPLICATE_IN_BATCH", None
    if any(object_id in pre for object_id in object_ids):
        return "rejected", "REFERENCE_ALREADY_CONSUMED", None
    if len(pre) + len(claims) > 4096:
        return "rejected", "REFERENCE_ARCHIVE_CAPACITY_EXCEEDED", None
    post = dict(pre)
    post.update(claims)
    return "accepted", None, dict(sorted(post.items()))


def _result_projection(result: object) -> tuple[str, str | None, dict[str, str] | None]:
    if type(result) is ReferenceRejectedV2:
        rejected = result
        return "rejected", rejected.code.value, None
    assert type(result) is ReferenceAcceptedV2
    accepted = result
    return (
        "accepted",
        None,
        {
            entry.object_id.value: entry.first_consumed_by_occurrence_id.value
            for entry in accepted.post_archive.entries
        },
    )


def test_given_empty_claims_when_applied_then_reference_accepts_exact_value_noop() -> None:
    # Arrange
    pre = _archive(1)
    pre_bytes = canonical_reference_archive_bytes_v2(pre)

    # Act
    result = apply_reference_object_nullifiers_v2(pre, ())

    # Assert
    assert type(result) is ReferenceAcceptedV2
    assert result.post_archive == pre
    assert result.post_archive is not pre
    assert canonical_reference_archive_bytes_v2(result.post_archive) == pre_bytes
    assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)
    assert result.post_reference_archive_digest == reference_archive_digest_v2(pre)


def test_given_one_fresh_claim_when_applied_then_reference_inserts_one_owned_entry() -> None:
    # Arrange
    pre = CanonicalReferenceNullifierArchiveV2.empty()
    claim = _claim(7, 101)

    # Act
    result = apply_reference_object_nullifiers_v2(pre, (claim,))

    # Assert
    assert type(result) is ReferenceAcceptedV2
    assert result.post_archive is not pre
    assert result.post_archive.entries == (_entry(7, 101),)
    assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)
    assert result.post_reference_archive_digest == reference_archive_digest_v2(
        result.post_archive
    )


@pytest.mark.parametrize("claim_count", [0, 1, 63, 64, 65])
def test_claim_count_bva_0_1_63_64_65(claim_count: int) -> None:
    # Arrange
    pre = CanonicalReferenceNullifierArchiveV2.empty()
    claims = tuple(_claim(index, 1_000 + index) for index in range(1, claim_count + 1))

    # Act
    result = apply_reference_object_nullifiers_v2(pre, claims)

    # Assert
    if claim_count <= MAX_REFERENCE_CLAIMS_PER_STEP_V2:
        assert type(result) is ReferenceAcceptedV2
        assert len(result.post_archive.entries) == claim_count
    else:
        assert type(result) is ReferenceRejectedV2
        assert result.code is ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED
        assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)


def test_archive_count_bva_4095_4096_4097() -> None:
    # Arrange
    at_4095 = _archive(MAX_REFERENCE_NULLIFIERS_V2 - 1)
    at_4096 = _archive(MAX_REFERENCE_NULLIFIERS_V2)
    fresh = _claim(MAX_REFERENCE_NULLIFIERS_V2 + 1, 99_999)

    # Act
    accepted_4096 = apply_reference_object_nullifiers_v2(at_4095, (fresh,))
    identity_4096 = apply_reference_object_nullifiers_v2(at_4096, ())
    rejected_4097 = apply_reference_object_nullifiers_v2(at_4096, (fresh,))

    # Assert
    assert type(accepted_4096) is ReferenceAcceptedV2
    assert len(accepted_4096.post_archive.entries) == MAX_REFERENCE_NULLIFIERS_V2
    assert type(identity_4096) is ReferenceAcceptedV2
    assert identity_4096.post_archive == at_4096
    assert identity_4096.post_archive is not at_4096
    assert type(rejected_4097) is ReferenceRejectedV2
    assert rejected_4097.code is ReferenceRejectCodeV2.REFERENCE_ARCHIVE_CAPACITY_EXCEEDED
    assert rejected_4097.pre_reference_archive_digest == reference_archive_digest_v2(
        at_4096
    )


@pytest.mark.parametrize(
    "invalid",
    [
        "0x" + "0" * 64,
        "0X" + "1" * 64,
        "0x" + "A" * 64,
        "0x01",
        "0x" + "g" * 64,
        "1" * 64,
    ],
)
def test_canonical_ids_reject_zero_uppercase_short_and_nonhex(invalid: str) -> None:
    with pytest.raises(ValueError):
        ReferenceObjectIdV2(invalid)
    with pytest.raises(ValueError):
        ReferenceOccurrenceIdV2(invalid)


def test_step_limit_precedes_duplicate_historical_and_capacity() -> None:
    # Arrange
    pre = _archive(MAX_REFERENCE_NULLIFIERS_V2)
    claims = tuple(_claim(1, 70_000 + index) for index in range(65))

    # Act
    result = apply_reference_object_nullifiers_v2(pre, claims)

    # Assert
    assert type(result) is ReferenceRejectedV2
    assert result.code is ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED
    assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)


def test_duplicate_in_batch_precedes_historical_and_capacity_with_exact_noop() -> None:
    # Arrange
    pre = _archive(MAX_REFERENCE_NULLIFIERS_V2)
    pre_bytes = canonical_reference_archive_bytes_v2(pre)
    claims = (_claim(1, 80_001), _claim(1, 80_002))

    # Act
    result = apply_reference_object_nullifiers_v2(pre, claims)

    # Assert
    assert type(result) is ReferenceRejectedV2
    assert result.code is ReferenceRejectCodeV2.REFERENCE_DUPLICATE_IN_BATCH
    assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)
    assert not hasattr(result, "post_archive")
    assert canonical_reference_archive_bytes_v2(pre) == pre_bytes


def test_already_consumed_precedes_capacity_with_exact_noop() -> None:
    # Arrange
    pre = _archive(MAX_REFERENCE_NULLIFIERS_V2)
    pre_bytes = canonical_reference_archive_bytes_v2(pre)

    # Act
    result = apply_reference_object_nullifiers_v2(pre, (_claim(1, 81_001),))

    # Assert
    assert type(result) is ReferenceRejectedV2
    assert result.code is ReferenceRejectCodeV2.REFERENCE_ALREADY_CONSUMED
    assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)
    assert result.diagnostic == "reference step includes a previously consumed object"
    assert not hasattr(result, "post_archive")
    assert canonical_reference_archive_bytes_v2(pre) == pre_bytes


def test_capacity_rejection_is_exact_noop() -> None:
    # Arrange
    pre = _archive(MAX_REFERENCE_NULLIFIERS_V2)
    pre_bytes = canonical_reference_archive_bytes_v2(pre)
    fresh = _claim(MAX_REFERENCE_NULLIFIERS_V2 + 1, 82_001)

    # Act
    result = apply_reference_object_nullifiers_v2(pre, (fresh,))

    # Assert
    assert type(result) is ReferenceRejectedV2
    assert result.code is ReferenceRejectCodeV2.REFERENCE_ARCHIVE_CAPACITY_EXCEEDED
    assert result.diagnostic == "reference archive successor exceeds 4096 entries"
    assert not hasattr(result, "post_archive")
    assert canonical_reference_archive_bytes_v2(pre) == pre_bytes


def test_claim_permutations_have_identical_bytes_digest_and_outcome() -> None:
    # Arrange
    pre = CanonicalReferenceNullifierArchiveV2.empty()
    claims = (_claim(3, 103), _claim(1, 101), _claim(2, 102))

    # Act
    results = tuple(
        apply_reference_object_nullifiers_v2(pre, permutation)
        for permutation in itertools.permutations(claims)
    )

    # Assert
    assert all(type(result) is ReferenceAcceptedV2 for result in results)
    archives = tuple(result.post_archive for result in results if type(result) is ReferenceAcceptedV2)
    assert len({canonical_reference_archive_bytes_v2(archive) for archive in archives}) == 1
    assert len({reference_archive_digest_v2(archive) for archive in archives}) == 1


def test_three_step_history_rejects_reuse_and_matches_independent_set_model() -> None:
    # Arrange
    archive = CanonicalReferenceNullifierArchiveV2.empty()
    model: dict[str, str] = {}
    steps = ((_claim(2, 102),), (_claim(1, 101), _claim(3, 103)), (_claim(2, 202),))

    # Act / Assert
    for claims in steps:
        raw_claims = tuple(
            (claim.object_id.value, claim.consumed_by_occurrence_id.value)
            for claim in claims
        )
        expected = _independent_model(model, raw_claims)
        result = apply_reference_object_nullifiers_v2(archive, claims)
        assert _result_projection(result) == expected
        if type(result) is ReferenceAcceptedV2:
            archive = result.post_archive
            model = expected[2] or {}


def test_bounded_small_traces_match_independent_executable_model() -> None:
    # Arrange / Act / Assert
    six_claims = tuple(_claim(index, 1_000 + index) for index in range(1, 7))
    for length in range(7):
        for claims in itertools.permutations(six_claims, length):
            raw_claims = tuple(
                (claim.object_id.value, claim.consumed_by_occurrence_id.value)
                for claim in claims
            )
            expected = _independent_model({}, raw_claims)
            result = apply_reference_object_nullifiers_v2(
                CanonicalReferenceNullifierArchiveV2.empty(), claims
            )
            assert _result_projection(result) == expected

    duplicate = (_claim(1, 101), _claim(1, 201))
    assert _result_projection(
        apply_reference_object_nullifiers_v2(
            CanonicalReferenceNullifierArchiveV2.empty(), duplicate
        )
    ) == _independent_model(
        {},
        tuple(
            (claim.object_id.value, claim.consumed_by_occurrence_id.value)
            for claim in duplicate
        ),
    )


def test_reference_archive_bytes_stay_below_redundant_hard_byte_ceiling() -> None:
    # Arrange
    full = _archive(MAX_REFERENCE_NULLIFIERS_V2)

    # Act
    canonical_bytes = canonical_reference_archive_bytes_v2(full)

    # Assert
    assert len(canonical_bytes) < MAX_REFERENCE_ARCHIVE_BYTES_V2


def test_rejection_projection_binds_every_reachable_code_digest_and_diagnostic() -> None:
    # Arrange
    empty = CanonicalReferenceNullifierArchiveV2.empty()
    full = _archive(MAX_REFERENCE_NULLIFIERS_V2)
    cases = (
        (
            empty,
            tuple(_claim(index, 30_000 + index) for index in range(1, 66)),
            ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED,
            "reference step claim count exceeds 64",
        ),
        (
            empty,
            (_claim(1, 101), _claim(1, 102)),
            ReferenceRejectCodeV2.REFERENCE_DUPLICATE_IN_BATCH,
            "reference step repeats an object identifier",
        ),
        (
            _archive(1),
            (_claim(1, 102),),
            ReferenceRejectCodeV2.REFERENCE_ALREADY_CONSUMED,
            "reference step includes a previously consumed object",
        ),
        (
            full,
            (_claim(MAX_REFERENCE_NULLIFIERS_V2 + 1, 90_001),),
            ReferenceRejectCodeV2.REFERENCE_ARCHIVE_CAPACITY_EXCEEDED,
            "reference archive successor exceeds 4096 entries",
        ),
    )

    # Act / Assert
    for pre, claims, code, diagnostic in cases:
        result = apply_reference_object_nullifiers_v2(pre, claims)
        assert type(result) is ReferenceRejectedV2
        assert result.code is code
        assert result.pre_reference_archive_digest == reference_archive_digest_v2(pre)
        assert result.diagnostic == diagnostic
        assert not hasattr(result, "post_archive")


def test_transition_snapshots_retained_aliases_and_checks_limit_before_elements() -> None:
    # Arrange
    pre = _archive(1)
    claim_object_id = _object_id(2)
    claim_occurrence_id = _occurrence_id(102)
    claim = ReferenceConsumptionClaimV2(claim_object_id, claim_occurrence_id)
    result = apply_reference_object_nullifiers_v2(pre, (claim,))
    assert type(result) is ReferenceAcceptedV2
    accepted_digest = result.post_reference_archive_digest
    direct_object_id = _object_id(8)
    direct_occurrence_id = _occurrence_id(108)
    direct_archive = CanonicalReferenceNullifierArchiveV2(
        (
            ReferenceNullifierEntryV2(
                direct_object_id,
                direct_occurrence_id,
            ),
        )
    )
    direct_digest = reference_archive_digest_v2(direct_archive)

    # Act
    object.__setattr__(claim.object_id, "value", _hex_id(3))
    object.__setattr__(claim_occurrence_id, "value", _hex_id(103))
    object.__setattr__(pre.entries[0].object_id, "value", _hex_id(4))
    object.__setattr__(pre.entries[0].first_consumed_by_occurrence_id, "value", _hex_id(104))
    object.__setattr__(direct_object_id, "value", _hex_id(9))
    object.__setattr__(direct_occurrence_id, "value", _hex_id(109))
    oversized_hostile = tuple(object() for _ in range(65))
    limited = apply_reference_object_nullifiers_v2(
        CanonicalReferenceNullifierArchiveV2.empty(), oversized_hostile  # type: ignore[arg-type]
    )

    # Assert
    assert result.post_reference_archive_digest == accepted_digest
    assert reference_archive_digest_v2(direct_archive) == direct_digest
    assert type(limited) is ReferenceRejectedV2
    assert limited.code is ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED


def _archive_from_raw(rows: list[dict[str, str]]) -> CanonicalReferenceNullifierArchiveV2:
    for row in rows:
        _require_exact_keys(
            row,
            {"first_consumed_by_occurrence_id", "object_id"},
            context="golden pre/post entry",
        )
    return CanonicalReferenceNullifierArchiveV2(
        entries=tuple(
            ReferenceNullifierEntryV2(
                object_id=ReferenceObjectIdV2(row["object_id"]),
                first_consumed_by_occurrence_id=ReferenceOccurrenceIdV2(
                    row["first_consumed_by_occurrence_id"]
                ),
            )
            for row in rows
        )
    )


def _claims_from_raw(rows: list[dict[str, str]]) -> tuple[ReferenceConsumptionClaimV2, ...]:
    for row in rows:
        _require_exact_keys(
            row,
            {"consumed_by_occurrence_id", "object_id"},
            context="golden claim",
        )
    return tuple(
        ReferenceConsumptionClaimV2(
            object_id=ReferenceObjectIdV2(row["object_id"]),
            consumed_by_occurrence_id=ReferenceOccurrenceIdV2(
                row["consumed_by_occurrence_id"]
            ),
        )
        for row in rows
    )


def _require_exact_keys(
    row: dict[str, object], expected: set[str], *, context: str
) -> None:
    actual = set(row)
    if actual != expected:
        raise ValueError(
            f"{context} fields differ: missing={sorted(expected - actual)} "
            f"unknown={sorted(actual - expected)}"
        )


def _validate_golden_fixture_shape(fixture: dict[str, object]) -> None:
    _require_exact_keys(
        fixture,
        {
        "digest_prefix_hex",
        "limits",
        "reference_schema",
        "schema",
        "vectors",
        },
        context="golden root",
    )
    limits = fixture["limits"]
    if type(limits) is not dict:
        raise ValueError("golden limits must be an object")
    _require_exact_keys(
        limits,
        {"max_archive_bytes", "max_claims_per_step", "max_nullifiers"},
        context="golden limits",
    )
    vectors = fixture["vectors"]
    if type(vectors) is not list:
        raise ValueError("golden vectors must be a list")
    for vector in vectors:
        if type(vector) is not dict:
            raise ValueError("golden vector must be an object")
        _require_exact_keys(
            vector,
            {
                "claims",
                "expected",
                "name",
                "pre_canonical_json",
                "pre_entries",
                "pre_reference_archive_digest",
            },
            context="golden vector",
        )
        _archive_from_raw(vector["pre_entries"])
        _claims_from_raw(vector["claims"])
        expected = vector["expected"]
        if type(expected) is not dict:
            raise ValueError("golden expected value must be an object")
        expected_fields = (
            {
                "kind",
                "post_canonical_json",
                "post_entries",
                "post_reference_archive_digest",
            }
            if expected.get("kind") == "accepted"
            else {"code", "kind"}
        )
        _require_exact_keys(expected, expected_fields, context="golden expected")
        if expected.get("kind") == "accepted":
            _archive_from_raw(expected["post_entries"])


def test_python_reference_matches_committed_golden_bytes_digests_and_outcomes() -> None:
    # Arrange
    fixture = json.loads(
        GOLDEN_PATH.read_text(encoding="utf-8"),
        object_pairs_hook=_closed_json_object,
    )
    _validate_golden_fixture_shape(fixture)

    assert fixture["digest_prefix_hex"] == (
        b"global-economic-object-nullifier-reference\x002\x00".hex()
    )
    assert fixture["reference_schema"] == (
        "zenodex/global-economic-object-nullifier-reference/v2"
    )
    assert fixture["limits"] == {
        "max_archive_bytes": MAX_REFERENCE_ARCHIVE_BYTES_V2,
        "max_claims_per_step": MAX_REFERENCE_CLAIMS_PER_STEP_V2,
        "max_nullifiers": MAX_REFERENCE_NULLIFIERS_V2,
    }
    assert [vector["name"] for vector in fixture["vectors"]] == [
        "empty_identity",
        "insert_one",
        "insert_two_reverse",
        "duplicate_in_batch",
        "already_consumed",
    ]

    # Act / Assert
    for vector in fixture["vectors"]:
        pre = _archive_from_raw(vector["pre_entries"])
        assert canonical_reference_archive_bytes_v2(pre).decode("utf-8") == vector[
            "pre_canonical_json"
        ]
        assert reference_archive_digest_v2(pre) == vector[
            "pre_reference_archive_digest"
        ]
        result = apply_reference_object_nullifiers_v2(
            pre, _claims_from_raw(vector["claims"])
        )
        expected = vector["expected"]
        if expected["kind"] == "accepted":
            assert type(result) is ReferenceAcceptedV2
            assert canonical_reference_archive_bytes_v2(result.post_archive).decode(
                "utf-8"
            ) == expected["post_canonical_json"]
            assert result.post_reference_archive_digest == expected[
                "post_reference_archive_digest"
            ]
            assert [
                {
                    "first_consumed_by_occurrence_id": entry.first_consumed_by_occurrence_id.value,
                    "object_id": entry.object_id.value,
                }
                for entry in result.post_archive.entries
            ] == expected["post_entries"]
        else:
            assert type(result) is ReferenceRejectedV2
            assert result.code.value == expected["code"]
            assert not hasattr(result, "post_archive")


def test_python_golden_consumer_rejects_unknown_nested_fields() -> None:
    # Arrange
    fixture = json.loads(
        GOLDEN_PATH.read_text(encoding="utf-8"),
        object_pairs_hook=_closed_json_object,
    )
    fixture["vectors"][1]["claims"][0]["unknown"] = "forbidden"

    # Act / Assert
    with pytest.raises(ValueError, match="unknown=.*unknown"):
        _validate_golden_fixture_shape(fixture)


def _closed_json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


@contextmanager
def _loaded_mutant(old: str, new: str) -> Iterator[types.ModuleType]:
    source = SOURCE_PATH.read_text(encoding="utf-8")
    assert source.count(old) == 1, f"mutation anchor drift: {old!r}"
    mutated = source.replace(old, new)
    mutation_id = hashlib.sha256(old.encode("utf-8")).hexdigest()[:16]
    name = f"experiments._global_object_nullifier_mutant_{mutation_id}"
    module = types.ModuleType(name)
    module.__file__ = str(SOURCE_PATH)
    module.__package__ = "experiments"
    module.__spec__ = importlib.util.spec_from_loader(name, loader=None)
    sys.modules[name] = module
    try:
        exec(compile(mutated, str(SOURCE_PATH), "exec"), module.__dict__)
        yield module
    finally:
        sys.modules.pop(name, None)


def _mutant_step_limit_rejects_65(module: types.ModuleType) -> bool:
    pre = module.CanonicalReferenceNullifierArchiveV2.empty()
    claims = tuple(
        module.ReferenceConsumptionClaimV2(
            module.ReferenceObjectIdV2(_hex_id(index)),
            module.ReferenceOccurrenceIdV2(_hex_id(1_000 + index)),
        )
        for index in range(1, 66)
    )
    result = module.apply_reference_object_nullifiers_v2(pre, claims)
    return (
        type(result) is module.ReferenceRejectedV2
        and result.code
        is module.ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED
    )


def _mutant_duplicate_is_rejected(module: types.ModuleType) -> bool:
    pre = module.CanonicalReferenceNullifierArchiveV2.empty()
    object_id = module.ReferenceObjectIdV2(_hex_id(1))
    claims = (
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(101))
        ),
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(102))
        ),
    )
    result = module.apply_reference_object_nullifiers_v2(pre, claims)
    return (
        type(result) is module.ReferenceRejectedV2
        and result.code is module.ReferenceRejectCodeV2.REFERENCE_DUPLICATE_IN_BATCH
    )


def _mutant_historical_is_rejected(module: types.ModuleType) -> bool:
    object_id = module.ReferenceObjectIdV2(_hex_id(1))
    pre = module.CanonicalReferenceNullifierArchiveV2(
        (
            module.ReferenceNullifierEntryV2(
                object_id, module.ReferenceOccurrenceIdV2(_hex_id(101))
            ),
        )
    )
    claims = (
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(102))
        ),
    )
    result = module.apply_reference_object_nullifiers_v2(pre, claims)
    return (
        type(result) is module.ReferenceRejectedV2
        and result.code is module.ReferenceRejectCodeV2.REFERENCE_ALREADY_CONSUMED
    )


def _mutant_exact_capacity_accepts(module: types.ModuleType) -> bool:
    entries = tuple(
        module.ReferenceNullifierEntryV2(
            module.ReferenceObjectIdV2(_hex_id(index)),
            module.ReferenceOccurrenceIdV2(_hex_id(10_000 + index)),
        )
        for index in range(1, 4096)
    )
    pre = module.CanonicalReferenceNullifierArchiveV2(entries)
    claim = module.ReferenceConsumptionClaimV2(
        module.ReferenceObjectIdV2(_hex_id(4096)),
        module.ReferenceOccurrenceIdV2(_hex_id(20_000)),
    )
    return type(module.apply_reference_object_nullifiers_v2(pre, (claim,))) is module.ReferenceAcceptedV2


def _mutant_precedence_is_historical(module: types.ModuleType) -> bool:
    entries = tuple(
        module.ReferenceNullifierEntryV2(
            module.ReferenceObjectIdV2(_hex_id(index)),
            module.ReferenceOccurrenceIdV2(_hex_id(10_000 + index)),
        )
        for index in range(1, 4097)
    )
    pre = module.CanonicalReferenceNullifierArchiveV2(entries)
    claim = module.ReferenceConsumptionClaimV2(
        module.ReferenceObjectIdV2(_hex_id(1)),
        module.ReferenceOccurrenceIdV2(_hex_id(90_000)),
    )
    result = module.apply_reference_object_nullifiers_v2(pre, (claim,))
    return (
        type(result) is module.ReferenceRejectedV2
        and result.code is module.ReferenceRejectCodeV2.REFERENCE_ALREADY_CONSUMED
    )


def _mutant_rejection_has_no_successor(module: types.ModuleType) -> bool:
    pre = module.CanonicalReferenceNullifierArchiveV2.empty()
    object_id = module.ReferenceObjectIdV2(_hex_id(1))
    claims = (
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(101))
        ),
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(102))
        ),
    )
    result = module.apply_reference_object_nullifiers_v2(pre, claims)
    return type(result) is module.ReferenceRejectedV2 and not hasattr(result, "post_archive")


def _mutant_permutations_stable(module: types.ModuleType) -> bool:
    pre = module.CanonicalReferenceNullifierArchiveV2.empty()
    claims = tuple(
        module.ReferenceConsumptionClaimV2(
            module.ReferenceObjectIdV2(_hex_id(index)),
            module.ReferenceOccurrenceIdV2(_hex_id(100 + index)),
        )
        for index in (3, 1, 2)
    )
    digests: set[str] = set()
    for permutation in itertools.permutations(claims):
        result = module.apply_reference_object_nullifiers_v2(pre, permutation)
        if type(result) is not module.ReferenceAcceptedV2:
            return False
        digests.add(module.reference_archive_digest_v2(result.post_archive))
    return len(digests) == 1


def _mutant_occurrence_changes_digest(module: types.ModuleType) -> bool:
    object_id = module.ReferenceObjectIdV2(_hex_id(1))
    archives = tuple(
        module.CanonicalReferenceNullifierArchiveV2(
            (
                module.ReferenceNullifierEntryV2(
                    object_id, module.ReferenceOccurrenceIdV2(_hex_id(occurrence))
                ),
            )
        )
        for occurrence in (101, 102)
    )
    return len({module.reference_archive_digest_v2(archive) for archive in archives}) == 2


def _mutant_matches_empty_golden_digest(module: types.ModuleType) -> bool:
    fixture = json.loads(GOLDEN_PATH.read_text(encoding="utf-8"))
    expected = fixture["vectors"][0]["pre_reference_archive_digest"]
    return (
        module.reference_archive_digest_v2(
            module.CanonicalReferenceNullifierArchiveV2.empty()
        )
        == expected
    )


def _mutant_uppercase_rejects(module: types.ModuleType) -> bool:
    try:
        module.ReferenceObjectIdV2("0x" + "A" * 64)
    except ValueError:
        return True
    return False


def _mutant_empty_is_identity(module: types.ModuleType) -> bool:
    pre = module.CanonicalReferenceNullifierArchiveV2(
        (
            module.ReferenceNullifierEntryV2(
                module.ReferenceObjectIdV2(_hex_id(1)),
                module.ReferenceOccurrenceIdV2(_hex_id(101)),
            ),
        )
    )
    result = module.apply_reference_object_nullifiers_v2(pre, ())
    return (
        type(result) is module.ReferenceAcceptedV2
        and result.post_archive == pre
        and result.post_reference_archive_digest
        == module.reference_archive_digest_v2(pre)
    )


def _mutant_rejection_projection_is_bound(module: types.ModuleType) -> bool:
    pre = module.CanonicalReferenceNullifierArchiveV2.empty()
    object_id = module.ReferenceObjectIdV2(_hex_id(1))
    claims = (
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(101))
        ),
        module.ReferenceConsumptionClaimV2(
            object_id, module.ReferenceOccurrenceIdV2(_hex_id(102))
        ),
    )
    result = module.apply_reference_object_nullifiers_v2(pre, claims)
    return (
        type(result) is module.ReferenceRejectedV2
        and result.pre_reference_archive_digest
        == module.reference_archive_digest_v2(pre)
        and result.diagnostic == "reference step repeats an object identifier"
    )


_SEMANTIC_MUTANTS: tuple[
    tuple[str, str, Callable[[types.ModuleType], bool]], ...
] = (
        (
            "if claim_count > MAX_REFERENCE_CLAIMS_PER_STEP_V2:",
            "if False and claim_count > MAX_REFERENCE_CLAIMS_PER_STEP_V2:",
            _mutant_step_limit_rejects_65,
        ),
        (
            "if len(claim_by_object) != claim_count:",
            "if False and len(claim_by_object) != claim_count:",
            _mutant_duplicate_is_rejected,
        ),
        (
            "if any(object_id in consumed_ids for object_id in claim_by_object):",
            "if any(object_id in consumed_ids for object_id in claim_by_object):\n"
            "        return ReferenceAcceptedV2(\n"
            "            pre_reference_archive_digest=reference_archive_digest_v2(owned_pre_archive),\n"
            "            post_archive=owned_pre_archive,\n"
            "        )\n"
            "    if False:",
            _mutant_historical_is_rejected,
        ),
        (
            "if successor_count > MAX_REFERENCE_NULLIFIERS_V2:",
            "if successor_count >= MAX_REFERENCE_NULLIFIERS_V2:",
            _mutant_exact_capacity_accepts,
        ),
        (
            "# MUTATION_ANCHOR:M05_HISTORICAL_BEFORE_CAPACITY",
            "# MUTATION_ANCHOR:M05_HISTORICAL_BEFORE_CAPACITY\n"
            "    if claim_count and len(pre_archive.entries) >= MAX_REFERENCE_NULLIFIERS_V2:\n"
            "        return _reject_reference_step_v2(\n"
            "            pre_archive,\n"
            "            ReferenceRejectCodeV2.REFERENCE_ARCHIVE_CAPACITY_EXCEEDED,\n"
            "            'mutated early capacity rejection',\n"
            "        )",
            _mutant_precedence_is_historical,
        ),
        (
            "return ReferenceRejectedV2(",
            "return ReferenceAcceptedV2(\n        pre_reference_archive_digest=pre_digest,\n        post_archive=CanonicalReferenceNullifierArchiveV2(tuple(pre_archive.entries)),\n    )\n    return ReferenceRejectedV2(",
            _mutant_rejection_has_no_successor,
        ),
        (
            "key=lambda entry: entry.object_id.decoded_bytes,",
            "key=lambda entry: b'',",
            _mutant_permutations_stable,
        ),
        (
            '"first_consumed_by_occurrence_id": entry.first_consumed_by_occurrence_id.value,',
            '"first_consumed_by_occurrence_id": "0x" + "0" * 64,',
            _mutant_occurrence_changes_digest,
        ),
        (
            "REFERENCE_DIGEST_PREFIX_V2 = REFERENCE_DIGEST_DOMAIN_V2 + b\"\\x00\" + b\"2\\x00\"",
            "REFERENCE_DIGEST_PREFIX_V2 = REFERENCE_DIGEST_DOMAIN_V2 + b\"\\x00\"",
            _mutant_matches_empty_golden_digest,
        ),
        (
            "if _CANONICAL_ID_RE.fullmatch(value) is None:",
            "if False and _CANONICAL_ID_RE.fullmatch(value) is None:",
            _mutant_uppercase_rejects,
        ),
        (
            "post_archive=owned_pre_archive,  # Exact value no-op with owned data.",
            "post_archive=CanonicalReferenceNullifierArchiveV2.empty(),",
            _mutant_empty_is_identity,
        ),
        (
            "pre_digest = reference_archive_digest_v2(pre_archive)",
            "pre_digest = '0x' + '0' * 64",
            _mutant_rejection_projection_is_bound,
        ),
        (
            "diagnostic=diagnostic,",
            "diagnostic='corrupted diagnostic',",
            _mutant_rejection_projection_is_bound,
        ),
)


def test_named_reference_semantic_source_mutants_are_killed() -> None:
    # Arrange
    mutants = _SEMANTIC_MUTANTS

    # Act
    survivors: list[int] = []
    for index, (old, new, obligation) in enumerate(mutants, start=1):
        with _loaded_mutant(old, new) as module:
            try:
                survived = obligation(module)
            except ValueError:
                if index != 7:
                    raise
                survived = False
            if survived:
                survivors.append(index)

    # Assert
    assert survivors == []
