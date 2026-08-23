from __future__ import annotations

import ast
import json
from itertools import combinations, permutations
from pathlib import Path

import pytest

from experiments.global_economic_object_nullifier_reference_v2 import (
    CanonicalReferenceNullifierArchiveV2,
    ReferenceAcceptedV2,
    ReferenceConsumptionClaimV2,
    ReferenceNullifierEntryV2,
    ReferenceObjectIdV2,
    ReferenceOccurrenceIdV2,
    ReferenceRejectCodeV2,
    ReferenceRejectedV2,
    apply_reference_object_nullifiers_v2,
)
from experiments.global_economic_object_nullifier_reference_v2_jmt_adapter_v1 import (
    MAX_OBJECT_NULLIFIER_JMT_WITNESS_BYTES_V1,
    encode_reference_object_absence_witness_v1,
    encode_reference_object_membership_witness_v1,
    project_reference_archive_to_jmt_entries_v1,
    reference_archive_candidate_jmt_root_v1,
    verify_reference_object_absence_witness_v1,
    verify_reference_object_membership_witness_v1,
)
from tools.build_operator_release_bundle import ROOT as RELEASE_ROOT
from tools.build_operator_release_bundle import _collect_bundle_files

REPO_ROOT = Path(__file__).resolve().parents[2]
ADAPTER_MODULE_NAME = "global_economic_object_nullifier_reference_v2_jmt_adapter_v1"


def _hex_id(number: int) -> str:
    return "0x" + f"{number:064x}"


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


def _archive(count: int) -> CanonicalReferenceNullifierArchiveV2:
    return CanonicalReferenceNullifierArchiveV2(
        tuple(_entry(number, 100_000 + number) for number in range(1, count + 1))
    )


def _canonical_wire(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def test_projection_fixed_roots_and_bijection() -> None:
    # Arrange
    empty = CanonicalReferenceNullifierArchiveV2.empty()
    one = CanonicalReferenceNullifierArchiveV2((_entry(1, 101),))
    two = CanonicalReferenceNullifierArchiveV2((_entry(1, 101), _entry(2, 102)))

    # Act
    projected = project_reference_archive_to_jmt_entries_v1(two)
    roots = tuple(reference_archive_candidate_jmt_root_v1(value) for value in (empty, one, two))

    # Assert
    assert projected == (
        ((1).to_bytes(32, "big"), (101).to_bytes(32, "big")),
        ((2).to_bytes(32, "big"), (102).to_bytes(32, "big")),
    )
    assert len({key for key, _value in projected}) == len(two.entries)
    assert len({value for _key, value in projected}) == len(two.entries)
    assert roots == (
        "0xc46350b4a866d01c4cde13f40a0c1d97ac4f8d791deeda8a4df7e5e4a94ca48b",
        "0x8c7754ebc3f1bfd97ba7549dfb37b4b6a6736721a898bc30cf4659aba1edf6a4",
        "0xb7dc9a5aa9eee5311a18a0b88d5644aa3e28946c858e0711302e2e15e9a1c455",
    )


def test_accepted_steps_refine_map_and_proofs() -> None:
    # Arrange
    pre = CanonicalReferenceNullifierArchiveV2((_entry(1, 101), _entry(2, 102)))
    fresh = _object_id(3)
    pre_root = reference_archive_candidate_jmt_root_v1(pre)
    absence = encode_reference_object_absence_witness_v1(pre, fresh)
    claims = (_claim(4, 104), _claim(3, 103))

    # Act
    result = apply_reference_object_nullifiers_v2(pre, claims)

    # Assert
    assert isinstance(result, ReferenceAcceptedV2)
    assert verify_reference_object_absence_witness_v1(pre_root, fresh, absence)
    assert project_reference_archive_to_jmt_entries_v1(result.post_archive) == (
        ((1).to_bytes(32, "big"), (101).to_bytes(32, "big")),
        ((2).to_bytes(32, "big"), (102).to_bytes(32, "big")),
        ((3).to_bytes(32, "big"), (103).to_bytes(32, "big")),
        ((4).to_bytes(32, "big"), (104).to_bytes(32, "big")),
    )
    post_root = reference_archive_candidate_jmt_root_v1(result.post_archive)
    assert post_root != pre_root
    assert not verify_reference_object_absence_witness_v1(post_root, fresh, absence)
    for object_number, occurrence_number in ((1, 101), (2, 102), (3, 103), (4, 104)):
        witness = encode_reference_object_membership_witness_v1(
            result.post_archive,
            _object_id(object_number),
        )
        assert verify_reference_object_membership_witness_v1(
            post_root,
            _object_id(object_number),
            _occurrence_id(occurrence_number),
            witness,
        )
    new_witness = encode_reference_object_membership_witness_v1(result.post_archive, fresh)
    assert not verify_reference_object_membership_witness_v1(
        post_root,
        fresh,
        _occurrence_id(999),
        new_witness,
    )


@pytest.mark.parametrize(
    ("pre", "claims", "expected_code"),
    [
        (
            CanonicalReferenceNullifierArchiveV2.empty(),
            tuple(_claim(number, 1_000 + number) for number in range(1, 66)),
            ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED,
        ),
        (
            CanonicalReferenceNullifierArchiveV2.empty(),
            (_claim(1, 101), _claim(1, 102)),
            ReferenceRejectCodeV2.REFERENCE_DUPLICATE_IN_BATCH,
        ),
        (
            CanonicalReferenceNullifierArchiveV2((_entry(1, 101),)),
            (_claim(1, 999),),
            ReferenceRejectCodeV2.REFERENCE_ALREADY_CONSUMED,
        ),
    ],
)
def test_rejections_have_no_successor_and_preserve_pre_root(
    pre: CanonicalReferenceNullifierArchiveV2,
    claims: tuple[ReferenceConsumptionClaimV2, ...],
    expected_code: ReferenceRejectCodeV2,
) -> None:
    # Arrange
    pre_root = reference_archive_candidate_jmt_root_v1(pre)

    # Act
    result = apply_reference_object_nullifiers_v2(pre, claims)

    # Assert
    assert isinstance(result, ReferenceRejectedV2)
    assert result.code is expected_code
    assert not hasattr(result, "post_archive")
    assert reference_archive_candidate_jmt_root_v1(pre) == pre_root


def test_empty_and_permuted_steps_are_root_invariant() -> None:
    # Arrange
    pre = CanonicalReferenceNullifierArchiveV2((_entry(1, 101),))
    claims = tuple(_claim(number, 100 + number) for number in range(2, 6))
    pre_root = reference_archive_candidate_jmt_root_v1(pre)

    # Act
    empty = apply_reference_object_nullifiers_v2(pre, ())
    roots = {
        reference_archive_candidate_jmt_root_v1(result.post_archive)
        for permutation in permutations(claims)
        if isinstance(
            (result := apply_reference_object_nullifiers_v2(pre, permutation)),
            ReferenceAcceptedV2,
        )
    }

    # Assert
    assert isinstance(empty, ReferenceAcceptedV2)
    assert reference_archive_candidate_jmt_root_v1(empty.post_archive) == pre_root
    assert len(roots) == 1


def test_bounded_stateful_traces_match_independent_map() -> None:
    # Arrange
    archive = CanonicalReferenceNullifierArchiveV2.empty()
    independent: dict[bytes, bytes] = {}
    history = (
        (_claim(5, 105), _claim(1, 101)),
        (_claim(8, 108),),
        (_claim(3, 103), _claim(2, 102), _claim(13, 113)),
    )

    # Act / Assert
    for claims in history:
        result = apply_reference_object_nullifiers_v2(archive, claims)
        assert isinstance(result, ReferenceAcceptedV2)
        for claim in claims:
            independent[claim.object_id.decoded_bytes] = bytes.fromhex(
                claim.consumed_by_occurrence_id.value[2:]
            )
        archive = result.post_archive
        assert project_reference_archive_to_jmt_entries_v1(archive) == tuple(
            sorted(independent.items())
        )
        root = reference_archive_candidate_jmt_root_v1(archive)
        for key, value in independent.items():
            object_id = ReferenceObjectIdV2("0x" + key.hex())
            occurrence_id = ReferenceOccurrenceIdV2("0x" + value.hex())
            witness = encode_reference_object_membership_witness_v1(archive, object_id)
            assert verify_reference_object_membership_witness_v1(
                root,
                object_id,
                occurrence_id,
                witness,
            )


def test_exhaustive_six_id_subsets_and_permutations_refine_one_root_per_subset() -> None:
    # Arrange
    claims = tuple(_claim(number, 1_000 + number) for number in range(1, 7))

    # Act / Assert
    for subset_size in range(7):
        for subset in combinations(claims, subset_size):
            roots: set[str] = set()
            expected = tuple(
                sorted(
                    (
                        claim.object_id.decoded_bytes,
                        bytes.fromhex(claim.consumed_by_occurrence_id.value[2:]),
                    )
                    for claim in subset
                )
            )
            for permutation in permutations(subset):
                result = apply_reference_object_nullifiers_v2(
                    CanonicalReferenceNullifierArchiveV2.empty(),
                    permutation,
                )
                assert isinstance(result, ReferenceAcceptedV2)
                assert project_reference_archive_to_jmt_entries_v1(result.post_archive) == expected
                roots.add(reference_archive_candidate_jmt_root_v1(result.post_archive))
            assert len(roots) == 1


@pytest.mark.parametrize("claim_count", [0, 1, 63, 64, 65])
def test_claim_count_boundaries(claim_count: int) -> None:
    # Arrange
    claims = tuple(_claim(number, 10_000 + number) for number in range(1, claim_count + 1))

    # Act
    result = apply_reference_object_nullifiers_v2(
        CanonicalReferenceNullifierArchiveV2.empty(),
        claims,
    )

    # Assert
    if claim_count <= 64:
        assert isinstance(result, ReferenceAcceptedV2)
        assert len(project_reference_archive_to_jmt_entries_v1(result.post_archive)) == claim_count
    else:
        assert isinstance(result, ReferenceRejectedV2)
        assert result.code is ReferenceRejectCodeV2.REFERENCE_STEP_LIMIT_EXCEEDED


def test_archive_capacity_boundaries_4095_4096_and_attempted_4097() -> None:
    # Arrange
    at_4095 = _archive(4_095)
    root_4095 = reference_archive_candidate_jmt_root_v1(at_4095)

    # Act
    accepted = apply_reference_object_nullifiers_v2(at_4095, (_claim(4_096, 204_096),))

    # Assert
    assert isinstance(accepted, ReferenceAcceptedV2)
    root_4096 = reference_archive_candidate_jmt_root_v1(accepted.post_archive)
    assert root_4096 != root_4095
    rejected = apply_reference_object_nullifiers_v2(
        accepted.post_archive,
        (_claim(4_097, 204_097),),
    )
    assert isinstance(rejected, ReferenceRejectedV2)
    assert rejected.code is ReferenceRejectCodeV2.REFERENCE_ARCHIVE_CAPACITY_EXCEEDED
    assert reference_archive_candidate_jmt_root_v1(accepted.post_archive) == root_4096


def test_canonical_witness_payloads_tamper_fail_closed() -> None:
    # Arrange
    archive = CanonicalReferenceNullifierArchiveV2((_entry(1, 101), _entry(1 << 255, 202)))
    root = reference_archive_candidate_jmt_root_v1(archive)
    object_id = _object_id(1)
    occurrence_id = _occurrence_id(101)
    membership = encode_reference_object_membership_witness_v1(archive, object_id)
    absence_id = _object_id(2)
    absence = encode_reference_object_absence_witness_v1(archive, absence_id)
    membership_obj = json.loads(membership)
    sibling_hash = membership_obj["siblings"][0]["sibling_hash"]
    membership_obj["siblings"][0]["sibling_hash"] = (
        "0x" + ("0" if sibling_hash[2] != "0" else "1") + sibling_hash[3:]
    )
    one_bit_tamper = _canonical_wire(membership_obj)

    # Act / Assert
    assert verify_reference_object_membership_witness_v1(
        root, object_id, occurrence_id, membership
    )
    assert not verify_reference_object_membership_witness_v1(
        "0x" + "ff" * 32, object_id, occurrence_id, membership
    )
    assert not verify_reference_object_membership_witness_v1(
        root, _object_id(2), occurrence_id, membership
    )
    assert not verify_reference_object_membership_witness_v1(
        root, object_id, _occurrence_id(999), membership
    )
    assert not verify_reference_object_membership_witness_v1(
        root, object_id, occurrence_id, membership + b" "
    )
    assert not verify_reference_object_membership_witness_v1(
        root, object_id, occurrence_id, type("WitnessBytes", (bytes,), {})(membership)
    )
    assert not verify_reference_object_membership_witness_v1(
        root, object_id, occurrence_id, one_bit_tamper
    )
    assert not verify_reference_object_membership_witness_v1(
        root,
        object_id,
        occurrence_id,
        b"{" + b"x" * MAX_OBJECT_NULLIFIER_JMT_WITNESS_BYTES_V1,
    )
    assert verify_reference_object_absence_witness_v1(root, absence_id, absence)
    assert not verify_reference_object_absence_witness_v1(root, object_id, absence)
    assert not verify_reference_object_absence_witness_v1(root, absence_id, absence + b"\n")


def test_adapter_snapshots_aliases_and_rejects_forged_values() -> None:
    # Arrange
    source_entry = _entry(1, 101)
    archive = CanonicalReferenceNullifierArchiveV2((source_entry,))
    expected_root = reference_archive_candidate_jmt_root_v1(archive)
    object.__setattr__(source_entry.object_id, "value", _hex_id(9))
    forged_archive = object.__new__(CanonicalReferenceNullifierArchiveV2)
    forged_object_id = object.__new__(ReferenceObjectIdV2)
    object.__setattr__(forged_object_id, "value", 7)

    # Act / Assert
    assert reference_archive_candidate_jmt_root_v1(archive) == expected_root
    with pytest.raises(TypeError, match="archive entries are missing"):
        reference_archive_candidate_jmt_root_v1(forged_archive)
    assert not verify_reference_object_membership_witness_v1(
        expected_root,
        forged_object_id,
        _occurrence_id(101),
        encode_reference_object_membership_witness_v1(archive, _object_id(1)),
    )


def test_adjacent_nonzero_ids_record_256_sibling_negative_frontier() -> None:
    # Arrange
    archive = CanonicalReferenceNullifierArchiveV2((_entry(2, 102), _entry(3, 103)))

    # Act
    witness = encode_reference_object_membership_witness_v1(archive, _object_id(2))
    decoded = json.loads(witness)

    # Assert
    assert len(decoded["siblings"]) == 256
    assert len(witness) == 28_357
    assert len(witness) < MAX_OBJECT_NULLIFIER_JMT_WITNESS_BYTES_V1
    assert verify_reference_object_membership_witness_v1(
        reference_archive_candidate_jmt_root_v1(archive),
        _object_id(2),
        _occurrence_id(102),
        witness,
    )


def test_adapter_is_one_way_unmounted_and_release_excluded() -> None:
    # Arrange
    adapter_path = (
        REPO_ROOT
        / "experiments/global_economic_object_nullifier_reference_v2_jmt_adapter_v1.py"
    )
    tree = ast.parse(adapter_path.read_text(encoding="utf-8"))
    scanned_roots = tuple(
        REPO_ROOT / name
        for name in ("src", "config", "generated", "zk", "tools", "bin", ".github")
    )

    # Act
    direct_imports = {
        alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.Import)
        for alias in node.names
    }
    imported_names = {
        node.module: {alias.name for alias in node.names}
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module is not None
    }
    offenders: list[str] = []
    for root in scanned_roots:
        if not root.exists():
            continue
        for path in root.rglob("*"):
            if not path.is_file() or path.suffix not in {".json", ".py", ".rs", ".sh", ".toml"}:
                continue
            if ADAPTER_MODULE_NAME in path.read_text(encoding="utf-8", errors="strict"):
                offenders.append(path.relative_to(REPO_ROOT).as_posix())
    bundled = {item.relative_path for item in _collect_bundle_files(RELEASE_ROOT)}

    # Assert
    assert direct_imports == {"re"}
    assert imported_names == {
        "__future__": {"annotations"},
        "experiments.global_economic_object_nullifier_reference_v2": {
            "CanonicalReferenceNullifierArchiveV2",
            "ReferenceObjectIdV2",
            "ReferenceOccurrenceIdV2",
        },
        "src.state.jmt": {
            "compute_jmt_root",
            "decode_jmt_absence_proof",
            "decode_jmt_membership_proof",
            "encode_jmt_absence_proof",
            "encode_jmt_membership_proof",
            "prove_jmt_absence",
            "prove_jmt_membership",
            "verify_jmt_absence",
            "verify_jmt_membership",
        },
    }
    assert offenders == []
    assert (
        "experiments/global_economic_object_nullifier_reference_v2_jmt_adapter_v1.py"
        not in bundled
    )
    assert "!experiments" not in (REPO_ROOT / ".dockerignore").read_text(encoding="utf-8")
