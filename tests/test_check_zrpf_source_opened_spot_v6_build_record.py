from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_build_record as checker


def _artifact_bytes(stage: str) -> bytes:
    return (f"bounded-test-elf:{stage}\n").encode()


def valid_record() -> dict:
    programs = []
    for stage, package, artifact_file, image_id, child_stage, child_image_id in (
        checker.PROGRAM_SPECS
    ):
        raw = _artifact_bytes(stage)
        programs.append(
            {
                "stage": stage,
                "package": package,
                "artifact_file": artifact_file,
                "raw_elf_bytes": len(raw),
                "raw_elf_sha256": hashlib.sha256(raw).hexdigest(),
                "image_id_hex": image_id,
                "image_id_words_le": checker._image_words_le(image_id),
                "verified_child_stage": child_stage,
                "verified_child_image_id": child_image_id,
            }
        )
    return {
        "schema": checker.RECORD_SCHEMA,
        "recorded_at": "2026-07-12",
        "source_snapshot": {
            "repository_commit": "1" * 40,
            "repository_tree": "2" * 40,
            "repository_dirty": True,
            "source_root_sha256": "3" * 64,
            "source_file_count": 123,
            "source_bytes": 456_789,
        },
        "toolchain": {
            "rustc": "rustc 1.88.0",
            "cargo": "cargo 1.88.0",
            "r0vm": "r0vm 3.0.3",
            "cargo_risczero": "cargo-risczero 3.0.4",
            "risc0_zkvm": "3.0.5",
            "cargo_lock_sha256": "4" * 64,
            "target": "riscv32im-risc0-zkvm-elf",
            "build_jobs": 2,
            "offline": True,
            "locked": True,
        },
        "programs": programs,
        "executed_commands": {
            field: True for field in sorted(checker.EXECUTED_COMMAND_FIELDS)
        },
        "claims": {
            **{field: True for field in sorted(checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(checker.FALSE_CLAIMS)},
        },
    }


def test_valid_build_record_binds_current_policy_chain() -> None:
    document = valid_record()
    raw = checker.canonical_bytes(document)

    report = checker.validate_record(document, raw)

    assert report["ok"] is True
    assert report["policy_dependencies_checked"] == 5
    assert report["external_artifact_files_checked"] == 0
    assert report["leaf_image_id"] == checker.LEAF_IMAGE_ID
    assert report["settlement_image_id"] == checker.SETTLEMENT_IMAGE_ID
    assert report["proofs_generated"] is False
    assert report["production_authority"] is False


def test_optional_artifact_directory_rechecks_all_four_elfs(tmp_path: Path) -> None:
    document = valid_record()
    for row in document["programs"]:
        (tmp_path / row["artifact_file"]).write_bytes(_artifact_bytes(row["stage"]))

    report = checker.validate_record(
        document,
        checker.canonical_bytes(document),
        artifact_directory=tmp_path,
    )

    assert report["external_artifact_files_checked"] == 4


def test_optional_artifact_directory_rejects_mutation_and_symlink(
    tmp_path: Path,
) -> None:
    document = valid_record()
    for row in document["programs"]:
        (tmp_path / row["artifact_file"]).write_bytes(_artifact_bytes(row["stage"]))
    first = document["programs"][0]["artifact_file"]
    (tmp_path / first).write_bytes(b"mutated")
    with pytest.raises(checker.BuildRecordError, match="identity mismatch"):
        checker.validate_record(
            document,
            checker.canonical_bytes(document),
            artifact_directory=tmp_path,
        )

    (tmp_path / first).unlink()
    (tmp_path / "target.elf").write_bytes(_artifact_bytes(document["programs"][0]["stage"]))
    (tmp_path / first).symlink_to("target.elf")
    with pytest.raises(checker.BuildRecordError, match="symlink rejected"):
        checker.validate_record(
            document,
            checker.canonical_bytes(document),
            artifact_directory=tmp_path,
        )


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda value: value["programs"][1].__setitem__(
                "verified_child_image_id", "0" * 64
            ),
            "verified_child_image_id mismatch",
        ),
        (
            lambda value: value["programs"][0].__setitem__(
                "image_id_hex", "0" * 64
            ),
            "image_id_hex mismatch",
        ),
        (
            lambda value: value["programs"][0].__setitem__(
                "image_id_words_le", [0] * 8
            ),
            "image_id_words_le mismatch",
        ),
        (
            lambda value: value["executed_commands"].__setitem__(
                "risc0_guests_built", 1
            ),
            "must be exactly True",
        ),
        (
            lambda value: value["claims"].__setitem__(
                "production_authority", True
            ),
            "must be exactly False",
        ),
        (
            lambda value: value["toolchain"].__setitem__("unreviewed", True),
            "toolchain field set mismatch",
        ),
    ],
)
def test_validator_rejects_identity_boolean_claim_and_field_mutations(
    mutate,
    message: str,
) -> None:
    document = valid_record()
    mutate(document)

    with pytest.raises(checker.BuildRecordError, match=message):
        checker.validate_record(document, checker.canonical_bytes(document))


@pytest.mark.parametrize(
    "raw",
    [
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":1.0}\n',
        b'{"schema":NaN}\n',
    ],
)
def test_loader_rejects_ambiguous_or_floating_json(tmp_path: Path, raw: bytes) -> None:
    path = tmp_path / "record.json"
    path.write_bytes(raw)

    with pytest.raises(checker.BuildRecordError):
        checker.load_record(path)


def test_loader_rejects_equivalent_noncanonical_json(tmp_path: Path) -> None:
    document = valid_record()
    path = tmp_path / "record.json"
    path.write_text(json.dumps(document), encoding="utf-8")

    with pytest.raises(checker.BuildRecordError, match="noncanonical"):
        checker.load_record(path)


def test_supplied_record_anchor_rejects_coherent_mutation() -> None:
    document = valid_record()
    raw = checker.canonical_bytes(document)
    expected = hashlib.sha256(raw).hexdigest()
    changed = copy.deepcopy(document)
    changed["recorded_at"] = "2026-07-13"

    with pytest.raises(checker.BuildRecordError, match="supplied anchor"):
        checker.validate_record(
            changed,
            checker.canonical_bytes(changed),
            expected_record_sha256=expected,
        )
