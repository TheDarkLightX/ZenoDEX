from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
from tools import check_zrpf_source_opened_spot_v6_local_evidence as checker


def artifact_bytes() -> dict[str, bytes]:
    return {
        artifact_id: (f"bounded-v6-artifact:{artifact_id}\n").encode()
        for artifact_id, _path, _kind in checker.ARTIFACT_SPECS
    }


def valid_evidence() -> dict:
    raw_artifacts = artifact_bytes()
    artifacts = []
    facts = {}
    for artifact_id, path, kind in checker.ARTIFACT_SPECS:
        raw = raw_artifacts[artifact_id]
        row = {
            "id": artifact_id,
            "path": path,
            "kind": kind,
            "size_bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
        artifacts.append(row)
        facts[artifact_id] = row
    nonzero = "a" * 64
    return {
        "schema": checker.EVIDENCE_SCHEMA,
        "recorded_at": "2026-07-12",
        "build_record_sha256": "b" * 64,
        "images": {
            "source_spot_v1": build_checker.SOURCE_SPOT_IMAGE_ID,
            "adapter_v3": build_checker.ADAPTER_IMAGE_ID,
            "spot_value_leaf_v6": build_checker.LEAF_IMAGE_ID,
            "spot_value_aggregate_l1_v6": build_checker.L1_IMAGE_ID,
            "spot_value_aggregate_l2_v6": build_checker.L2_IMAGE_ID,
            "source_opened_spot_settlement_v6": build_checker.SETTLEMENT_IMAGE_ID,
        },
        "artifacts": artifacts,
        "stages": {
            "source_opening": {
                "ok": True,
                "source_image_id": build_checker.SOURCE_SPOT_IMAGE_ID,
                "source_program_sha256": "1" * 64,
                "source_cli_sha256": "2" * 64,
                "generator_sha256": "3" * 64,
                "r0vm_sha256": "4" * 64,
                "request_sha256": facts["source_request"]["sha256"],
                "proof_sha256": facts["source_proof"]["sha256"],
                "receipt_kind": "succinct",
            },
            "adapter": {
                "image_id": build_checker.ADAPTER_IMAGE_ID,
                "receipt_sha256": facts["adapter_receipt"]["sha256"],
                "receipt_kind": "succinct",
                "verified": True,
            },
            "leaf": {
                "ok": True,
                "image_id": build_checker.LEAF_IMAGE_ID,
                "receipt_sha256": facts["leaf_receipt"]["sha256"],
                "receipt_profile_id": checker.SUCCINCT_PROFILE_ID,
                "source_proof_sha256": facts["source_proof"]["sha256"],
                "adapter_receipt_sha256": facts["adapter_receipt"]["sha256"],
                "source_envelope_sha256": facts["leaf_source_envelope"]["sha256"],
                "verified_program_manifest_root": nonzero,
                "action_nullifier_root": "c" * 64,
                "statement_hash": "d" * 64,
            },
            "level_one": {
                "ok": True,
                "image_id": build_checker.L1_IMAGE_ID,
                "child_receipt_sha256": facts["leaf_receipt"]["sha256"],
                "receipt_sha256": facts["l1_receipt"]["sha256"],
                "verified_child_count": 1,
            },
            "level_two": {
                "ok": True,
                "image_id": build_checker.L2_IMAGE_ID,
                "child_receipt_sha256": facts["l1_receipt"]["sha256"],
                "receipt_sha256": facts["l2_receipt"]["sha256"],
                "verified_child_count": 1,
            },
            "settlement": {
                "ok": True,
                "image_id": build_checker.SETTLEMENT_IMAGE_ID,
                "l2_receipt_sha256": facts["l2_receipt"]["sha256"],
                "source_envelope_sha256": facts["leaf_source_envelope"]["sha256"],
                "receipt_sha256": facts["settlement_receipt"]["sha256"],
                "mutation_receipt_sha256": facts["settlement_mutation_receipt"]["sha256"],
                "mutation_rejected": True,
                "admission_journal_sha256": facts["settlement_admission_journal"]["sha256"],
                "guest_input_sha256": facts["settlement_guest_input"]["sha256"],
                "replay_sha256": facts["settlement_replay"]["sha256"],
                "data_availability_certificate_sha256": facts[
                    "settlement_da_certificate"
                ]["sha256"],
                "settlement_claim_binding": "e" * 64,
                "settlement_program_manifest_root": "f" * 64,
                "settlement_program_id": build_checker.SETTLEMENT_IMAGE_ID,
                "succinct_receipt_profile_id": checker.SUCCINCT_PROFILE_ID,
                "action_count": 1,
                "consumed_object_count": 1,
            },
            "external_verifier": {
                "positive_receipt_sha256": facts["settlement_receipt"]["sha256"],
                "positive_guest_input_sha256": facts["settlement_guest_input"]["sha256"],
                "positive_output_sha256": facts["external_verifier_output"]["sha256"],
                "mutation_receipt_sha256": facts["settlement_mutation_receipt"]["sha256"],
                "mutation_rejected": True,
                "mutation_error_code": checker.MUTATION_ERROR_CODE,
            },
        },
        "executed_commands": {
            field: True for field in sorted(checker.EXECUTED_COMMAND_FIELDS)
        },
        "claims": {
            **{field: True for field in sorted(checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(checker.FALSE_CLAIMS)},
        },
    }


def valid_build_record() -> dict:
    programs = []
    for stage, package, artifact_file, image_id, child_stage, child_image_id in (
        build_checker.PROGRAM_SPECS
    ):
        raw = (f"elf:{stage}").encode()
        programs.append(
            {
                "stage": stage,
                "package": package,
                "artifact_file": artifact_file,
                "raw_elf_bytes": len(raw),
                "raw_elf_sha256": hashlib.sha256(raw).hexdigest(),
                "image_id_hex": image_id,
                "image_id_words_le": build_checker._image_words_le(image_id),
                "verified_child_stage": child_stage,
                "verified_child_image_id": child_image_id,
            }
        )
    return {
        "schema": build_checker.RECORD_SCHEMA,
        "recorded_at": "2026-07-12",
        "source_snapshot": {
            "repository_commit": "1" * 40,
            "repository_tree": "2" * 40,
            "repository_dirty": True,
            "source_root_sha256": "3" * 64,
            "source_file_count": 10,
            "source_bytes": 100,
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
            field: True for field in sorted(build_checker.EXECUTED_COMMAND_FIELDS)
        },
        "claims": {
            **{field: True for field in sorted(build_checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(build_checker.FALSE_CLAIMS)},
        },
    }


def test_valid_evidence_binds_complete_singleton_dependency_chain() -> None:
    document = valid_evidence()

    report = checker.validate_evidence(document, checker.canonical_bytes(document))

    assert report["ok"] is True
    assert report["dependency_chain_verified"] is True
    assert report["mutation_rejected"] is True
    assert report["external_artifact_files_checked"] == 0
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False


def test_optional_artifact_directory_rechecks_all_files(tmp_path: Path) -> None:
    document = valid_evidence()
    raw_artifacts = artifact_bytes()
    for artifact_id, path, _kind in checker.ARTIFACT_SPECS:
        (tmp_path / path).write_bytes(raw_artifacts[artifact_id])

    report = checker.validate_evidence(
        document,
        checker.canonical_bytes(document),
        artifact_directory=tmp_path,
    )

    assert report["external_artifact_files_checked"] == len(checker.ARTIFACT_SPECS)


def test_optional_build_record_is_rechecked_and_hash_bound(tmp_path: Path) -> None:
    build_document = valid_build_record()
    build_raw = build_checker.canonical_bytes(build_document)
    build_path = tmp_path / "build.json"
    build_path.write_bytes(build_raw)
    evidence = valid_evidence()
    evidence["build_record_sha256"] = hashlib.sha256(build_raw).hexdigest()

    report = checker.validate_evidence(
        evidence,
        checker.canonical_bytes(evidence),
        build_record_path=build_path,
    )

    assert report["build_record_rechecked"] is True


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda value: value["stages"]["level_one"].__setitem__(
                "child_receipt_sha256", "0" * 64
            ),
            "level_one child receipt SHA-256 mismatch",
        ),
        (
            lambda value: value["stages"]["settlement"].__setitem__(
                "l2_receipt_sha256", "0" * 64
            ),
            "settlement L2 receipt SHA-256 mismatch",
        ),
        (
            lambda value: value["stages"]["external_verifier"].__setitem__(
                "mutation_error_code", "accepted"
            ),
            "mutation_error_code mismatch",
        ),
        (
            lambda value: value["executed_commands"].__setitem__(
                "settlement_proving_executed", 1
            ),
            "must be exactly True",
        ),
        (
            lambda value: value["claims"].__setitem__(
                "settlement_authority", True
            ),
            "must be exactly False",
        ),
        (
            lambda value: value["stages"]["leaf"].__setitem__(
                "unreviewed", True
            ),
            "stages.leaf field set mismatch",
        ),
    ],
)
def test_validator_rejects_dependency_command_claim_and_field_mutations(
    mutate,
    message: str,
) -> None:
    document = valid_evidence()
    mutate(document)

    with pytest.raises(checker.EvidenceError, match=message):
        checker.validate_evidence(document, checker.canonical_bytes(document))


def test_external_artifact_mutation_rejects(tmp_path: Path) -> None:
    document = valid_evidence()
    raw_artifacts = artifact_bytes()
    for artifact_id, path, _kind in checker.ARTIFACT_SPECS:
        (tmp_path / path).write_bytes(raw_artifacts[artifact_id])
    (tmp_path / checker.ARTIFACT_SPECS[-1][1]).write_bytes(b"mutated output")

    with pytest.raises(checker.EvidenceError, match="identity mismatch"):
        checker.validate_evidence(
            document,
            checker.canonical_bytes(document),
            artifact_directory=tmp_path,
        )


@pytest.mark.parametrize(
    "raw",
    [
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":1.0}\n',
        b'{"schema":Infinity}\n',
    ],
)
def test_loader_rejects_ambiguous_or_floating_json(tmp_path: Path, raw: bytes) -> None:
    path = tmp_path / "evidence.json"
    path.write_bytes(raw)

    with pytest.raises(checker.EvidenceError):
        checker.load_evidence(path)


def test_loader_rejects_noncanonical_equivalent_json(tmp_path: Path) -> None:
    document = valid_evidence()
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(document), encoding="utf-8")

    with pytest.raises(checker.EvidenceError, match="noncanonical"):
        checker.load_evidence(path)


def test_supplied_evidence_anchor_rejects_coherent_change() -> None:
    document = valid_evidence()
    raw = checker.canonical_bytes(document)
    expected = hashlib.sha256(raw).hexdigest()
    changed = copy.deepcopy(document)
    changed["recorded_at"] = "2026-07-13"

    with pytest.raises(checker.EvidenceError, match="supplied anchor"):
        checker.validate_evidence(
            changed,
            checker.canonical_bytes(changed),
            expected_evidence_sha256=expected,
        )
