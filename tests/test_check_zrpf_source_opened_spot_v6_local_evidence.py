from __future__ import annotations

import copy
import hashlib
import json
import subprocess
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
from tools import check_zrpf_source_opened_spot_v6_local_evidence as checker


def artifact_bytes() -> dict[str, bytes]:
    raw = {
        artifact_id: (f"bounded-v6-artifact:{artifact_id}\n").encode()
        for artifact_id, _path, _kind in checker.ARTIFACT_SPECS
    }
    for artifact_id, _path, kind in checker.ARTIFACT_SPECS:
        if kind == "risc0_program_binary":
            raw[artifact_id] = b"R0BF\x01\x00\x00\x00" + raw[artifact_id]
    receipt = {
        "inner": {"Succinct": {"seal": [10, 20, 30]}},
        "journal": {},
        "metadata": {},
    }
    mutation = copy.deepcopy(receipt)
    mutation["inner"]["Succinct"]["seal"][1] = 21
    receipt_raw = json.dumps(receipt, separators=(",", ":")).encode()
    mutation_raw = json.dumps(mutation, separators=(",", ":")).encode()
    for artifact_id in (
        "leaf_receipt",
        "l1_receipt",
        "l2_receipt",
        "settlement_receipt",
    ):
        raw[artifact_id] = receipt_raw
    for artifact_id in (
        "leaf_mutation_receipt",
        "l1_mutation_receipt",
        "l2_mutation_receipt",
        "settlement_mutation_receipt",
    ):
        raw[artifact_id] = mutation_raw
    digest = {key: hashlib.sha256(value).hexdigest() for key, value in raw.items()}
    external = {
        "ok": True,
        "schema": "zenodex.source_opened_spot_settlement_verifier_v6.response.v1",
        "verified_settlement_admission": {
            "receipt_sha256": digest["settlement_receipt"],
            "guest_input_sha256": digest["settlement_guest_input"],
            "admission_journal_sha256": digest["settlement_admission_journal"],
        },
    }
    raw["external_verifier_output"] = (json.dumps(external, separators=(",", ":")) + "\n").encode()
    chain = {
        "ok": True,
        "schema": "zenodex.source_opened_spot_v6_chain_verifier.response.v1",
        "positive_receipts_verified": 4,
        "exact_seal_mutations_rejected": 4,
        "fake_receipt_rejected": True,
        "receipt_profile_id": checker.SUCCINCT_PROFILE_ID,
        "leaf_receipt_sha256": digest["leaf_receipt"],
        "level_one_receipt_sha256": digest["l1_receipt"],
        "level_two_receipt_sha256": digest["l2_receipt"],
        "settlement_receipt_sha256": digest["settlement_receipt"],
        "settlement_claim_binding": "a" * 64,
        "settlement_admission_journal_sha256": digest["settlement_admission_journal"],
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }
    raw["chain_verifier_output"] = (json.dumps(chain, separators=(",", ":")) + "\n").encode()
    return raw


def _program_artifact_bytes_by_path(raw_artifacts: dict[str, bytes]) -> dict[str, bytes]:
    return {
        path: raw_artifacts[artifact_id]
        for artifact_id, path, kind in checker.ARTIFACT_SPECS
        if kind == "risc0_program_binary"
    }


def _write_artifacts(directory: Path, raw_artifacts: dict[str, bytes]) -> None:
    for artifact_id, path, _kind in checker.ARTIFACT_SPECS:
        (directory / path).write_bytes(raw_artifacts[artifact_id])


def _install_fake_r0vm(directory: Path, document: dict) -> Path:
    artifact_id_by_path = {
        path: artifact_id
        for artifact_id, path, kind in checker.ARTIFACT_SPECS
        if kind == "risc0_program_binary"
    }
    image_ids = {
        artifact_id_by_path[row["artifact_file"]]: row["image_id_hex"]
        for row in document["programs"]
    }
    r0vm = directory / "r0vm"
    r0vm.write_text(
        "#!/usr/bin/python3\n"
        "import sys\n"
        f"images = {image_ids!r}\n"
        "if len(sys.argv) != 4 or sys.argv[1] != '--elf' or sys.argv[3] != '--id':\n"
        "    raise SystemExit(2)\n"
        "raw = open(sys.argv[2], 'rb').read()\n"
        "artifact_id = raw.split(b'bounded-v6-artifact:', 1)[1].strip().decode()\n"
        "print(images[artifact_id])\n",
        encoding="utf-8",
    )
    r0vm.chmod(0o755)
    document["toolchain"]["r0vm"] = (
        "risc0-r0vm 3.0.5 sha256:" + hashlib.sha256(r0vm.read_bytes()).hexdigest()
    )
    return r0vm


def _bind_evidence_program_artifacts(
    evidence: dict,
    raw_programs_by_path: dict[str, bytes],
) -> None:
    for row in evidence["artifacts"]:
        raw = raw_programs_by_path.get(row["path"])
        if raw is not None:
            row["size_bytes"] = len(raw)
            row["sha256"] = hashlib.sha256(raw).hexdigest()


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
                "mutation_receipt_sha256": facts["leaf_mutation_receipt"]["sha256"],
                "mutation_rejected": True,
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
                "mutation_receipt_sha256": facts["l1_mutation_receipt"]["sha256"],
                "mutation_rejected": True,
                "verified_child_count": 1,
            },
            "level_two": {
                "ok": True,
                "image_id": build_checker.L2_IMAGE_ID,
                "child_receipt_sha256": facts["l1_receipt"]["sha256"],
                "receipt_sha256": facts["l2_receipt"]["sha256"],
                "mutation_receipt_sha256": facts["l2_mutation_receipt"]["sha256"],
                "mutation_rejected": True,
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
                "data_availability_certificate_sha256": facts["settlement_da_certificate"][
                    "sha256"
                ],
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
                "chain_output_sha256": facts["chain_verifier_output"]["sha256"],
                "ambient_dev_chain_output_sha256": facts["chain_verifier_output"]["sha256"],
                "normal_dev_outputs_equal": True,
                "fake_receipt_rejected": True,
                "positive_receipts_verified": 4,
                "exact_seal_mutations_rejected": 4,
                "mutation_receipt_sha256": facts["settlement_mutation_receipt"]["sha256"],
                "mutation_rejected": True,
                "mutation_error_code": checker.MUTATION_ERROR_CODE,
            },
        },
        "executed_commands": {field: True for field in sorted(checker.EXECUTED_COMMAND_FIELDS)},
        "claims": {
            **{field: True for field in sorted(checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(checker.FALSE_CLAIMS)},
        },
    }


def valid_build_record() -> dict:
    commit = subprocess.check_output(
        ["git", "-C", str(build_checker.REPO_ROOT), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    tree = subprocess.check_output(
        ["git", "-C", str(build_checker.REPO_ROOT), "rev-parse", "HEAD^{tree}"],
        text=True,
    ).strip()
    source_root, source_count, source_bytes = build_checker.compute_source_closure(
        build_checker.REPO_ROOT
    )
    program_artifacts = _program_artifact_bytes_by_path(artifact_bytes())
    programs = []
    for (
        stage,
        package,
        artifact_file,
        image_id,
        child_stage,
        child_image_id,
    ) in build_checker.PROGRAM_SPECS:
        raw = program_artifacts[artifact_file]
        programs.append(
            {
                "stage": stage,
                "package": package,
                "artifact_file": artifact_file,
                "program_binary_bytes": len(raw),
                "program_binary_sha256": hashlib.sha256(raw).hexdigest(),
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
            "repository_commit": commit,
            "repository_tree": tree,
            "repository_dirty": False,
            "source_root_sha256": source_root,
            "source_file_count": source_count,
            "source_bytes": source_bytes,
        },
        "toolchain": {
            "rustc": "rustc 1.88.0",
            "cargo": "cargo 1.88.0",
            "r0vm": "risc0-r0vm 3.0.5 sha256:" + "5" * 64,
            "cargo_risczero": "cargo-risczero 3.0.5 sha256:" + "6" * 64,
            "risc0_zkvm": "3.0.5",
            "cargo_lock_sha256": hashlib.sha256(
                (build_checker.REPO_ROOT / build_checker.CARGO_LOCK_RELATIVE).read_bytes()
            ).hexdigest(),
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
    assert report["mutation_rejected"] is False
    assert report["scoped_local_replay_claim_allowed"] is False
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
    assert report["exact_mutation_relations_checked"] == 4
    assert report["verifier_transcripts_checked"] == 2
    assert report["mutation_rejected"] is True


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
    assert report["program_image_ids_recomputed"] == 0
    assert report["scoped_local_replay_claim_allowed"] is False


def test_scoped_claim_cross_binds_all_program_artifact_identities(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    raw_artifacts = artifact_bytes()
    _write_artifacts(tmp_path, raw_artifacts)
    build_document = valid_build_record()
    r0vm = _install_fake_r0vm(tmp_path, build_document)
    build_raw = build_checker.canonical_bytes(build_document)
    build_path = tmp_path / "build.json"
    build_path.write_bytes(build_raw)
    evidence = valid_evidence()
    evidence["build_record_sha256"] = hashlib.sha256(build_raw).hexdigest()
    evidence_raw = checker.canonical_bytes(evidence)
    monkeypatch.setattr(build_checker, "_validate_policy_sources", lambda _root: None)

    report = checker.validate_evidence(
        evidence,
        evidence_raw,
        artifact_directory=tmp_path,
        build_record_path=build_path,
        r0vm_path=r0vm.resolve(),
        expected_evidence_sha256=hashlib.sha256(evidence_raw).hexdigest(),
    )

    assert report["program_image_ids_recomputed"] == len(build_checker.PROGRAM_SPECS)
    assert report["program_artifact_bindings_checked"] == len(build_checker.PROGRAM_SPECS)
    assert report["scoped_local_replay_claim_allowed"] is True


def test_program_set_swap_after_build_validation_cannot_promote(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    initial_artifacts = artifact_bytes()
    _write_artifacts(tmp_path, initial_artifacts)
    build_document = valid_build_record()
    r0vm = _install_fake_r0vm(tmp_path, build_document)
    build_raw = build_checker.canonical_bytes(build_document)
    build_path = tmp_path / "build.json"
    build_path.write_bytes(build_raw)

    alternative_programs = {
        path: raw[:-1] + bytes([raw[-1] ^ 1])
        for path, raw in _program_artifact_bytes_by_path(initial_artifacts).items()
    }
    evidence = valid_evidence()
    _bind_evidence_program_artifacts(evidence, alternative_programs)
    evidence["build_record_sha256"] = hashlib.sha256(build_raw).hexdigest()
    evidence_raw = checker.canonical_bytes(evidence)
    evidence_path = tmp_path / "evidence.json"
    evidence_path.write_bytes(evidence_raw)

    original_validate_record = build_checker.validate_record
    swapped = False

    def validate_then_swap(*args, **kwargs):
        nonlocal swapped
        report = original_validate_record(*args, **kwargs)
        for path, raw in alternative_programs.items():
            (tmp_path / path).write_bytes(raw)
        swapped = True
        return report

    monkeypatch.setattr(build_checker, "_validate_policy_sources", lambda _root: None)
    monkeypatch.setattr(build_checker, "validate_record", validate_then_swap)

    report = checker.check_evidence(
        evidence_path,
        artifact_directory=tmp_path,
        build_record_path=build_path,
        r0vm_path=r0vm.resolve(),
        expected_evidence_sha256=hashlib.sha256(evidence_raw).hexdigest(),
        require_scoped_claim=True,
    )

    assert swapped is True
    assert report["ok"] is False
    assert report["scoped_local_replay_claim_allowed"] is False
    assert report["errors"] == [
        "program artifact SHA-256 differs between evidence and build record: spot_value_leaf_v6"
    ]


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
            lambda value: value["stages"]["settlement"].__setitem__("l2_receipt_sha256", "0" * 64),
            "settlement L2 receipt SHA-256 mismatch",
        ),
        (
            lambda value: value["stages"]["external_verifier"].__setitem__(
                "mutation_error_code", "accepted"
            ),
            "mutation_error_code mismatch",
        ),
        (
            lambda value: value["executed_commands"].__setitem__("settlement_proving_executed", 1),
            "must be exactly True",
        ),
        (
            lambda value: value["claims"].__setitem__("settlement_authority", True),
            "must be exactly False",
        ),
        (
            lambda value: value["stages"]["leaf"].__setitem__("unreviewed", True),
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


@pytest.mark.parametrize("mutation_kind", ["metadata", "second_seal_word"])
def test_exact_seal_mutation_relation_rejects_coherent_extra_drift(
    mutation_kind: str,
) -> None:
    raw = artifact_bytes()
    source = raw["leaf_receipt"]
    candidate = json.loads(raw["leaf_mutation_receipt"])
    if mutation_kind == "metadata":
        candidate["metadata"]["unreviewed"] = True
    else:
        candidate["inner"]["Succinct"]["seal"][2] ^= 1
    candidate_raw = json.dumps(candidate, separators=(",", ":")).encode()

    with pytest.raises(checker.EvidenceError, match="outside seal word 1"):
        checker._validate_exact_succinct_seal_mutation(source, candidate_raw)


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


def test_cli_check_can_require_the_scoped_claim(tmp_path: Path) -> None:
    document = valid_evidence()
    path = tmp_path / "evidence.json"
    path.write_bytes(checker.canonical_bytes(document))

    report = checker.check_evidence(path, require_scoped_claim=True)

    assert report["ok"] is False
    assert report["scoped_local_replay_claim_allowed"] is False
    assert report["errors"] == ["scoped local replay claim is not established"]
