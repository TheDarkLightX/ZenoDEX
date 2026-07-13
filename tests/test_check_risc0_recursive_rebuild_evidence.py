from __future__ import annotations

import base64
import copy
import hashlib
import inspect
import io
import json
import os
import tarfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from unittest import mock

import pytest

from tools import check_risc0_recursive_rebuild_evidence as checker


@dataclass(frozen=True)
class RebuildFixture:
    workspace: Path
    workspace_archive: Path
    artifact_report: Path
    programs: Path
    verifier: Path
    proof: Path
    positive_verify_request: Path
    transcript: Path
    malformed_proof: Path
    malformed_verify_request: Path
    malformed_reject_transcript: Path
    reference: Path
    reference_digest: str


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _write(path: Path, raw: bytes) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path


def _write_json(path: Path, value: object, *, canonical: bool) -> Path:
    if canonical:
        raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    else:
        raw = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    return _write(path, raw)


def _image_words(seed: int) -> list[int]:
    return [seed * 100 + offset for offset in range(1, 9)]


def _image_id(words: list[int]) -> str:
    return b"".join(word.to_bytes(4, "little") for word in words).hex()


def _source_root(rows: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in sorted(rows, key=lambda item: str(item["path"])):
        digest.update(str(row["path"]).encode("ascii"))
        digest.update(b"\x00")
        digest.update(str(row["sha256"]).encode("ascii"))
        digest.update(b"\x00")
    return digest.hexdigest()


def _write_normalized_archive(path: Path, payloads: dict[str, bytes]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    directories = sorted(
        {
            parent.as_posix()
            for relative in payloads
            for parent in Path(relative).parents
            if parent.as_posix() != "."
        }
    )
    with tarfile.open(path, "w", format=tarfile.GNU_FORMAT) as archive:
        root = tarfile.TarInfo(".")
        root.type = tarfile.DIRTYPE
        root.mode = 0o775
        root.uid = 0
        root.gid = 0
        root.mtime = 0
        archive.addfile(root)
        for directory in directories:
            info = tarfile.TarInfo(f"./{directory}")
            info.type = tarfile.DIRTYPE
            info.mode = 0o775
            info.uid = 0
            info.gid = 0
            info.mtime = 0
            archive.addfile(info)
        for relative, raw in sorted(payloads.items()):
            info = tarfile.TarInfo(f"./{relative}")
            info.mode = 0o664
            info.uid = 0
            info.gid = 0
            info.mtime = 0
            info.size = len(raw)
            archive.addfile(info, io.BytesIO(raw))
    return path


def _fixture(tmp_path: Path) -> RebuildFixture:
    workspace = tmp_path / "source" / "state_proof_risc0"
    source_payloads = {
        "Cargo.lock": b"version = 4\n",
        "Cargo.toml": b"[workspace]\nmembers = []\n",
        "payload.bin": b"compiler-visible-payload",
        "src/lib.rs": b"pub const PAYLOAD: &[u8] = include_bytes!(\"../payload.bin\");\n",
    }
    source_rows: list[dict[str, Any]] = []
    for relative, raw in sorted(source_payloads.items()):
        _write(workspace / relative, raw)
        source_rows.append(
            {
                "path": f"{checker.WORKSPACE_IDENTITY_PREFIX}/{relative}",
                "sha256": _sha256(raw),
                "size_bytes": len(raw),
            }
        )

    programs = tmp_path / "programs"
    programs.mkdir()
    program_rows: list[dict[str, Any]] = []
    artifact_methods: list[dict[str, Any]] = []
    for seed, name in enumerate(checker.EXPECTED_PROGRAM_NAMES, start=1):
        artifact = f"{name}.bin"
        raw = f"risc0-program-{name}".encode("ascii")
        _write(programs / artifact, raw)
        words = _image_words(seed)
        row = {
            "artifact": artifact,
            "generated_image_id_words": words,
            "image_id": _image_id(words),
            "name": name,
            "program_bytes": len(raw),
            "program_sha256": _sha256(raw),
        }
        program_rows.append(row)
        artifact_methods.append({**row, "program_format": checker.PROGRAM_FORMAT})

    artifact_report_value = {
        "method_count": len(artifact_methods),
        "methods": artifact_methods,
        "schema": checker.ARTIFACT_REPORT_SCHEMA,
        "sdk_version": checker.SDK_VERSION,
    }
    artifact_report = _write_json(
        tmp_path / "artifact-report.json",
        artifact_report_value,
        canonical=True,
    )
    workspace_archive = _write_normalized_archive(
        tmp_path / "workspace.tar",
        source_payloads,
    )
    verifier = _write(tmp_path / "verifier.bin", b"static-verifier")
    receipt_value: dict[str, Any] = {
        "inner": {
            "Succinct": {
                "seal": [1001, 2003],
                "control_id": "control",
                "claim": "claim",
                "hashfn": "poseidon2",
                "verifier_parameters": "params",
                "control_inclusion_proof": [],
            }
        },
        "journal": [1, 2, 3],
        "metadata": {"test": True},
    }
    receipt_raw = json.dumps(receipt_value, separators=(",", ":")).encode("ascii")
    proof_value = {
        "meta": {"receipt_kind": "Succinct"},
        "proof": base64.b64encode(receipt_raw).decode("ascii"),
        "proof_type": "risc0.zenodex_recursive_epoch.v1",
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": "01" * 32,
    }
    proof = _write_json(tmp_path / "root-proof.json", proof_value, canonical=False)
    positive_request_value = {
        "proof": proof_value,
        "recursive_expectations": {"receipt_kind": "Succinct"},
        "recursive_input": {"children": []},
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": proof_value["state_hash"],
    }
    positive_verify_request = _write_json(
        tmp_path / "positive-verify-request.json",
        positive_request_value,
        canonical=False,
    )
    transcript = _write(tmp_path / "verified-transcript.json", b'{"ok":true}\n')
    mutation_index = 1
    mutation_original = receipt_value["inner"]["Succinct"]["seal"][mutation_index]
    mutation_mutated = mutation_original ^ 1
    mutated_receipt_value = copy.deepcopy(receipt_value)
    mutated_receipt_value["inner"]["Succinct"]["seal"][mutation_index] = mutation_mutated
    mutated_receipt_raw = json.dumps(
        mutated_receipt_value,
        separators=(",", ":"),
    ).encode("ascii")
    mutated_proof_value = copy.deepcopy(proof_value)
    mutated_proof_value["proof"] = base64.b64encode(mutated_receipt_raw).decode("ascii")
    mutated_proof = _write_json(
        tmp_path / "mutated-root-proof.json",
        mutated_proof_value,
        canonical=True,
    )
    malformed_request_value = copy.deepcopy(positive_request_value)
    malformed_request_value["proof"] = mutated_proof_value
    malformed_verify_request = _write_json(
        tmp_path / "malformed-verify-request.json",
        malformed_request_value,
        canonical=True,
    )
    malformed_reject_transcript = _write_json(
        tmp_path / "malformed-reject-transcript.json",
        {
            "process_exit_code": 0,
            "response": {"error": checker.CRYPTOGRAPHIC_INVALID_ERROR, "ok": False},
            "stderr": "",
        },
        canonical=True,
    )

    def blob(path: Path) -> dict[str, Any]:
        raw = path.read_bytes()
        return {"sha256": _sha256(raw), "size_bytes": len(raw)}

    reference_value = {
        "artifact_report": {
            "schema": checker.ARTIFACT_REPORT_SCHEMA,
            **blob(artifact_report),
        },
        "claims": dict(checker.EXPECTED_CLAIMS),
        "malformed_proof_reject": {
            "expected_error": checker.CRYPTOGRAPHIC_INVALID_ERROR,
            "expected_process_exit_code": 0,
            "mutated_root_proof": blob(mutated_proof),
            "mutation_kind": checker.MALFORMED_PROOF_MUTATION_KIND,
            "reject_transcript": blob(malformed_reject_transcript),
            "schema": checker.MALFORMED_PROOF_REJECT_SCHEMA,
            "seal_word_index": mutation_index,
            "seal_word_mutated": mutation_mutated,
            "seal_word_original": mutation_original,
            "source_root_proof_sha256": blob(proof)["sha256"],
            "verify_request": blob(malformed_verify_request),
        },
        "positive_verify_request": blob(positive_verify_request),
        "programs": program_rows,
        "root_proof": blob(proof),
        "schema": checker.REFERENCE_SCHEMA,
        "sdk_version": checker.SDK_VERSION,
        "source_compile": {
            "file_count": len(source_rows),
            "files": source_rows,
            "root_algorithm": checker.SOURCE_ROOT_ALGORITHM,
            "root_sha256": _source_root(source_rows),
            "workspace_identity_prefix": checker.WORKSPACE_IDENTITY_PREFIX,
        },
        "static_verifier": blob(verifier),
        "verified_transcript": blob(transcript),
        "version": 2,
        "workspace_archive": {
            "format": "normalized_gnu_tar_v1",
            **blob(workspace_archive),
        },
    }
    reference = _write_json(tmp_path / "reference.json", reference_value, canonical=False)
    return RebuildFixture(
        workspace=workspace,
        workspace_archive=workspace_archive,
        artifact_report=artifact_report,
        programs=programs,
        verifier=verifier,
        proof=proof,
        positive_verify_request=positive_verify_request,
        transcript=transcript,
        malformed_proof=mutated_proof,
        malformed_verify_request=malformed_verify_request,
        malformed_reject_transcript=malformed_reject_transcript,
        reference=reference,
        reference_digest=checker.reference_canonical_sha256(reference_value),
    )


def _check(
    fixture: RebuildFixture,
    *,
    trusted_reference_sha256: str | None = None,
) -> dict[str, Any]:
    reference_digest = (
        fixture.reference_digest if trusted_reference_sha256 is None else trusted_reference_sha256
    )
    with (
        mock.patch.object(checker, "REFERENCE_PATH", fixture.reference),
        mock.patch.object(
            checker,
            "EXPECTED_REFERENCE_CANONICAL_SHA256",
            reference_digest,
        ),
    ):
        return checker.check_risc0_recursive_rebuild_evidence(
            checker.RebuildEvidencePaths(
                workspace_root=fixture.workspace,
                workspace_archive=fixture.workspace_archive,
                artifact_report=fixture.artifact_report,
                program_directory=fixture.programs,
                static_verifier=fixture.verifier,
                root_proof=fixture.proof,
                positive_verify_request=fixture.positive_verify_request,
                verified_transcript=fixture.transcript,
                malformed_root_proof=fixture.malformed_proof,
                malformed_verify_request=fixture.malformed_verify_request,
                malformed_reject_transcript=fixture.malformed_reject_transcript,
            )
        )


def _mutate_same_size(path: Path) -> None:
    raw = bytearray(path.read_bytes())
    raw[0] ^= 1
    path.write_bytes(raw)


def test_committed_reference_is_authenticated_and_claim_limited() -> None:
    raw = checker.REFERENCE_PATH.read_bytes()
    reference = json.loads(raw)

    validated = checker.validate_reference(reference)

    assert checker.reference_canonical_sha256(validated) == (
        checker.EXPECTED_REFERENCE_CANONICAL_SHA256
    )
    assert validated["source_compile"]["root_sha256"] == (
        "81f5dc170de45306b7427f8379ea23add429f5c6325a06c0bb4fa6c4315f78bf"
    )
    assert [program["program_sha256"] for program in validated["programs"]] == [
        "bbc64916ff42389fce5f4e76fe4b52e4f3eaad70d27813aef7156f372d5ded5e",
        "c3d64f382d9510f5837c562295991629154091feaa2f258a2e1a25f76f1c28d6",
        "bcf7516b1564a7071f0a6c0ded20580bfcc30bde8a47929d648538715b7ccf4b",
        "d1fd8915a3c1650b42527e6b878f203679cd447b506916c6a9a56008ed0951a8",
        "ea44c990e32c6de41536521148c04954cf8705740d75faa8008ca9427c32dd88",
        "62ce1d97b3a2671e985b2a6633f6e01520b71f6d7a4a0408924725b74555c5a7",
    ]
    assert validated["root_proof"]["sha256"] == (
        "061f99b459e54a0bef821880f43049bb2120d5ff427439067950141286d533dd"
    )
    assert validated["static_verifier"] == {
        "sha256": "8836f22431e2ce241eec9e6503f741b92673e2fec054208b0c36dea4f1bcf146",
        "size_bytes": 15_339_184,
    }
    assert validated["verified_transcript"]["sha256"] == (
        "af2a660f10f3b4eb01811cb4215f01546679618296dcd369e3f6d542bfae5c8a"
    )
    assert validated["claims"] == checker.EXPECTED_CLAIMS


def test_matching_candidate_reports_pinned_artifact_scope_only(tmp_path: Path) -> None:
    report = _check(_fixture(tmp_path))

    assert report["ok"] is True
    assert report["status"] == "pinned_rebuild_artifact_match"
    assert report["pinned_rebuild_artifact_match"] is True
    assert report["malformed_proof_reject_verified"] is True
    assert report["same_host_clean_rebuild"] is False
    assert report["source_file_count"] == 4
    assert report["workspace_archive_source_root_sha256"] == report["source_compile_root_sha256"]
    assert report["evidence_basis"] == (
        "code_pinned_reference_candidate_byte_equality_and_malformed_proof_semantics"
    )
    assert report["build_command_authenticated"] is False
    assert report["build_environment_authenticated"] is False
    assert report["clean_target_verified"] is False
    assert report["cross_environment_reproducibility"] is False
    assert report["production_ready"] is False
    assert report["public_claim_allowed"] is False
    assert report["public_replay"] is False
    assert report["independent_rebuild"] is False
    assert report["reproducible_release"] is False
    assert report["settlement_authorization"] is False
    assert report["source_archive_provenance_authenticated"] is False
    assert report["toolchain_execution_authenticated"] is False
    assert report["independent_image_id_rerun"] == {
        "attempted": False,
        "matched": False,
        "reason": "no hash-pinned r0vm was supplied for execution",
    }


def test_missing_source_compile_file_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    (fixture.workspace / "Cargo.lock").unlink()

    report = _check(fixture)

    assert report["error_codes"] == ["SOURCE_FILE_MISSING"]


def test_extra_source_compile_file_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _write(fixture.workspace / "src/extra.rs", b"pub fn extra() {}\n")

    report = _check(fixture)

    assert report["error_codes"] == ["SOURCE_FILE_EXTRA"]


@pytest.mark.parametrize("relative_path", [".cargo/config", "methods/.cargo/config"])
def test_undeclared_cargo_config_rejects(tmp_path: Path, relative_path: str) -> None:
    fixture = _fixture(tmp_path)
    _write(fixture.workspace / relative_path, b"[build]\nrustflags = []\n")

    report = _check(fixture)

    assert report["error_codes"] == ["SOURCE_FILE_EXTRA"]


def test_source_content_mutation_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(fixture.workspace / "src/lib.rs")

    report = _check(fixture)

    assert report["error_codes"] == ["SOURCE_SHA256_MISMATCH"]


def test_include_bytes_payload_mutation_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(fixture.workspace / "payload.bin")

    report = _check(fixture)

    assert report["error_codes"] == ["SOURCE_SHA256_MISMATCH"]


def test_source_scope_target_directory_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _write(fixture.workspace / "target/hidden.bin", b"compiler-visible")

    report = _check(fixture)

    assert report["error_codes"] == ["SOURCE_TARGET_PRESENT"]


@pytest.mark.skipif(not hasattr(os, "symlink"), reason="symlinks unavailable")
def test_source_symlink_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    source = fixture.workspace / "src/lib.rs"
    replacement = fixture.workspace / "src/replacement.txt"
    source.rename(replacement)
    source.symlink_to(replacement.name)

    report = _check(fixture)

    assert report["error_codes"] == ["SYMLINK_FORBIDDEN"]


def test_workspace_archive_mutation_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(fixture.workspace_archive)

    report = _check(fixture)

    assert report["error_codes"] == ["WORKSPACE_ARCHIVE_SHA256_MISMATCH"]


def test_workspace_archive_source_mismatch_rejects_with_recomputed_reference_digest(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    mutated_lib = bytearray((fixture.workspace / "src/lib.rs").read_bytes())
    mutated_lib[0] ^= 1
    payloads = {
        "Cargo.lock": (fixture.workspace / "Cargo.lock").read_bytes(),
        "Cargo.toml": (fixture.workspace / "Cargo.toml").read_bytes(),
        "payload.bin": (fixture.workspace / "payload.bin").read_bytes(),
        "src/lib.rs": bytes(mutated_lib),
    }
    _write_normalized_archive(fixture.workspace_archive, payloads)
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    archive_raw = fixture.workspace_archive.read_bytes()
    reference["workspace_archive"]["sha256"] = _sha256(archive_raw)
    reference["workspace_archive"]["size_bytes"] = len(archive_raw)
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["WORKSPACE_ARCHIVE_SOURCE_SHA256_MISMATCH"]


def test_artifact_report_mutation_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(fixture.artifact_report)

    report = _check(fixture)

    assert report["error_codes"] == ["ARTIFACT_REPORT_SHA256_MISMATCH"]


def test_program_content_mutation_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(fixture.programs / "aggregate.bin")

    report = _check(fixture)

    assert report["error_codes"] == ["PROGRAM_SHA256_MISMATCH"]


def test_extra_program_artifact_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _write(fixture.programs / "undeclared.bin", b"undeclared")

    report = _check(fixture)

    assert report["error_codes"] == ["PROGRAM_ARTIFACT_EXTRA"]


def test_missing_program_artifact_rejects(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    (fixture.programs / "aggregate.bin").unlink()

    report = _check(fixture)

    assert report["error_codes"] == ["PROGRAM_ARTIFACT_MISSING"]


@pytest.mark.parametrize(
    ("field", "expected_code"),
    [
        ("verifier", "STATIC_VERIFIER_SHA256_MISMATCH"),
        ("proof", "ROOT_PROOF_SHA256_MISMATCH"),
        ("positive_verify_request", "POSITIVE_VERIFY_REQUEST_SHA256_MISMATCH"),
        ("transcript", "VERIFIED_TRANSCRIPT_SHA256_MISMATCH"),
        ("malformed_proof", "MALFORMED_ROOT_PROOF_SHA256_MISMATCH"),
        ("malformed_verify_request", "MALFORMED_VERIFY_REQUEST_SHA256_MISMATCH"),
        ("malformed_reject_transcript", "MALFORMED_REJECT_TRANSCRIPT_SHA256_MISMATCH"),
    ],
)
def test_bound_evidence_mutation_rejects(
    tmp_path: Path,
    field: str,
    expected_code: str,
) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(getattr(fixture, field))

    report = _check(fixture)

    assert report["error_codes"] == [expected_code]


def test_rebound_transcript_cannot_change_cryptographic_reject_class(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    _write_json(
        fixture.malformed_reject_transcript,
        {"process_exit_code": 0, "response": {"ok": True}, "stderr": ""},
        canonical=True,
    )
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    raw = fixture.malformed_reject_transcript.read_bytes()
    reference["malformed_proof_reject"]["reject_transcript"] = {
        "sha256": _sha256(raw),
        "size_bytes": len(raw),
    }
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["MALFORMED_PROOF_EVIDENCE"]


def test_rebound_malformed_request_cannot_drift_outside_proof(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    request = json.loads(fixture.malformed_verify_request.read_bytes())
    request["recursive_input"] = {"children": ["drift"]}
    _write_json(fixture.malformed_verify_request, request, canonical=True)
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    raw = fixture.malformed_verify_request.read_bytes()
    reference["malformed_proof_reject"]["verify_request"] = {
        "sha256": _sha256(raw),
        "size_bytes": len(raw),
    }
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["MALFORMED_PROOF_EVIDENCE"]


def test_rebound_malformed_proof_cannot_change_second_seal_word(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    proof = json.loads(fixture.malformed_proof.read_bytes())
    receipt_raw = base64.b64decode(proof["proof"], validate=True)
    receipt = json.loads(receipt_raw)
    receipt["inner"]["Succinct"]["seal"][0] ^= 1
    proof["proof"] = base64.b64encode(
        json.dumps(receipt, separators=(",", ":")).encode("ascii")
    ).decode("ascii")
    _write_json(fixture.malformed_proof, proof, canonical=True)
    request = json.loads(fixture.malformed_verify_request.read_bytes())
    request["proof"] = proof
    _write_json(fixture.malformed_verify_request, request, canonical=True)
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    malformed_raw = fixture.malformed_proof.read_bytes()
    request_raw = fixture.malformed_verify_request.read_bytes()
    reference["malformed_proof_reject"]["mutated_root_proof"] = {
        "sha256": _sha256(malformed_raw),
        "size_bytes": len(malformed_raw),
    }
    reference["malformed_proof_reject"]["verify_request"] = {
        "sha256": _sha256(request_raw),
        "size_bytes": len(request_raw),
    }
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["MALFORMED_PROOF_EVIDENCE"]


def test_rebound_noncanonical_base64_cannot_impersonate_seal_reject(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    proof = json.loads(fixture.malformed_proof.read_bytes())
    encoded = proof["proof"]
    alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    padding = len(encoded) - len(encoded.rstrip("="))
    assert padding in {1, 2}
    final_index = len(encoded) - padding - 1
    value = alphabet.index(encoded[final_index])
    unused_mask = 0b11 if padding == 1 else 0b1111
    assert value & unused_mask == 0
    proof["proof"] = encoded[:final_index] + alphabet[value | 1] + encoded[final_index + 1 :]
    assert base64.b64decode(proof["proof"], validate=True) == base64.b64decode(
        encoded,
        validate=True,
    )
    _write_json(fixture.malformed_proof, proof, canonical=True)
    request = json.loads(fixture.malformed_verify_request.read_bytes())
    request["proof"] = proof
    _write_json(fixture.malformed_verify_request, request, canonical=True)
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    malformed_raw = fixture.malformed_proof.read_bytes()
    request_raw = fixture.malformed_verify_request.read_bytes()
    reference["malformed_proof_reject"]["mutated_root_proof"] = {
        "sha256": _sha256(malformed_raw),
        "size_bytes": len(malformed_raw),
    }
    reference["malformed_proof_reject"]["verify_request"] = {
        "sha256": _sha256(request_raw),
        "size_bytes": len(request_raw),
    }
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["MALFORMED_PROOF_EVIDENCE"]


def test_reference_rejects_unchanged_seal_word_as_mutation(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    reference["malformed_proof_reject"]["seal_word_mutated"] = reference["malformed_proof_reject"][
        "seal_word_original"
    ]
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["REFERENCE_SCHEMA"]


def test_reference_trust_root_cannot_be_supplied_by_caller(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)

    parameters = inspect.signature(checker.check_risc0_recursive_rebuild_evidence).parameters
    assert "reference_path" not in parameters
    assert "expected_reference_sha256" not in parameters

    with mock.patch.object(checker, "REFERENCE_PATH", fixture.reference):
        report = checker.check_risc0_recursive_rebuild_evidence(
            checker.RebuildEvidencePaths(
                workspace_root=fixture.workspace,
                workspace_archive=fixture.workspace_archive,
                artifact_report=fixture.artifact_report,
                program_directory=fixture.programs,
                static_verifier=fixture.verifier,
                root_proof=fixture.proof,
                positive_verify_request=fixture.positive_verify_request,
                verified_transcript=fixture.transcript,
                malformed_root_proof=fixture.malformed_proof,
                malformed_verify_request=fixture.malformed_verify_request,
                malformed_reject_transcript=fixture.malformed_reject_transcript,
            )
        )

    assert report["error_codes"] == ["REFERENCE_DIGEST_MISMATCH"]


def test_claim_escalation_rejects_with_recomputed_reference_digest(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    reference = json.loads(fixture.reference.read_text(encoding="utf-8"))
    reference["claims"]["production_ready"] = True
    _write_json(fixture.reference, reference, canonical=False)

    report = _check(
        fixture,
        trusted_reference_sha256=checker.reference_canonical_sha256(reference),
    )

    assert report["error_codes"] == ["REFERENCE_CLAIMS"]


@pytest.mark.parametrize(
    ("raw", "expected_code"),
    [
        (b'{"schema":"first","schema":"second"}\n', "REFERENCE_JSON_DUPLICATE_KEY"),
        (b'{"value":1.5}\n', "REFERENCE_JSON_FLOAT"),
        (b'{"value":100000000000000000000}\n', "REFERENCE_JSON_INTEGER_LIMIT"),
        (b"[" * 65 + b"0" + b"]" * 65, "REFERENCE_JSON_DEPTH_LIMIT"),
    ],
)
def test_noncanonical_reference_numbers_or_keys_reject(
    tmp_path: Path,
    raw: bytes,
    expected_code: str,
) -> None:
    fixture = _fixture(tmp_path)
    fixture.reference.write_bytes(raw)

    report = _check(fixture)

    assert report["error_codes"] == [expected_code]


def test_cli_returns_nonzero_and_stable_json_on_drift(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fixture = _fixture(tmp_path)
    _mutate_same_size(fixture.proof)

    with (
        mock.patch.object(checker, "REFERENCE_PATH", fixture.reference),
        mock.patch.object(
            checker,
            "EXPECTED_REFERENCE_CANONICAL_SHA256",
            fixture.reference_digest,
        ),
    ):
        return_code = checker.main(
            [
                "--workspace-root",
                str(fixture.workspace),
                "--workspace-archive",
                str(fixture.workspace_archive),
                "--artifact-report",
                str(fixture.artifact_report),
                "--program-directory",
                str(fixture.programs),
                "--static-verifier",
                str(fixture.verifier),
                "--root-proof",
                str(fixture.proof),
                "--positive-verify-request",
                str(fixture.positive_verify_request),
                "--verified-transcript",
                str(fixture.transcript),
                "--malformed-root-proof",
                str(fixture.malformed_proof),
                "--malformed-verify-request",
                str(fixture.malformed_verify_request),
                "--malformed-reject-transcript",
                str(fixture.malformed_reject_transcript),
                "--json",
            ]
        )
    output = json.loads(capsys.readouterr().out)

    assert return_code == 1
    assert output["error_codes"] == ["ROOT_PROOF_SHA256_MISMATCH"]
    assert output["pinned_rebuild_artifact_match"] is False
    assert output["same_host_clean_rebuild"] is False


@pytest.mark.parametrize("raw_path", ["bad\x00path", "bad\ud800path"])
def test_regular_path_rejects_unencodable_or_nul_path(raw_path: str) -> None:
    with pytest.raises(checker.EvidenceError) as rejected:
        checker._read_regular_path(
            Path(raw_path),
            label="evidence",
            max_bytes=1,
        )

    assert rejected.value.code == "FILE_PATH_INVALID"


@pytest.mark.parametrize("raw_path", ["bad\x00directory", "bad\ud800directory"])
def test_directory_rejects_unencodable_or_nul_path(raw_path: str) -> None:
    with pytest.raises(checker.EvidenceError) as rejected:
        checker._canonical_directory(Path(raw_path), label="workspace")

    assert rejected.value.code == "DIRECTORY_INVALID"


def test_regular_path_rejects_path_normalization_oserror(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def unavailable_working_directory(_path: str) -> str:
        raise FileNotFoundError("working directory was removed")

    monkeypatch.setattr(checker.os.path, "abspath", unavailable_working_directory)

    with pytest.raises(checker.EvidenceError) as rejected:
        checker._read_regular_path(
            Path("relative-evidence.json"),
            label="evidence",
            max_bytes=1,
        )

    assert rejected.value.code == "FILE_PATH_INVALID"


def test_regular_path_converts_descriptor_close_failure(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    evidence = _write(tmp_path / "evidence.json", b"{}")
    real_close = checker.os.close

    def close_then_fail(descriptor: int) -> None:
        real_close(descriptor)
        raise OSError("injected close failure")

    monkeypatch.setattr(checker.os, "close", close_then_fail)

    with pytest.raises(checker.EvidenceError) as rejected:
        checker._read_regular_path(
            evidence,
            label="evidence",
            max_bytes=2,
        )

    assert rejected.value.code == "FILE_CLOSE_FAILED"


def test_regular_path_preserves_read_failure_when_cleanup_also_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    evidence = _write(tmp_path / "evidence.json", b"{}")
    real_close = checker.os.close

    def fail_read(_descriptor: int, _size: int) -> bytes:
        raise OSError("injected read failure")

    def close_then_fail(descriptor: int) -> None:
        real_close(descriptor)
        raise OSError("injected close failure")

    monkeypatch.setattr(checker.os, "read", fail_read)
    monkeypatch.setattr(checker.os, "close", close_then_fail)

    with pytest.raises(checker.EvidenceError) as rejected:
        checker._read_regular_path(
            evidence,
            label="evidence",
            max_bytes=2,
        )

    assert rejected.value.code == "FILE_OPEN_FAILED"
    assert "cleanup_failure=FILE_CLOSE_FAILED" in str(rejected.value)


def test_regular_path_does_not_suppress_close_failure_inside_outer_handler(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    evidence = _write(tmp_path / "evidence.json", b"{}")
    real_close = checker.os.close

    def close_then_fail(descriptor: int) -> None:
        real_close(descriptor)
        raise OSError("injected close failure")

    monkeypatch.setattr(checker.os, "close", close_then_fail)
    outer_error = RuntimeError("unrelated outer failure")

    try:
        raise outer_error
    except RuntimeError:
        with pytest.raises(checker.EvidenceError) as rejected:
            checker._read_regular_path(
                evidence,
                label="evidence",
                max_bytes=2,
            )

    assert rejected.value.code == "FILE_CLOSE_FAILED"
    assert getattr(outer_error, "__notes__", []) == []
