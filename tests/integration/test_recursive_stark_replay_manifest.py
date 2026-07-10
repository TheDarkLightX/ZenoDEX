from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
from typing import Any

import pytest

from src.core.recursive_stark_admission import (
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)
from src.integration.recursive_stark_replay_manifest import (
    EXPECTED_METHOD_ARTIFACTS_V1,
    EXPECTED_METHOD_NAMES_V1,
    MANIFEST_FILENAME_V1,
    NON_CLAIMS_V1,
    RECEIPT_CODEC_V1,
    ROOT_PROOF_META_KEYS_V1,
    ROOT_PROOF_TYPE_V1,
    STATUS_V1,
    NamedArtifactInput,
    RecursiveStarkReplayBundleError,
    build_recursive_stark_replay_bundle_v1,
    check_recursive_stark_replay_bundle_v1,
    recursive_stark_replay_manifest_hash_v1,
)
from src.state.canonical import canonical_json_bytes
from tools import build_recursive_stark_replay_bundle as build_tool
from tools import check_recursive_stark_replay_bundle as check_tool


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _image_words(seed: int) -> list[int]:
    return [seed * 100 + index for index in range(1, 9)]


def _image_id(words: list[int]) -> str:
    return b"".join(word.to_bytes(4, "little") for word in words).hex()


def _write(path: Path, raw: bytes) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path


def _root_replay_transcript(aggregate_image_id: str) -> tuple[dict[str, Any], ...]:
    meta = {
        key: f"{index + 1:064x}"
        for index, key in enumerate(sorted(ROOT_PROOF_META_KEYS_V1))
    }
    child_claims = ("0x" + "31" * 32,)
    receipt_ids = ("0x" + "32" * 32,)
    message_ids = ("0x" + "33" * 32,)
    meta.update(
        {
            "risc0_image_id": aggregate_image_id,
            "receipt_codec": RECEIPT_CODEC_V1,
            "receipt_kind": "succinct",
            "receipt_hashfn": "poseidon2",
            "receipt_verifier_parameters": "12" * 32,
            "receipt_control_id": "13" * 32,
            "proof_type": ROOT_PROOF_TYPE_V1,
            "domain_separator": "zenodex.risc0.recursive_epoch.v1",
            "chain_id": "zenodex-devnet",
            "epoch_id": 7,
            "proof_profile": "recursive_epoch_v1",
            "child_count": 1,
            "post_state_root": "22" * 32,
            "child_verification_claims_root": recursive_child_verification_claims_root_v1(
                child_claims
            )[2:],
            "accepted_receipts_root": recursive_receipt_ids_root_v1(receipt_ids)[2:],
            "cross_shard_message_ids_root": recursive_message_ids_root_v1(message_ids)[2:],
        }
    )
    proof = {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": meta["post_state_root"],
        "proof_type": ROOT_PROOF_TYPE_V1,
        "proof": "e30=",
        "meta": meta,
    }
    expectations = {**meta, "journal_version": 1}
    request = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": meta["post_state_root"],
        "proof": proof,
        "recursive_input": {"disclosure": "fixture"},
        "recursive_expectations": expectations,
    }
    facts = {
        "schema": "zenodex.verified_recursive_stark_root_facts.v1",
        "aggregate_image_id": aggregate_image_id,
        "receipt_codec": RECEIPT_CODEC_V1,
        "receipt_kind": "succinct",
        "receipt_hashfn": "poseidon2",
        "receipt_verifier_parameters": "12" * 32,
        "receipt_control_id": "13" * 32,
        "chain_id": "zenodex-devnet",
        "epoch_id": 7,
        "proof_profile": "recursive_epoch_v1",
        "root_journal_hash": "0x" + "34" * 32,
        "verifier_set_root": "0x" + str(meta["verifier_set_root"]),
        "public_policy_hash": "0x" + str(meta["public_policy_hash"]),
        "child_verification_claim_hashes": list(child_claims),
        "child_verification_claims_root": "0x" + str(meta["child_verification_claims_root"]),
        "accepted_receipt_ids": list(receipt_ids),
        "accepted_receipts_root": "0x" + str(meta["accepted_receipts_root"]),
        "cross_shard_message_ids": list(message_ids),
        "cross_shard_message_ids_root": "0x" + str(meta["cross_shard_message_ids_root"]),
    }
    return proof, request, {"ok": True, "verified_recursive_facts": facts}


def _fixture_inputs(tmp_path: Path) -> dict[str, Any]:
    artifact_directory = tmp_path / "exported"
    artifact_directory.mkdir(parents=True)
    methods: list[dict[str, Any]] = []
    for seed, name in enumerate(EXPECTED_METHOD_NAMES_V1, start=1):
        filename = EXPECTED_METHOD_ARTIFACTS_V1[name]
        program = f"risc0-program-{name}".encode("ascii")
        _write(artifact_directory / filename, program)
        words = _image_words(seed)
        methods.append(
            {
                "artifact": filename,
                "generated_image_id_words": words,
                "image_id": _image_id(words),
                "name": name,
                "program_bytes": len(program),
                "program_format": "risc0_program_binary_v1compat_v3",
                "program_sha256": _sha256(program),
            }
        )
    export_report = {
        "schema": "zenodex/risc0_recursive_embedded_artifacts/v1",
        "sdk_version": "3.0.5",
        "method_count": len(methods),
        "methods": methods,
    }
    export_report_path = _write(
        artifact_directory / "report-input.json",
        json.dumps(export_report, indent=2).encode("utf-8"),
    )
    source = _write(tmp_path / "inputs/source.rs", b"fn main() {}\n")
    toolchain = _write(tmp_path / "inputs/r0vm.bin", b"pinned-r0vm")
    proof_value, request_value, verification_value = _root_replay_transcript(
        str(methods[0]["image_id"])
    )
    proof = _write(
        tmp_path / "inputs/root-proof.json",
        json.dumps(proof_value, indent=2).encode(),
    )
    request = _write(
        tmp_path / "inputs/root-request.json",
        json.dumps(request_value, indent=2).encode(),
    )
    verification = _write(
        tmp_path / "inputs/root-verification.json",
        json.dumps(verification_value, indent=2).encode(),
    )
    return {
        "artifact_export_report_path": export_report_path,
        "artifact_directory": artifact_directory,
        "source_files": [NamedArtifactInput("workspace.rs", source)],
        "toolchain_files": [NamedArtifactInput("r0vm.bin", toolchain)],
        "proof_files": [NamedArtifactInput("root.json", proof)],
        "request_files": [NamedArtifactInput("root.json", request)],
        "verification_files": [NamedArtifactInput("root.json", verification)],
    }


def _build(tmp_path: Path, *, name: str = "bundle") -> tuple[Path, dict[str, Any]]:
    bundle = tmp_path / name
    report = build_recursive_stark_replay_bundle_v1(
        **_fixture_inputs(tmp_path / f"fixture-{name}"),
        output_directory=bundle,
    )
    return bundle, report


def _manifest(bundle: Path) -> dict[str, Any]:
    return json.loads((bundle / MANIFEST_FILENAME_V1).read_text(encoding="utf-8"))


def _write_manifest(bundle: Path, manifest: dict[str, Any]) -> None:
    manifest["manifest_hash"] = recursive_stark_replay_manifest_hash_v1(manifest)
    (bundle / MANIFEST_FILENAME_V1).write_bytes(canonical_json_bytes(manifest))


def test_build_and_check_local_artifact_pinned_bundle(tmp_path: Path) -> None:
    bundle, build_report = _build(tmp_path)

    check = check_recursive_stark_replay_bundle_v1(bundle)
    manifest = _manifest(bundle)

    assert check["ok"] is True
    assert check["status"] == STATUS_V1
    assert check["expected_manifest_sha256_matched"] is False
    assert check["production_ready"] is False
    assert check["public_claim_allowed"] is False
    assert check["reproducible_build_claim"] is False
    assert manifest["non_claims"] == list(NON_CLAIMS_V1)
    assert manifest["invalidated_evidence_versions"] == ["1.2.6"]
    assert build_report["manifest_sha256"] == check["manifest_sha256"]
    assert build_report["artifact_count"] == 12


def test_bundle_build_is_deterministic(tmp_path: Path) -> None:
    first_bundle, first = _build(tmp_path, name="first")
    second_bundle, second = _build(tmp_path, name="second")

    assert first["manifest_hash"] == second["manifest_hash"]
    assert first["manifest_sha256"] == second["manifest_sha256"]
    assert (first_bundle / MANIFEST_FILENAME_V1).read_bytes() == (
        second_bundle / MANIFEST_FILENAME_V1
    ).read_bytes()


def test_checker_rejects_noncanonical_manifest_bytes(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    (bundle / MANIFEST_FILENAME_V1).write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["NONCANONICAL_JSON_BYTES"]


def test_checker_rejects_duplicate_manifest_key(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    manifest_path = bundle / MANIFEST_FILENAME_V1
    raw = manifest_path.read_bytes()
    manifest_path.write_bytes(raw[:-1] + b',"schema":"substituted"}')

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["DUPLICATE_JSON_KEY"]


def test_checker_rejects_claim_escalation_even_with_recomputed_hash(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    manifest["production_ready"] = True
    _write_manifest(bundle, manifest)

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["CLAIM_ESCALATION"]


def test_checker_rejects_bound_artifact_tamper(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    with (bundle / "methods/aggregate.bin").open("ab") as handle:
        handle.write(b"tamper")

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["ARTIFACT_BINDING_MISMATCH"]


def test_checker_rejects_undeclared_file(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    _write(bundle / "proof/undeclared.json", b"{}")

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["INVENTORY_MISMATCH"]
    assert "undeclared.json" in check["errors"][0]


def test_checker_rejects_undeclared_directory(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    (bundle / "undeclared").mkdir()

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["INVENTORY_MISMATCH"]


@pytest.mark.skipif(not hasattr(os, "symlink"), reason="symlink unsupported")
def test_checker_rejects_symlink_artifact(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    source = bundle / "source/workspace.rs"
    source.unlink()
    source.symlink_to(bundle / "methods/aggregate.bin")

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["SYMLINK_FORBIDDEN"]


@pytest.mark.parametrize("unsafe", [".", "/tmp/escape", "../escape", "proof\\escape"])
def test_checker_rejects_unsafe_manifest_paths(tmp_path: Path, unsafe: str) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    manifest["artifacts"][0]["path"] = unsafe
    _write_manifest(bundle, manifest)

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["UNSAFE_PATH"]


@pytest.mark.parametrize("field", ["role", "path"])
def test_checker_rejects_duplicate_artifact_identity(tmp_path: Path, field: str) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    duplicate = copy.deepcopy(manifest["artifacts"][1])
    duplicate["role"] = manifest["artifacts"][2]["role"] if field == "role" else "duplicate.role"
    duplicate["path"] = manifest["artifacts"][2]["path"] if field == "path" else duplicate["path"]
    manifest["artifacts"].append(duplicate)
    manifest["artifacts"].sort(key=lambda item: (item["kind"], item["role"], item["path"]))
    manifest["artifact_count"] += 1
    manifest["total_size_bytes"] += duplicate["size_bytes"]
    _write_manifest(bundle, manifest)

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["DUPLICATE_ROLE" if field == "role" else "DUPLICATE_PATH"]


def test_checker_rejects_source_root_drift(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    manifest["source_root"] = "sha256:" + "0" * 64
    _write_manifest(bundle, manifest)

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["SOURCE_ROOT_MISMATCH"]


def test_checker_rejects_role_path_relabeling(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    source_row = next(item for item in manifest["artifacts"] if item["kind"] == "source")
    source_row["role"] = "source.relabelled.rs"
    _write_manifest(bundle, manifest)

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["ARTIFACT_ROLE_PATH"]


def test_checker_rejects_non_string_artifact_kind_without_crashing(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)
    manifest = _manifest(bundle)
    manifest["artifacts"][0]["kind"] = []
    _write_manifest(bundle, manifest)

    check = check_recursive_stark_replay_bundle_v1(bundle)

    assert check["ok"] is False
    assert check["error_codes"] == ["ARTIFACT_KIND"]


def test_external_manifest_digest_is_optional_and_fail_closed(tmp_path: Path) -> None:
    bundle, report = _build(tmp_path)

    accepted = check_recursive_stark_replay_bundle_v1(
        bundle,
        expected_manifest_sha256=report["manifest_sha256"],
    )
    rejected = check_recursive_stark_replay_bundle_v1(
        bundle,
        expected_manifest_sha256="sha256:" + "0" * 64,
    )

    assert accepted["ok"] is True
    assert accepted["expected_manifest_sha256_matched"] is True
    assert accepted["status"] == STATUS_V1
    assert rejected["error_codes"] == ["EXPECTED_MANIFEST_SHA256_MISMATCH"]


def test_external_manifest_digest_rejects_non_string_without_crashing(tmp_path: Path) -> None:
    bundle, _ = _build(tmp_path)

    check = check_recursive_stark_replay_bundle_v1(  # type: ignore[arg-type]
        bundle,
        expected_manifest_sha256=7,
    )

    assert check["ok"] is False
    assert check["error_codes"] == ["EXPECTED_MANIFEST_SHA256_FORMAT"]


def test_builder_rejects_export_image_encoding_mismatch(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    report_path = inputs["artifact_export_report_path"]
    report = json.loads(report_path.read_text(encoding="utf-8"))
    report["methods"][0]["image_id"] = "11" * 32
    report_path.write_text(json.dumps(report), encoding="utf-8")

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(
            **inputs,
            output_directory=tmp_path / "bundle",
        )

    assert exc_info.value.code == "EXPORT_IMAGE_ENCODING"


def test_builder_rejects_duplicate_named_role(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    inputs["source_files"].append(inputs["source_files"][0])

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(
            **inputs,
            output_directory=tmp_path / "bundle",
        )

    assert exc_info.value.code == "DUPLICATE_ROLE"


def test_builder_rejects_duplicate_json_key(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    proof_path = inputs["proof_files"][0].path
    proof_path.write_bytes(b'{"schema":"proof-v1","schema":"substituted"}')

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(
            **inputs,
            output_directory=tmp_path / "bundle",
        )

    assert exc_info.value.code == "DUPLICATE_JSON_KEY"


def test_builder_rejects_surrogate_json_value(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    proof_path = inputs["proof_files"][0].path
    proof_path.write_bytes(b'{"proof":"\\ud800"}')

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(
            **inputs,
            output_directory=tmp_path / "bundle",
        )

    assert exc_info.value.code == "NONCANONICAL_JSON_VALUE"


def test_builder_and_checker_accept_maximum_length_input_name(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    source = inputs["source_files"][0]
    inputs["source_files"] = [NamedArtifactInput("a" * 128, source.path)]

    report = build_recursive_stark_replay_bundle_v1(
        **inputs,
        output_directory=tmp_path / "bundle",
    )
    check = check_recursive_stark_replay_bundle_v1(tmp_path / "bundle")

    assert report["ok"] is True
    assert check["ok"] is True


def test_builder_requires_accepted_verification(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    verification_path = inputs["verification_files"][0].path
    verification_path.write_text(
        json.dumps({"ok": False, "error": "fixture reject"}),
        encoding="utf-8",
    )

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(
            **inputs,
            output_directory=tmp_path / "bundle",
        )

    assert exc_info.value.code == "ACCEPTED_VERIFICATION_REQUIRED"


def test_builder_rejects_unbound_accepted_verification(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    verification_path = inputs["verification_files"][0].path
    verification = json.loads(verification_path.read_text(encoding="utf-8"))
    verification["verified_recursive_facts"]["chain_id"] = "substituted-chain"
    verification_path.write_text(json.dumps(verification), encoding="utf-8")

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(
            **inputs,
            output_directory=tmp_path / "bundle",
        )

    assert exc_info.value.code == "VERIFICATION_TRANSCRIPT_UNBOUND"


def test_builder_preflights_artifact_count_before_output_creation(tmp_path: Path) -> None:
    inputs = _fixture_inputs(tmp_path)
    source = inputs["source_files"][0].path
    inputs["source_files"] = [
        NamedArtifactInput(f"s{index:03d}", source)
        for index in range(506)
    ]
    output = tmp_path / "bundle"

    with pytest.raises(RecursiveStarkReplayBundleError) as exc_info:
        build_recursive_stark_replay_bundle_v1(**inputs, output_directory=output)

    assert exc_info.value.code == "ARTIFACT_COUNT_LIMIT"
    assert not output.exists()


def _tool_args(inputs: dict[str, Any], output_directory: Path) -> list[str]:
    return [
        "--artifact-export-report",
        str(inputs["artifact_export_report_path"]),
        "--artifact-directory",
        str(inputs["artifact_directory"]),
        "--source",
        f"{inputs['source_files'][0].name}={inputs['source_files'][0].path}",
        "--toolchain",
        f"{inputs['toolchain_files'][0].name}={inputs['toolchain_files'][0].path}",
        "--proof",
        f"{inputs['proof_files'][0].name}={inputs['proof_files'][0].path}",
        "--request",
        f"{inputs['request_files'][0].name}={inputs['request_files'][0].path}",
        "--verification",
        f"{inputs['verification_files'][0].name}={inputs['verification_files'][0].path}",
        "--out-dir",
        str(output_directory),
    ]


def test_build_and_check_cli_reports_remain_local(tmp_path: Path, capsys) -> None:
    inputs = _fixture_inputs(tmp_path)
    bundle = tmp_path / "bundle"

    build_code = build_tool.main(_tool_args(inputs, bundle))
    build_report = json.loads(capsys.readouterr().out)
    check_code = check_tool.main(
        [str(bundle), "--expected-manifest-sha256", build_report["manifest_sha256"]]
    )
    check_report = json.loads(capsys.readouterr().out)

    assert build_code == 0
    assert check_code == 0
    assert build_report["status"] == STATUS_V1
    assert check_report["status"] == STATUS_V1
    assert check_report["expected_manifest_sha256_matched"] is True
    assert check_report["production_ready"] is False
    assert check_report["public_claim_allowed"] is False


def test_check_cli_rejects_wrong_external_digest(tmp_path: Path, capsys) -> None:
    bundle, _ = _build(tmp_path)

    code = check_tool.main(
        [str(bundle), "--expected-manifest-sha256", "sha256:" + "0" * 64]
    )
    report = json.loads(capsys.readouterr().out)

    assert code == 1
    assert report["status"] == "rejected"
    assert report["error_codes"] == ["EXPECTED_MANIFEST_SHA256_MISMATCH"]
