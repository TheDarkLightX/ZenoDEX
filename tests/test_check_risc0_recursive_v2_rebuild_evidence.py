from __future__ import annotations

import base64
import copy
import hashlib
import inspect
import io
import json
import os
import subprocess
import tarfile
from pathlib import Path
from typing import Any

import pytest

from tools import check_risc0_recursive_v2_rebuild_evidence as checker


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _write(path: Path, raw: bytes) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path


def test_run_pinned_rejects_nonregular_input_with_stable_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable = _write(tmp_path / "candidate", b"candidate")
    monkeypatch.setattr(
        checker,
        "_canonical_path",
        lambda path, *, label, directory: Path(path).resolve(),
    )
    monkeypatch.setattr(checker.stat, "S_ISREG", lambda _mode: False)

    with pytest.raises(checker.EvidenceError, match="EXECUTION_INPUT_INVALID"):
        checker._run_pinned(
            executable,
            {"sha256": _sha256(b"candidate"), "size_bytes": len(b"candidate")},
            [],
            env={"PATH": "/usr/bin:/bin"},
            timeout=1,
        )


def _reference() -> dict[str, Any]:
    return copy.deepcopy(dict(checker.load_reference()))


def _words(value: str) -> list[int]:
    raw = bytes.fromhex(value)
    return [int.from_bytes(raw[index : index + 4], "little") for index in range(0, 32, 4)]


def _source_fixture(tmp_path: Path) -> tuple[dict[str, Any], Path]:
    reference = _reference()
    for row in reference["source_compile"]["files"]:
        source = checker.ROOT / row["path"]
        _write(tmp_path / row["path"], source.read_bytes())
    return reference, tmp_path


def _artifact_fixture(
    tmp_path: Path, role: str = "inner"
) -> tuple[dict[str, Any], Path, dict[str, Any]]:
    reference = _reference()
    pair = reference["proof_pair"]
    role_ref = pair[role]
    security = pair["receipt_security"]
    receipt = {
        "inner": {
            "Succinct": {
                "control_id": _words(security["control_id"]),
                "hashfn": security["hashfn"],
                "verifier_parameters": _words(security["verifier_parameters"]),
            }
        },
        "journal": {"bytes": [1, 2, 3]},
        "metadata": {"verifier_parameters": _words(security["verifier_parameters"])},
    }
    receipt_bytes = json.dumps(receipt, sort_keys=True, separators=(",", ":")).encode("ascii")
    journal = {
        "flat_leaf_count": role_ref["flat_leaf_count"],
        "immediate_child_count": role_ref["immediate_child_count"],
        "level": role_ref["level"],
        "profile": role_ref["profile"],
        "self_image_id": reference["program"]["generated_image_id_words"],
        "subtree_node_count": role_ref["subtree_node_count"],
        "tree_height": role_ref["tree_height"],
    }
    artifact = {
        **pair["receipt_artifact_contract"],
        "journal": journal,
        "journal_sha256": role_ref["journal_sha256"],
        "nonclaims": list(checker.EXPECTED_NONCLAIMS),
        "proof": base64.b64encode(receipt_bytes).decode("ascii"),
        "protocol_journal_hash": role_ref["protocol_journal_hash"],
        "receipt_sha256": _sha256(receipt_bytes),
        "risc0_image_id": reference["program"]["image_id"],
    }
    path = tmp_path / f"{role}.json"
    _rewrite_artifact(reference, path, artifact, role, receipt_bytes)
    return reference, path, artifact


def _rewrite_artifact(
    reference: dict[str, Any],
    path: Path,
    artifact: dict[str, Any],
    role: str,
    receipt_bytes: bytes | None = None,
) -> bytes:
    raw = json.dumps(artifact, sort_keys=True, separators=(",", ":")).encode("ascii")
    _write(path, raw)
    role_ref = reference["proof_pair"][role]
    role_ref["file_sha256"] = _sha256(raw)
    role_ref["size_bytes"] = len(raw)
    if receipt_bytes is not None:
        role_ref["receipt_sha256"] = _sha256(receipt_bytes)
        role_ref["receipt_bytes"] = len(receipt_bytes)
        artifact["receipt_sha256"] = role_ref["receipt_sha256"]
        raw = json.dumps(artifact, sort_keys=True, separators=(",", ":")).encode("ascii")
        _write(path, raw)
        role_ref["file_sha256"] = _sha256(raw)
        role_ref["size_bytes"] = len(raw)
    return raw


def _program_fixture(tmp_path: Path) -> tuple[dict[str, Any], Path, dict[str, Path]]:
    reference = _reference()
    target = tmp_path / "target"
    guest = target / (
        "riscv-guest/tau-state-proof-risc0-recursive-v2-methods/"
        "tau-state-proof-risc0-aggregate-v2/riscv32im-risc0-zkvm-elf/release"
    )
    host = target / "x86_64-unknown-linux-gnu/release"
    program = _write(guest / "tau-state-proof-risc0-aggregate-v2.bin", b"combined-program")
    raw_elf = _write(guest / "tau-state-proof-risc0-aggregate-v2", b"raw-elf")
    verifier = _write(host / "verify_recursive_v2_pair", b"verifier")
    two_leaf_verifier = _write(host / "verify_recursive_v2_two_leaf_pair", b"two-leaf-verifier")
    methods = host / "build/tau-state-proof-risc0-recursive-v2-methods-test/out/methods.rs"
    words = reference["program"]["generated_image_id_words"]
    methods_text = (
        f'pub const TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF: &[u8] = include_bytes!("{program}");\n'
        f'pub const TAU_STATE_PROOF_RISC0_AGGREGATE_V2_PATH: &str = "{program}";\n'
        f"pub const TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID: [u32; 8] = {words};\n"
    )
    _write(methods, methods_text.encode("ascii"))
    reference["program"]["program_bytes"] = program.stat().st_size
    reference["program"]["program_sha256"] = _sha256(program.read_bytes())
    reference["program"]["raw_elf"]["size_bytes"] = raw_elf.stat().st_size
    reference["program"]["raw_elf"]["sha256"] = _sha256(raw_elf.read_bytes())
    reference["proof_pair"]["static_verifier"]["size_bytes"] = verifier.stat().st_size
    reference["proof_pair"]["static_verifier"]["sha256"] = _sha256(verifier.read_bytes())
    reference["proof_pair"]["two_leaf_static_verifier"]["size_bytes"] = (
        two_leaf_verifier.stat().st_size
    )
    reference["proof_pair"]["two_leaf_static_verifier"]["sha256"] = _sha256(
        two_leaf_verifier.read_bytes()
    )
    return (
        reference,
        target,
        {
            "methods": methods,
            "program": program,
            "raw_elf": raw_elf,
            "two_leaf_verifier": two_leaf_verifier,
            "verifier": verifier,
        },
    )


def test_committed_reference_is_authenticated_and_claim_limited() -> None:
    reference = checker.load_reference()

    assert (
        checker.reference_canonical_sha256(reference) == checker.EXPECTED_REFERENCE_CANONICAL_SHA256
    )
    assert reference["claims"] == checker.EXPECTED_CLAIMS
    assert reference["source_compile"]["root_sha256"] == (
        "38676d8eb843ba20a0511746552d4d57107be4b7956dd306552095f92cf763dd"
    )
    assert reference["claims"]["production_ready"] is False
    assert reference["claims"]["settlement_authorization"] is False


def test_reference_claim_escalation_rejects() -> None:
    reference = _reference()
    reference["claims"]["production_ready"] = True

    with pytest.raises(checker.EvidenceError, match="REFERENCE_CLAIMS"):
        checker.validate_reference(reference)


def test_reference_trust_root_is_not_caller_supplied() -> None:
    parameters = inspect.signature(checker.check_candidate).parameters

    assert "reference_path" not in parameters
    assert "expected_reference_sha256" not in parameters


def test_exact_cross_workspace_source_closure_accepts(tmp_path: Path) -> None:
    reference, repository = _source_fixture(tmp_path)

    report = checker._check_source(reference, repository)

    assert report["file_count"] == 20
    assert report["root_sha256"] == reference["source_compile"]["root_sha256"]


def test_external_v1_shared_source_mutation_rejects(tmp_path: Path) -> None:
    reference, repository = _source_fixture(tmp_path)
    path = repository / "zk/state_proof_risc0/shared/src/recursive.rs"
    raw = bytearray(path.read_bytes())
    raw[0] ^= 1
    path.write_bytes(raw)

    with pytest.raises(checker.EvidenceError, match="SOURCE_SHA256_MISMATCH"):
        checker._check_source(reference, repository)


def test_declared_include_bytes_payload_mutation_rejects(tmp_path: Path) -> None:
    reference, repository = _source_fixture(tmp_path)
    relative = "zk/recursive_stark_v2_risc0/shared/payload.bin"
    path = _write(repository / relative, b"compiler-visible-payload")
    rows = reference["source_compile"]["files"]
    rows.append(
        {
            "path": relative,
            "sha256": _sha256(path.read_bytes()),
            "size_bytes": path.stat().st_size,
        }
    )
    rows.sort(key=lambda row: row["path"])
    reference["source_compile"]["file_count"] = len(rows)
    reference["source_compile"]["root_sha256"] = checker._source_root(rows)
    raw = bytearray(path.read_bytes())
    raw[0] ^= 1
    path.write_bytes(raw)

    with pytest.raises(checker.EvidenceError, match="SOURCE_SHA256_MISMATCH"):
        checker._check_source(reference, repository)


def test_source_scope_target_directory_rejects(tmp_path: Path) -> None:
    reference, repository = _source_fixture(tmp_path)
    _write(
        repository / "zk/recursive_stark_v2_risc0/shared/target/hidden.bin",
        b"compiler-visible",
    )

    with pytest.raises(checker.EvidenceError, match="SOURCE_TARGET_PRESENT"):
        checker._check_source(reference, repository)


def test_extra_nested_cargo_config_rejects(tmp_path: Path) -> None:
    reference, repository = _source_fixture(tmp_path)
    _write(
        repository / "zk/recursive_stark_v2_risc0/methods/.cargo/config.toml",
        b"[net]\noffline = false\n",
    )

    with pytest.raises(checker.EvidenceError, match="SOURCE_FILE_EXTRA"):
        checker._check_source(reference, repository)


@pytest.mark.skipif(not hasattr(os, "symlink"), reason="symlinks unavailable")
def test_source_symlink_rejects(tmp_path: Path) -> None:
    reference, repository = _source_fixture(tmp_path)
    path = repository / "zk/recursive_stark_v2_risc0/shared/src/lib.rs"
    replacement = path.with_suffix(".copy")
    path.rename(replacement)
    path.symlink_to(replacement.name)

    with pytest.raises(checker.EvidenceError, match="SYMLINK_FORBIDDEN"):
        checker._check_source(reference, repository)


def test_generated_methods_and_both_guest_artifacts_accept(tmp_path: Path) -> None:
    reference, target, _ = _program_fixture(tmp_path)

    report = checker._check_program_and_methods(reference, target)

    assert report["program_sha256"] == reference["program"]["program_sha256"]
    assert report["raw_elf_sha256"] == reference["program"]["raw_elf"]["sha256"]


def test_generated_image_id_word_mutation_rejects(tmp_path: Path) -> None:
    reference, target, paths = _program_fixture(tmp_path)
    first_word = reference["program"]["generated_image_id_words"][0]
    text = (
        paths["methods"]
        .read_text(encoding="ascii")
        .replace(
            str(first_word),
            str(first_word + 1),
            1,
        )
    )
    paths["methods"].write_text(text, encoding="ascii")

    with pytest.raises(checker.EvidenceError, match="GENERATED_IMAGE_ID_MISMATCH"):
        checker._check_program_and_methods(reference, target)


def test_raw_elf_mutation_rejects(tmp_path: Path) -> None:
    reference, target, paths = _program_fixture(tmp_path)
    paths["raw_elf"].write_bytes(b"raw-elf-mutated")

    with pytest.raises(checker.EvidenceError, match="RAW_ELF_SIZE_MISMATCH"):
        checker._check_program_and_methods(reference, target)


def test_receipt_artifact_surface_accepts_exact_claim_scope(tmp_path: Path) -> None:
    reference, path, _ = _artifact_fixture(tmp_path)

    report = checker._check_receipt_artifact(reference, path, role="inner")

    assert report["receipt_sha256"] == reference["proof_pair"]["inner"]["receipt_sha256"]


def test_weakened_nonclaim_list_rejects_even_when_file_hash_is_rebound(tmp_path: Path) -> None:
    reference, path, artifact = _artifact_fixture(tmp_path)
    artifact["nonclaims"] = ["experimental"]
    _rewrite_artifact(reference, path, artifact, "inner")

    with pytest.raises(checker.EvidenceError, match="ARTIFACT_HEADER_MISMATCH"):
        checker._check_receipt_artifact(reference, path, role="inner")


def test_receipt_security_mutation_rejects(tmp_path: Path) -> None:
    reference, path, artifact = _artifact_fixture(tmp_path)
    receipt = json.loads(base64.b64decode(artifact["proof"]))
    receipt["inner"]["Succinct"]["hashfn"] = "sha-256"
    receipt_bytes = json.dumps(receipt, sort_keys=True, separators=(",", ":")).encode("ascii")
    artifact["proof"] = base64.b64encode(receipt_bytes).decode("ascii")
    _rewrite_artifact(reference, path, artifact, "inner", receipt_bytes)

    with pytest.raises(checker.EvidenceError, match="ARTIFACT_RECEIPT_SECURITY"):
        checker._check_receipt_artifact(reference, path, role="inner")


def test_noncanonical_base64_rejects_after_outer_hash_rebind(tmp_path: Path) -> None:
    reference, path, artifact = _artifact_fixture(tmp_path)
    artifact["proof"] = artifact["proof"] + "\n"
    _rewrite_artifact(reference, path, artifact, "inner")

    with pytest.raises(checker.EvidenceError, match="ARTIFACT_RECEIPT_BASE64"):
        checker._check_receipt_artifact(reference, path, role="inner")


def test_unknown_artifact_field_rejects(tmp_path: Path) -> None:
    reference, path, artifact = _artifact_fixture(tmp_path)
    artifact["unknown_critical"] = True
    _rewrite_artifact(reference, path, artifact, "inner")

    with pytest.raises(checker.EvidenceError, match="ARTIFACT_SCHEMA"):
        checker._check_receipt_artifact(reference, path, role="inner")


def _proxy_fixture(tmp_path: Path) -> tuple[Path, list[str], dict[str, str], Path]:
    workspace = tmp_path / "workspace"
    manifest = _write(workspace / "methods/aggregate_v2/Cargo.toml", b"[package]\nname='x'\n")
    build_target = tmp_path / "build-target"
    nested_target = build_target / "riscv-guest/test"
    nested_target.mkdir(parents=True)
    cargo = _write(tmp_path / "pinned-cargo", b"#!/bin/sh\nexit 0\n")
    cargo.chmod(0o700)
    proxy = _write(tmp_path / "cargo", checker.NESTED_CARGO_PROXY.encode("ascii"))
    proxy.chmod(0o700)
    log = tmp_path / "nested.jsonl"
    rustc = tmp_path / "rustc"
    args = [
        "build",
        "--target",
        "riscv32im-risc0-zkvm-elf",
        "--locked",
        "--manifest-path",
        str(manifest),
        "--target-dir",
        str(nested_target),
        "--release",
    ]
    env = {
        "PATH": "/usr/bin:/bin",
        "RUSTC": str(rustc),
        "ZENODEX_BUILD_TARGET": str(build_target),
        "ZENODEX_CARGO_HOME": str(tmp_path / "cargo-home"),
        "ZENODEX_NESTED_CARGO_LOG": str(log),
        "ZENODEX_PINNED_CARGO": str(cargo),
        "ZENODEX_PINNED_CARGO_SHA256": _sha256(cargo.read_bytes()),
        "ZENODEX_PINNED_RUSTC": str(rustc),
        "ZENODEX_WORKSPACE": str(workspace),
    }
    return proxy, args, env, log


def test_nested_cargo_proxy_observes_exact_guest_build(tmp_path: Path) -> None:
    proxy, args, env, log = _proxy_fixture(tmp_path)

    result = subprocess.run(
        [str(proxy), *args],
        cwd=tmp_path / "workspace",
        env=env,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0
    events = checker._read_nested_log(log)
    assert len(events) == 1
    assert events[0]["manifest_relative"] == "methods/aggregate_v2/Cargo.toml"


def test_nested_cargo_proxy_rejects_unlocked_guest_build(tmp_path: Path) -> None:
    proxy, args, env, log = _proxy_fixture(tmp_path)
    args.remove("--locked")

    result = subprocess.run(
        [str(proxy), *args],
        cwd=tmp_path / "workspace",
        env=env,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 97
    assert not log.exists()


def test_nested_cargo_log_rejects_extra_invocation(tmp_path: Path) -> None:
    _, _, _, log = _proxy_fixture(tmp_path)
    event = {
        "argv": ["build"],
        "cargo_sha256": "0" * 64,
        "cwd_relative": ".",
        "manifest_relative": "methods/aggregate_v2/Cargo.toml",
        "rustc": "rustc",
        "target_relative": "guest",
    }
    raw = json.dumps(event, sort_keys=True, separators=(",", ":")).encode("ascii") + b"\n"
    _write(log, raw + raw)

    with pytest.raises(checker.EvidenceError, match="NESTED_CARGO_EVENT_COUNT"):
        checker._read_nested_log(log)


def test_crate_archive_parser_accepts_regular_files() -> None:
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:gz") as archive:
        data = b"pub fn checked() {}\n"
        info = tarfile.TarInfo("example-1.0.0/src/lib.rs")
        info.size = len(data)
        archive.addfile(info, io.BytesIO(data))

    files = checker._crate_archive_files(buffer.getvalue(), "example-1.0.0")

    assert files == {"src/lib.rs": _sha256(data)}


def test_crate_archive_parser_rejects_parent_traversal() -> None:
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:gz") as archive:
        data = b"escape"
        info = tarfile.TarInfo("example-1.0.0/../escape")
        info.size = len(data)
        archive.addfile(info, io.BytesIO(data))

    with pytest.raises(checker.EvidenceError, match="CRATE_ARCHIVE_PATH"):
        checker._crate_archive_files(buffer.getvalue(), "example-1.0.0")


def test_clean_observation_rejects_missing_nested_event(tmp_path: Path) -> None:
    observation = {
        "nested_cargo_events": [],
        "outer_cargo_sha256": "0" * 64,
        "pinned_rustc": "rustc",
        "target_was_absent": True,
    }

    with pytest.raises(checker.EvidenceError, match="NESTED_CARGO_EVENT_COUNT"):
        checker._validate_clean_observation(observation, _reference(), checker.ROOT, tmp_path)
