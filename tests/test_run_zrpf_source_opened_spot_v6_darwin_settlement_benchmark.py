from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path

import pytest

from tools import run_zrpf_source_opened_spot_v6_darwin_settlement_benchmark as worker


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode()


def _write(root: Path, relative: str, raw: bytes) -> dict[str, object]:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return {
        "path": relative,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "size_bytes": len(raw),
    }


def task_fixture(tmp_path: Path) -> tuple[Path, dict[str, object]]:
    root = tmp_path / "task"
    source_envelope = _write(root, "inputs/leaf_source_envelope.bin", b"source-envelope")
    l2_receipt = _write(root, "inputs/l2_receipt.json", b'{"receipt":1}')
    programs = []
    for index, (role, filename, image_id) in enumerate(
        (
            ("level_two", "spot_value_aggregate_l2_v6.bin", "33" * 32),
            ("settlement", "source_opened_spot_settlement_v6.bin", "44" * 32),
        ),
        start=1,
    ):
        artifact = _write(root, f"programs/{filename}", b"R0BF" + bytes([index]) * 32)
        programs.append({"role": role, "image_id": image_id, **artifact})
    local_files = {
        "local-chain/leaf.receipt.json": _write(
            root, "local-chain/leaf.receipt.json", b'{"leaf":1}'
        ),
        "local-chain/leaf.report.json": _write(
            root, "local-chain/leaf.report.json", b'{"leaf_report":1}'
        ),
        "local-chain/l1.receipt.json": _write(
            root, "local-chain/l1.receipt.json", b'{"l1":1}'
        ),
        "local-chain/l1.report.json": _write(
            root, "local-chain/l1.report.json", b'{"l1_report":1}'
        ),
        "local-chain/l2.report.json": _write(
            root, "local-chain/l2.report.json", b'{"l2_report":1}'
        ),
        "local-chain/linux-cpu-timing-summary.json": _write(
            root, "local-chain/linux-cpu-timing-summary.json", b'{"timing":1}'
        ),
    }
    chain_inventory = [
        {"stage": "source_envelope", **source_envelope},
        {"stage": "leaf_receipt", **local_files["local-chain/leaf.receipt.json"]},
        {"stage": "leaf_report", **local_files["local-chain/leaf.report.json"]},
        {"stage": "level_one_receipt", **local_files["local-chain/l1.receipt.json"]},
        {"stage": "level_one_report", **local_files["local-chain/l1.report.json"]},
        {"stage": "level_two_receipt", **l2_receipt},
        {"stage": "level_two_report", **local_files["local-chain/l2.report.json"]},
        {
            "stage": "publisher_timing_summary",
            **local_files["local-chain/linux-cpu-timing-summary.json"],
        },
    ]
    chain_manifest_value = {
        "artifacts": chain_inventory,
        "claims": {
            "cross_host_reproducible_proof_generation": False,
            "production_authority": False,
            "release_authority": False,
            "settlement_authority": False,
        },
        "completed_chain_tip": {
            "image_id": "33" * 32,
            "receipt_sha256": l2_receipt["sha256"],
            "stage": "level_two",
        },
        "nonclaims": [],
        "schema": "zenodex/zrpf_v6_local_candidate_chain_manifest/v1",
    }
    chain_manifest = _write(
        root, "local-chain/manifest.json", _canonical(chain_manifest_value)
    )
    local_files = {"local-chain/manifest.json": chain_manifest, **local_files}
    guest_record_value = {
        "programs": [
            {
                "image_id_hex": program["image_id"],
                "program_binary_bytes": program["size_bytes"],
                "program_binary_sha256": program["sha256"],
                "stage": stage,
            }
            for program, stage in zip(
                programs,
                ("spot_value_aggregate_l2_v6", "source_opened_spot_settlement_v6"),
                strict=True,
            )
        ],
        "schema": "zenodex/zrpf_source_opened_spot_v6_build_record/v3",
    }
    guest_build_record = _write(
        root, worker.GUEST_BUILD_RECORD_PATH, _canonical(guest_record_value)
    )
    document: dict[str, object] = {
        "schema": worker.TASK_SCHEMA,
        "task_id": "0" * 64,
        "worker_source": {
            "commit": "a" * 40,
            "tree": "b" * 40,
            "governed_tree_listing_sha256": "c" * 64,
            "governed_file_count": 123,
        },
        "guest_build_record": guest_build_record,
        "local_chain_artifacts": [local_files[path] for path in worker.LOCAL_CHAIN_PATHS],
        "workspace": {
            "cargo_lock_sha256": "55" * 32,
            "manifest_path": "zk/zrpf_risc0/Cargo.toml",
            "package": "zenodex-zrpf-risc0-harness",
            "features": ["spot-v6-methods"],
        },
        "toolchain": {
            "host_target": "aarch64-apple-darwin",
            "risc0_zkvm_version": "3.0.5",
            "r0vm_version": worker.EXPECTED_R0VM_VERSION,
            "cargo_risczero_version": worker.EXPECTED_CARGO_RISCZERO_VERSION,
            "rustc_version": worker.EXPECTED_RUSTC_VERSION,
            "cargo_version": worker.EXPECTED_CARGO_VERSION,
        },
        "limits": {
            "build_timeout_seconds": 7_200,
            "stage_timeout_seconds": 86_400,
            "max_virtual_address_space_bytes": 120 * 1024**3,
            "max_output_capture_bytes": 128 * 1024,
            "max_stage_artifact_bytes": 64 * 1024**2,
            "max_total_candidate_artifact_bytes": 192 * 1024**2,
            "max_open_files": 1_024,
            "max_processes": 2_048,
        },
        "inputs": {
            "source_envelope": source_envelope,
            "l2_receipt": l2_receipt,
        },
        "programs": programs,
        "expected_output_inventory": list(worker.ARTIFACT_NAMES),
        "claims": {field: False for field in worker.AUTHORITY_CLAIMS},
        "nonclaims": list(worker.NONCLAIMS),
    }
    document["task_id"] = worker.derive_task_id(document)
    manifest = root / "task.json"
    manifest.write_bytes(_canonical(document))
    return manifest, document


def _tool_observations(document: dict[str, object]) -> dict[str, str]:
    toolchain = document["toolchain"]
    assert isinstance(toolchain, dict)
    return {field: str(toolchain[field]) for field in worker.TOOL_OBSERVATION_FIELDS}


def _settlement_report(
    task: worker.Task, artifacts: dict[str, bytes]
) -> dict[str, object]:
    return {
        "action_count": 1,
        "admission_journal_bytes": len(artifacts["settlement_admission_journal.bin"]),
        "admission_journal_sha256": hashlib.sha256(
            artifacts["settlement_admission_journal.bin"]
        ).hexdigest(),
        "consumed_object_count": 1,
        "data_availability_certificate_bytes": len(
            artifacts["settlement_da_certificate.bin"]
        ),
        "data_availability_certificate_sha256": hashlib.sha256(
            artifacts["settlement_da_certificate.bin"]
        ).hexdigest(),
        "guest_input_bytes": len(artifacts["settlement_guest_input.bin"]),
        "guest_input_sha256": hashlib.sha256(
            artifacts["settlement_guest_input.bin"]
        ).hexdigest(),
        "image_id": task.programs["settlement"].image_id,
        "l2_receipt_sha256": task.inputs["l2_receipt"].sha256,
        "mutation_receipt_sha256": hashlib.sha256(
            artifacts["settlement_mutation_receipt.json"]
        ).hexdigest(),
        "mutation_rejected": True,
        "nonclaims": list(worker.SETTLEMENT_NONCLAIMS),
        "ok": True,
        "receipt_bytes": len(artifacts["settlement_receipt.json"]),
        "receipt_sha256": hashlib.sha256(
            artifacts["settlement_receipt.json"]
        ).hexdigest(),
        "replay_bytes": len(artifacts["settlement_replay.bin"]),
        "replay_sha256": hashlib.sha256(artifacts["settlement_replay.bin"]).hexdigest(),
        "schema": worker.SETTLEMENT_REPORT_SCHEMA,
        "settlement_claim_binding": "66" * 32,
        "settlement_program_id": task.programs["settlement"].image_id,
        "settlement_program_manifest_root": "77" * 32,
        "source_envelope_sha256": task.inputs["source_envelope"].sha256,
        "status": worker.SETTLEMENT_STATUS,
        "succinct_receipt_profile_id": worker.SETTLEMENT_PROFILE,
    }


def test_task_manifest_is_exact_canonical_and_content_addressed(tmp_path: Path) -> None:
    manifest, expected = task_fixture(tmp_path)

    task = worker.load_task(manifest, verify_checkout=False)

    assert task.document == expected
    assert task.task_id == expected["task_id"]
    assert tuple(task.inputs) == worker.TASK_INPUT_KEYS
    assert tuple(task.programs) == worker.PROGRAM_ROLES


@pytest.mark.parametrize(
    "mutation",
    (
        lambda value: value.update({"unknown": True}),
        lambda value: value["claims"].update({"production_authority": True}),
        lambda value: value["limits"].update({"stage_timeout_seconds": 0}),
        lambda value: value["programs"][0].update({"image_id": "0" * 64}),
        lambda value: value["inputs"]["source_envelope"].update({"size_bytes": 999}),
        lambda value: value["expected_output_inventory"].reverse(),
    ),
)
def test_task_manifest_rejects_mutated_authority_or_identity(
    tmp_path: Path, mutation: object
) -> None:
    manifest, document = task_fixture(tmp_path)
    mutated = copy.deepcopy(document)
    mutation(mutated)  # type: ignore[operator]
    mutated["task_id"] = worker.derive_task_id(mutated)
    manifest.write_bytes(_canonical(mutated))

    with pytest.raises(worker.WorkerError):
        worker.load_task(manifest, verify_checkout=False)


def test_task_manifest_rejects_noncanonical_bytes(tmp_path: Path) -> None:
    manifest, document = task_fixture(tmp_path)
    manifest.write_text(json.dumps(document, indent=2) + "\n")

    with pytest.raises(worker.WorkerError, match="canonical"):
        worker.load_task(manifest, verify_checkout=False)


def test_task_manifest_rejects_duplicate_keys(tmp_path: Path) -> None:
    manifest, document = task_fixture(tmp_path)
    canonical = _canonical(document).decode()
    manifest.write_text(canonical.replace('{"claims":', '{"schema":"duplicate","claims":', 1))

    with pytest.raises(worker.WorkerError, match="duplicate JSON key"):
        worker.load_task(manifest, verify_checkout=False)


@pytest.mark.parametrize("constant", ("NaN", "Infinity", "-Infinity"))
def test_task_manifest_rejects_nonfinite_json_number(tmp_path: Path, constant: str) -> None:
    manifest, _document = task_fixture(tmp_path)
    manifest.write_bytes(b'{"value":' + constant.encode() + b"}\n")

    with pytest.raises(worker.WorkerError, match="non-finite JSON number"):
        worker.load_task(manifest, verify_checkout=False)


def test_apple_silicon_machine_name_maps_to_rust_target() -> None:
    assert worker._canonical_darwin_host_target("arm64") == "aarch64-apple-darwin"
    assert worker._canonical_darwin_host_target("aarch64") == "aarch64-apple-darwin"
    with pytest.raises(worker.WorkerError):
        worker._canonical_darwin_host_target("x86_64")


def test_bounded_quiet_command_allows_empty_stdout(tmp_path: Path) -> None:
    limits = {
        "max_open_files": 256,
        "max_processes": 65_536,
        "max_virtual_address_space_bytes": 4 * 1024**3,
        "max_stage_artifact_bytes": 1024 * 1024,
    }
    stdout, stderr, observed_rss = worker._run_bounded(
        ("/bin/sh", "-c", "exit 0"),
        cwd=tmp_path,
        environment={"PATH": os.environ.get("PATH", "/usr/bin:/bin")},
        timeout_seconds=10,
        capture_limit=1024,
        limits=limits,
        capture_root=tmp_path,
        label="quiet",
        require_stdout=False,
    )

    assert stdout == b""
    assert stderr == b""
    assert observed_rss >= 0


def test_bounded_command_kills_and_rejects_residual_process_group(tmp_path: Path) -> None:
    limits = {
        "max_open_files": 256,
        "max_processes": 65_536,
        "max_virtual_address_space_bytes": 4 * 1024**3,
        "max_stage_artifact_bytes": 1024 * 1024,
    }
    with pytest.raises(worker.WorkerError, match="residual process"):
        worker._run_bounded(
            ("/bin/sh", "-c", "sleep 60 </dev/null >/dev/null 2>&1 &"),
            cwd=tmp_path,
            environment={"PATH": os.environ.get("PATH", "/usr/bin:/bin")},
            timeout_seconds=10,
            capture_limit=1024,
            limits=limits,
            capture_root=tmp_path,
            label="residual",
            require_stdout=False,
        )


def test_task_manifest_rejects_changed_input_after_hashing(tmp_path: Path) -> None:
    manifest, _document = task_fixture(tmp_path)
    source = manifest.parent / "inputs/leaf_source_envelope.bin"
    source.write_bytes(b"changed")

    with pytest.raises(worker.WorkerError, match="source_envelope"):
        worker.load_task(manifest, verify_checkout=False)


def test_task_manifest_rejects_program_symlink(tmp_path: Path) -> None:
    manifest, _document = task_fixture(tmp_path)
    program = manifest.parent / "programs/spot_value_aggregate_l2_v6.bin"
    replacement = manifest.parent / "programs/replacement.bin"
    program.rename(replacement)
    program.symlink_to(replacement.name)

    with pytest.raises(worker.WorkerError, match="cannot be opened safely"):
        worker.load_task(manifest, verify_checkout=False)


def test_prebuilt_manifest_binds_exact_two_programs(tmp_path: Path) -> None:
    manifest, _document = task_fixture(tmp_path)
    task = worker.load_task(manifest, verify_checkout=False)
    output = tmp_path / "prebuilt.json"

    worker.write_prebuilt_methods_manifest(task, output)

    value = json.loads(output.read_bytes())
    assert value["schema"] == worker.PREBUILT_METHODS_SCHEMA
    assert value["profile"] == "settlement_only_v1"
    assert [row["role"] for row in value["programs"]] == list(worker.PROGRAM_ROLES)
    assert [row["file"] for row in value["programs"]] == [
        worker.PROGRAM_ARTIFACTS[role] for role in worker.PROGRAM_ROLES
    ]
    assert output.read_bytes() == _canonical(value)
    assert (output.parent / worker.PROGRAM_ARTIFACTS["level_two"]).read_bytes().startswith(
        b"R0BF"
    )
    assert (output.parent / worker.PROGRAM_ARTIFACTS["settlement"]).read_bytes().startswith(
        b"R0BF"
    )


def test_output_bundle_is_revalidated_before_acceptance(tmp_path: Path) -> None:
    manifest, document = task_fixture(tmp_path)
    task = worker.load_task(manifest, verify_checkout=False)
    root = tmp_path / "output"
    artifacts = {name: name.encode() for name in worker.ARTIFACT_NAMES}
    report = b'{"ok":true}\n'
    worker.persist_candidate_bundle_for_test(
        task=task,
        output_directory=root,
        artifacts=artifacts,
        settlement_report=report,
        elapsed_milliseconds=10,
        children_max_rss_observation_bytes=20,
        cargo_build_stderr_sha256=hashlib.sha256(b"").hexdigest(),
        executable_identities={
            role: {"sha256": "99" * 32, "size_bytes": 1} for role in worker.EXECUTABLE_ROLES
        },
        tool_observations=_tool_observations(document),
    )

    checked = worker.validate_candidate_bundle(root, task, semantic_validator=lambda *_: True)
    assert checked["ok"] is True
    assert checked["production_authority"] is False

    (root / "artifacts/settlement_receipt.json").write_bytes(b"changed")
    with pytest.raises(worker.WorkerError, match="SHA-256"):
        worker.validate_candidate_bundle(root, task, semantic_validator=lambda *_: True)


@pytest.mark.parametrize("artifact_name", worker.ARTIFACT_NAMES)
def test_semantic_validator_binds_every_settlement_artifact(
    tmp_path: Path, artifact_name: str
) -> None:
    manifest, _document = task_fixture(tmp_path)
    task = worker.load_task(manifest, verify_checkout=False)
    artifacts = {name: name.encode() for name in worker.ARTIFACT_NAMES}
    report = _canonical(_settlement_report(task, artifacts))
    assert worker._semantic_candidate_validator(task, artifacts, report, {})

    mutated = dict(artifacts)
    mutated[artifact_name] += b"-mutation"
    assert not worker._semantic_candidate_validator(task, mutated, report, {})


def test_worker_report_cannot_promote_authority(tmp_path: Path) -> None:
    manifest, document = task_fixture(tmp_path)
    task = worker.load_task(manifest, verify_checkout=False)

    report = worker.candidate_worker_report(
        task=task,
        artifacts={name: name.encode() for name in worker.ARTIFACT_NAMES},
        settlement_report=b'{"ok":true}\n',
        elapsed_milliseconds=1,
        children_max_rss_observation_bytes=1,
        cargo_build_stderr_sha256=hashlib.sha256(b"").hexdigest(),
        executable_identities={
            role: {"sha256": "99" * 32, "size_bytes": 1} for role in worker.EXECUTABLE_ROLES
        },
        tool_observations=_tool_observations(document),
    )

    assert all(report[field] is False for field in worker.AUTHORITY_CLAIMS)
    assert report["firecracker_executed"] is False
    assert report["sandbox_authority"] is False
    assert report["status"] == "darwin_m3_settlement_benchmark_authority_false"


def test_failed_candidate_persistence_leaves_no_published_output(tmp_path: Path) -> None:
    manifest, document = task_fixture(tmp_path)
    task = worker.load_task(manifest, verify_checkout=False)
    output = tmp_path / "candidate"
    artifacts = {name: name.encode() for name in worker.ARTIFACT_NAMES}
    artifacts[worker.ARTIFACT_NAMES[0]] = b""

    with pytest.raises(worker.WorkerError, match="empty"):
        worker.persist_candidate_bundle_for_test(
            task=task,
            output_directory=output,
            artifacts=artifacts,
            settlement_report=b'{"ok":true}\n',
            elapsed_milliseconds=1,
            children_max_rss_observation_bytes=1,
            cargo_build_stderr_sha256=hashlib.sha256(b"").hexdigest(),
            executable_identities={
                role: {"sha256": "99" * 32, "size_bytes": 1}
                for role in worker.EXECUTABLE_ROLES
            },
            tool_observations=_tool_observations(document),
        )

    assert not output.exists()
    assert not list(tmp_path.glob(".candidate.staging-*"))
