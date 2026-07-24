from __future__ import annotations

import ast
import copy
import hashlib
import os
import subprocess
import sys
import time
from dataclasses import replace
from pathlib import Path
from typing import Any, Sequence, cast

import pytest

from tests import test_check_zrpf_initial_paid_calibration_attempt_v1 as paid_fixture
from tests import test_plan_zrpf_remote_reproof_handoff_v2 as handoff_fixture
from tools import check_zrpf_initial_paid_calibration_attempt_v1 as paid_calibration
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools import run_zrpf_remote_reproof_worker_v2 as worker
from tools import zrpf_paid_run_prerequisites_v1 as paid_shared
from tools import zrpf_remote_reproof_stage_publication_marker_v1 as publication_marker
from tools import zrpf_remote_reproof_worker_v2_publication as publication


def _stage_context(
    tmp_path: Path,
    stage_id: str = "v6_l1_receipt",
    prover_compute_profile_id: str = handoff.CPU_PROVER_COMPUTE_PROFILE_ID,
) -> tuple[Path, list[str], dict[str, Any], Path, Path, dict[str, Any]]:
    repo, chain = handoff_fixture._ancestry_repo(tmp_path)
    subprocess.run(["git", "-C", str(repo), "reset", "--hard", "-q", chain[3]], check=True)
    plan = handoff_fixture._plan_for_chain(repo, chain, prover_compute_profile_id)
    artifact_root = tmp_path / "artifacts"
    handoff_fixture._write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    handoff_fixture._write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    task = next(row for row in plan["tasks"] if row["stage_id"] == stage_id)
    packet_path = packet_directory / f"{task['ordinal']:02d}-{stage_id}.json"
    packet = handoff.load_canonical_json(packet_path, "execution packet")
    assert isinstance(packet, dict)
    marker_path = artifact_root / publication_marker.stage_publication_marker_relative_path_v1(
        int(task["ordinal"]), stage_id
    )
    marker_path.unlink()
    return repo, chain, plan, artifact_root, packet_path, cast(dict[str, Any], packet)


def _fake_v6_l1_success(
    command: worker.ResolvedCommand,
    _policy: worker.ResourcePolicy,
    _environment: dict[str, str],
    _cwd: Path,
) -> worker.ProcessResult:
    argv = list(command.argv)
    receipt_path = Path(argv[argv.index("--receipt-out") + 1])
    receipt_path.write_bytes(b"receipt\n")
    return worker.ProcessResult(
        stdout=b'{"status":"candidate"}\n',
        stderr=b"bounded diagnostic\n",
        exit_code=0,
        duration_milliseconds=1,
    )


def _capture_v6_l1(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[Path, dict[str, Any], Path, Path, dict[str, Any]]:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(tmp_path)
    monkeypatch.setattr(worker, "_run_bounded_command", _fake_v6_l1_success)
    run_root = tmp_path / "run"
    capture = worker.execute_stage(plan, packet, repo, artifact_root, run_root)
    return repo, plan, artifact_root, run_root, capture


def _remove_captured_artifacts(artifact_root: Path, capture: dict[str, Any]) -> list[Path]:
    paths = [artifact_root / str(row["path"]) for row in capture["outputs"]]
    for path in paths:
        path.unlink()
    return paths


def _refresh_fixture_publication_marker(
    plan: dict[str, Any],
    artifact_root: Path,
    packet_directory: Path,
    stage_id: str,
) -> None:
    task = next(row for row in plan["tasks"] if row["stage_id"] == stage_id)
    packet = handoff.load_canonical_json(
        packet_directory / f"{task['ordinal']:02d}-{stage_id}.json",
        "execution packet",
    )
    assert isinstance(packet, dict)
    contracts = {
        row["contract_id"]: row for row in cast(list[dict[str, Any]], plan["artifact_contracts"])
    }
    outputs = [
        handoff._artifact_record(contracts[contract_id], artifact_root)
        for contract_id in task["output_artifact_contract_ids"]
    ]
    marker = publication_marker.build_stage_publication_marker_v1(
        handoff_id=str(plan["handoff_id"]),
        execution_packet_id=str(packet["execution_packet_id"]),
        task_id=str(task["task_id"]),
        stage_id=stage_id,
        ordinal=int(task["ordinal"]),
        capture_id=hashlib.sha256(f"refreshed:{stage_id}".encode("ascii")).hexdigest(),
        outputs=outputs,
    )
    marker_path = artifact_root / publication_marker.stage_publication_marker_relative_path_v1(
        int(task["ordinal"]), stage_id
    )
    marker_path.write_bytes(publication_marker.canonical_json_bytes_v1(marker))


def test_worker_executes_exact_packet_into_clean_output_stage(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet_path = tmp_path / "packets/07-v6_l1_receipt.json"
    packet = handoff.load_canonical_json(packet_path, "execution packet")
    assert isinstance(packet, dict)
    assert capture["capture_id"] == worker.derive_capture_id(capture)
    assert capture["authority"] == worker.false_authority()
    assert capture["prover_compute_profile"]["profile_id"] == (
        handoff.CPU_PROVER_COMPUTE_PROFILE_ID
    )
    assert [row["role"] for row in capture["outputs"]] == [
        "v6_l1_receipt",
        "v6_l1_report",
    ]
    assert (run_root / "outputs/proofs/v6_l1_receipt.json").read_bytes() == b"receipt\n"
    assert (run_root / "outputs/proofs/v6_l1_report.json").read_bytes().startswith(b"{")
    worker.validate_worker_capture(
        plan,
        cast(dict[str, Any], packet),
        capture,
        repo,
        artifact_root,
        run_root,
    )


def test_publish_stage_validates_capture_and_commits_exact_declared_outputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)

    records, marker = worker.publish_stage_outputs(
        plan,
        cast(dict[str, Any], packet),
        capture,
        repo,
        artifact_root,
        run_root,
    )

    assert records == capture["outputs"]
    marker_path = artifact_root / publication_marker.stage_publication_marker_relative_path_v1(
        7, "v6_l1_receipt"
    )
    assert marker_path.read_bytes() == publication_marker.canonical_json_bytes_v1(marker)
    assert marker["execution_packet_id"] == packet["execution_packet_id"]
    assert [path.read_bytes() for path in published_paths] == [
        b"receipt\n",
        b'{"status":"candidate"}\n',
    ]
    assert [path.stat().st_mode & 0o777 for path in published_paths] == [0o400, 0o400]


def test_publication_effect_module_does_not_import_worker_orchestrator() -> None:
    module_file = publication.__file__
    assert module_file is not None
    source_path = Path(module_file)
    syntax = ast.parse(source_path.read_text(encoding="utf-8"))
    imported_modules: set[str] = set()
    for node in ast.walk(syntax):
        if isinstance(node, ast.Import):
            imported_modules.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            module = node.module or ""
            imported_modules.update(f"{module}.{alias.name}" for alias in node.names)

    assert "tools.run_zrpf_remote_reproof_worker_v2" not in imported_modules


def test_publish_stage_rejects_invalid_capture_before_filesystem_effect(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    invalid = copy.deepcopy(capture)
    invalid["capture_id"] = "0" * 64

    with pytest.raises(worker.WorkerError, match="capture ID"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            invalid,
            repo,
            artifact_root,
            run_root,
        )

    assert all(not path.exists() for path in published_paths)


def test_publish_stage_rejects_existing_destination_without_overwrite(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    published_paths[0].write_bytes(b"preexisting\n")

    with pytest.raises(worker.WorkerError, match="destination must begin absent"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert published_paths[0].read_bytes() == b"preexisting\n"
    assert not published_paths[1].exists()


def test_publish_stage_atomic_no_replace_rejects_destination_race(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    link_noreplace = publication._link_fd_noreplace
    raced = False

    def race_destination(file_fd: int, directory_fd: int, destination_name: str) -> None:
        nonlocal raced
        if not raced:
            raced = True
            descriptor = os.open(
                destination_name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                0o600,
                dir_fd=directory_fd,
            )
            try:
                os.write(descriptor, b"racer\n")
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        link_noreplace(file_fd, directory_fd, destination_name)

    monkeypatch.setattr(publication, "_link_fd_noreplace", race_destination)

    with pytest.raises(worker.WorkerError, match="destination must begin absent"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert published_paths[0].read_bytes() == b"racer\n"
    assert not published_paths[1].exists()


def test_publish_stage_rejects_output_mutation_after_temporary_write(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    write_temporaries = publication._write_output_temporaries
    captured_output = run_root / "outputs/proofs/v6_l1_receipt.json"

    def mutate_after_temporary_write(
        prepared: Sequence[publication.PreparedPublication],
        stage: publication.ValidatedStage,
        output_root: Path,
        expected_outputs: Sequence[dict[str, object]],
    ) -> None:
        write_temporaries(prepared, stage, output_root, expected_outputs)
        captured_output.unlink()
        captured_output.write_bytes(b"substituted\n")

    monkeypatch.setattr(
        publication,
        "_write_output_temporaries",
        mutate_after_temporary_write,
    )

    with pytest.raises(worker.WorkerError, match="stage output bytes differ"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert all(not path.exists() for path in published_paths)


def test_publish_stage_recomputes_published_records_before_accepting(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    validate_published = publication._validate_published_records

    def reject_after_published_revalidation(
        stage: publication.ValidatedStage,
        root: Path,
        expected_outputs: Sequence[dict[str, object]],
    ) -> None:
        validate_published(stage, root, expected_outputs)
        raise worker.WorkerError("published artifact records differ from validated capture")

    monkeypatch.setattr(
        publication,
        "_validate_published_records",
        reject_after_published_revalidation,
    )

    with pytest.raises(worker.WorkerError, match="differ from validated capture"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert all(path.is_file() for path in published_paths)
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_cli_publish_stage_emits_authority_false_result(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet_path = tmp_path / "packets/07-v6_l1_receipt.json"
    handoff_path = tmp_path / "handoff.json"
    capture_path = tmp_path / "capture.json"
    handoff_path.write_bytes(handoff.canonical_json_bytes(plan))
    capture_path.write_bytes(handoff.canonical_json_bytes(capture))
    published_paths = _remove_captured_artifacts(artifact_root, capture)

    assert (
        worker.main(
            [
                "publish-stage",
                "--repository",
                str(repo),
                "--handoff",
                str(handoff_path),
                "--packet",
                str(packet_path),
                "--artifact-root",
                str(artifact_root),
                "--run-root",
                str(run_root),
                "--capture-output",
                str(capture_path),
            ]
        )
        == 0
    )
    result = handoff.strict_json_loads(capsys.readouterr().out.encode("ascii"))
    expected_marker = publication_marker.build_stage_publication_marker_v1(
        handoff_id=str(capture["handoff_id"]),
        execution_packet_id=str(capture["execution_packet_id"]),
        task_id=str(capture["task_id"]),
        stage_id=str(capture["stage_id"]),
        ordinal=int(capture["ordinal"]),
        capture_id=str(capture["capture_id"]),
        outputs=cast(list[dict[str, object]], capture["outputs"]),
    )

    assert result == {
        "accepted": True,
        "authority": worker.false_authority(),
        "capture_id": capture["capture_id"],
        "published_artifact_ids": [row["artifact_id"] for row in capture["outputs"]],
        "publication_marker_id": expected_marker["content_id"],
    }
    assert all(path.is_file() for path in published_paths)


def test_partial_multi_output_commit_never_exposes_completion_marker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)

    def fail_after_first_output(
        prepared: Sequence[publication.PreparedPublication],
    ) -> None:
        publication._link_owned_temporary(prepared[0])
        publication._fsync_directory(prepared[0].directory_fd)
        raise worker.WorkerError("injected crash after first output")

    monkeypatch.setattr(publication, "_commit_output_publications", fail_after_first_output)
    with pytest.raises(worker.WorkerError, match="injected crash"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert published_paths[0].is_file()
    assert not published_paths[1].exists()
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_publication_uses_only_unnamed_temporaries_and_never_unlinks_a_competitor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    _remove_captured_artifacts(artifact_root, capture)
    competitor = artifact_root / "proofs/.competitor-owned"
    competitor.write_bytes(b"other-publisher-owned\n")
    link_noreplace = publication._link_fd_noreplace
    observed_directory_names: list[list[str]] = []

    def record_unnamed_source(file_fd: int, directory_fd: int, destination_name: str) -> None:
        source = os.fstat(file_fd)
        assert source.st_nlink == 0
        observed_directory_names.append(sorted(os.listdir(directory_fd)))
        link_noreplace(file_fd, directory_fd, destination_name)

    monkeypatch.setattr(publication, "_link_fd_noreplace", record_unnamed_source)
    worker.publish_stage_outputs(
        plan,
        cast(dict[str, Any], packet),
        capture,
        repo,
        artifact_root,
        run_root,
    )

    assert observed_directory_names
    assert all(
        all(not name.startswith(".zrpf-publish-") for name in names)
        for names in observed_directory_names
    )
    assert competitor.read_bytes() == b"other-publisher-owned\n"


def test_publication_marker_is_the_final_exact_descriptor_link(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    _remove_captured_artifacts(artifact_root, capture)
    link_noreplace = publication._link_fd_noreplace
    destinations: list[str] = []

    def record_link(file_fd: int, directory_fd: int, destination_name: str) -> None:
        destinations.append(destination_name)
        link_noreplace(file_fd, directory_fd, destination_name)

    monkeypatch.setattr(publication, "_link_fd_noreplace", record_link)
    worker.publish_stage_outputs(
        plan,
        cast(dict[str, Any], packet),
        capture,
        repo,
        artifact_root,
        run_root,
    )

    assert destinations == [
        "v6_l1_receipt.json",
        "v6_l1_report.json",
        "07-v6_l1_receipt.json",
    ]


def test_unavailable_no_replace_primitive_leaves_marker_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)

    def unavailable(*_args: object) -> None:
        raise worker.WorkerError("atomic no-replace publication is unavailable")

    monkeypatch.setattr(publication, "_link_fd_noreplace", unavailable)
    with pytest.raises(worker.WorkerError, match="no-replace publication is unavailable"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert all(not path.exists() for path in published_paths)
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_final_marker_link_failure_leaves_complete_outputs_without_marker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    link_noreplace = publication._link_fd_noreplace
    calls = 0

    def fail_marker_link(file_fd: int, directory_fd: int, destination_name: str) -> None:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise worker.WorkerError("injected final marker link failure")
        link_noreplace(file_fd, directory_fd, destination_name)

    monkeypatch.setattr(publication, "_link_fd_noreplace", fail_marker_link)
    with pytest.raises(worker.WorkerError, match="final marker link failure"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert all(path.is_file() for path in published_paths)
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_directory_fsync_failure_after_first_output_leaves_marker_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    calls = 0

    def fail_first_directory_fsync(_directory_fd: int) -> None:
        nonlocal calls
        calls += 1
        if calls == 1:
            raise worker.WorkerError("published artifact directory fsync failed")

    monkeypatch.setattr(publication, "_fsync_directory", fail_first_directory_fsync)
    with pytest.raises(worker.WorkerError, match="directory fsync failed"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert published_paths[0].is_file()
    assert not published_paths[1].exists()
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_file_fsync_failure_leaves_outputs_and_marker_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)

    def fail_fsync(_descriptor: int) -> None:
        raise OSError("injected file fsync failure")

    monkeypatch.setattr(publication.os, "fsync", fail_fsync)
    with pytest.raises(worker.WorkerError, match="temporary write failed"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert all(not path.exists() for path in published_paths)
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_late_repo_mutation_blocks_marker_after_output_revalidation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    published_paths = _remove_captured_artifacts(artifact_root, capture)
    validate_published = publication._validate_published_records

    def dirty_repo_after_published_validation(
        stage: publication.ValidatedStage,
        root: Path,
        expected_outputs: Sequence[dict[str, object]],
    ) -> None:
        validate_published(stage, root, expected_outputs)
        (repo / "untracked-after-validation").write_bytes(b"mutation\n")

    monkeypatch.setattr(
        publication,
        "_validate_published_records",
        dirty_repo_after_published_validation,
    )
    with pytest.raises(worker.WorkerError, match="repository must be clean"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert all(path.is_file() for path in published_paths)
    assert not (
        artifact_root
        / publication_marker.stage_publication_marker_relative_path_v1(7, "v6_l1_receipt")
    ).exists()


def test_marker_parent_fsync_failure_is_indeterminate_and_exact_retry_reconciles(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    _remove_captured_artifacts(artifact_root, capture)
    marker_path = artifact_root / publication_marker.stage_publication_marker_relative_path_v1(
        7, "v6_l1_receipt"
    )
    fsync_directory = publication._fsync_directory
    calls = 0

    def fail_marker_parent_fsync(directory_fd: int) -> None:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise worker.WorkerError("injected marker parent fsync failure")
        fsync_directory(directory_fd)

    monkeypatch.setattr(publication, "_fsync_directory", fail_marker_parent_fsync)
    with pytest.raises(publication.PublicationCommitIndeterminate, match="indeterminate"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    assert marker_path.is_file()
    monkeypatch.setattr(publication, "_fsync_directory", fsync_directory)
    records, marker = worker.publish_stage_outputs(
        plan,
        cast(dict[str, Any], packet),
        capture,
        repo,
        artifact_root,
        run_root,
    )
    assert records == capture["outputs"]
    assert marker_path.read_bytes() == publication_marker.canonical_json_bytes_v1(marker)


@pytest.mark.parametrize("destination_name", ("published-output.json", "stage-marker.json"))
@pytest.mark.skipif(not hasattr(os, "mkfifo"), reason="FIFO witness requires POSIX")
def test_publication_reconciliation_rejects_fifo_without_blocking(
    tmp_path: Path,
    destination_name: str,
) -> None:
    publication_root = tmp_path / "publication"
    publication_root.mkdir()
    os.mkfifo(publication_root / destination_name, mode=0o600)
    script = """
import os
import sys
from pathlib import Path
from tools import zrpf_remote_reproof_worker_v2_publication as publication
from tools.zrpf_remote_reproof_worker_v2_contract import WorkerError

root = Path(sys.argv[1])
directory_fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY)
item = publication.PreparedPublication(directory_fd, (), sys.argv[2])
try:
    publication._fsync_linked_publications([item])
except WorkerError as exc:
    if "linked regular file" not in str(exc):
        raise
    raise SystemExit(0)
finally:
    os.close(directory_fd)
raise SystemExit("FIFO publication unexpectedly reconciled")
"""
    completed = subprocess.run(
        [sys.executable, "-c", script, str(publication_root), destination_name],
        cwd=handoff_fixture.REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=2,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr


def test_marker_parent_namespace_replacement_cannot_report_success(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    _remove_captured_artifacts(artifact_root, capture)
    marker_parent = artifact_root / ".zrpf-stage-publications/v1"
    displaced_parent = artifact_root / ".zrpf-stage-publications/displaced-v1"
    link_owned = publication._link_owned_temporary
    calls = 0

    def replace_parent_before_marker_link(
        prepared: publication.PreparedPublication,
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == 3:
            marker_parent.rename(displaced_parent)
            marker_parent.mkdir(mode=0o700)
        link_owned(prepared)

    monkeypatch.setattr(publication, "_link_owned_temporary", replace_parent_before_marker_link)
    with pytest.raises(publication.PublicationCommitIndeterminate, match="indeterminate"):
        worker.publish_stage_outputs(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )

    marker_name = "07-v6_l1_receipt.json"
    assert not (marker_parent / marker_name).exists()
    assert (displaced_parent / marker_name).is_file()


def test_descriptor_cleanup_is_nonthrowing(monkeypatch: pytest.MonkeyPatch) -> None:
    def fail_close(_descriptor: int) -> None:
        raise OSError("injected close failure")

    monkeypatch.setattr(publication.os, "close", fail_close)
    publication._best_effort_close(123)


def test_cli_output_failure_after_commit_is_indeterminate_and_retry_reconciles(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet_path = tmp_path / "packets/07-v6_l1_receipt.json"
    handoff_path = tmp_path / "handoff.json"
    capture_path = tmp_path / "capture.json"
    handoff_path.write_bytes(handoff.canonical_json_bytes(plan))
    capture_path.write_bytes(handoff.canonical_json_bytes(capture))
    _remove_captured_artifacts(artifact_root, capture)
    marker_path = artifact_root / publication_marker.stage_publication_marker_relative_path_v1(
        7, "v6_l1_receipt"
    )
    argv = [
        "publish-stage",
        "--repository",
        str(repo),
        "--handoff",
        str(handoff_path),
        "--packet",
        str(packet_path),
        "--artifact-root",
        str(artifact_root),
        "--run-root",
        str(run_root),
        "--capture-output",
        str(capture_path),
    ]
    emit = worker._emit_committed_publication_result

    def fail_output(_raw: bytes) -> None:
        raise publication.PublicationCommitIndeterminate("injected committed-result output failure")

    monkeypatch.setattr(worker, "_emit_committed_publication_result", fail_output)
    assert worker.main(argv) == 3
    assert "indeterminate:" in capsys.readouterr().err
    assert marker_path.is_file()

    monkeypatch.setattr(worker, "_emit_committed_publication_result", emit)
    assert worker.main(argv) == 0
    retried = handoff.strict_json_loads(capsys.readouterr().out.encode("ascii"))
    assert isinstance(retried, dict)
    assert retried["accepted"] is True
    decoded_marker = handoff.strict_json_loads(marker_path.read_bytes())
    assert isinstance(decoded_marker, dict)
    assert retried["publication_marker_id"] == decoded_marker["content_id"]


def test_publication_roots_must_be_pairwise_disjoint(tmp_path: Path) -> None:
    repository = tmp_path / "repository"
    artifact_root = repository / "artifacts"
    run_root = tmp_path / "run"
    artifact_root.mkdir(parents=True)
    run_root.mkdir()

    with pytest.raises(worker.WorkerError, match="must be disjoint"):
        worker._require_disjoint_roots(repository, artifact_root, run_root)


def test_worker_privately_snapshots_exact_execution_packet_and_rejects_rebinding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    snapshot = run_root / "inputs/execution-packet.json"
    assert snapshot.read_bytes() == handoff.canonical_json_bytes(packet)

    snapshot.chmod(0o600)
    snapshot.write_bytes(handoff.canonical_json_bytes({**packet, "ordinal": 999}))
    with pytest.raises(worker.WorkerError, match="execution packet snapshot changed"):
        worker.validate_worker_capture(
            plan,
            cast(dict[str, Any], packet),
            capture,
            repo,
            artifact_root,
            run_root,
        )


def _source_calibration_context(
    tmp_path: Path,
) -> tuple[
    Path,
    dict[str, Any],
    Path,
    dict[str, Any],
    Path,
    dict[str, Path],
]:
    repo, chain, plan, artifact_root, _packet_path, _stale_packet = _stage_context(
        tmp_path,
        stage_id="source_spot_proof",
        prover_compute_profile_id=(handoff.CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID),
    )
    source_program = artifact_root / "identity/run/outputs/01-source-spot/source_spot.bin"
    prover_r0vm = artifact_root / "inputs/prover-risc0-home/bin/r0vm"
    source_guest_input = artifact_root / "profiles/source_guest_input.bin"
    source_guest_input.write_bytes(b"source-calibration-position-distinct-guest-input\n")

    profile = paid_fixture._profile()
    source_program_raw = source_program.read_bytes()
    prover_r0vm_raw = prover_r0vm.read_bytes()
    guest_input_raw = source_guest_input.read_bytes()
    profile["program"]["artifact"] = {
        "sha256": hashlib.sha256(source_program_raw).hexdigest(),
        "size_bytes": len(source_program_raw),
    }
    profile["r0vm"] = {
        "sha256": hashlib.sha256(prover_r0vm_raw).hexdigest(),
        "size_bytes": len(prover_r0vm_raw),
    }
    profile["guest_input"] = {
        "sha256": hashlib.sha256(guest_input_raw).hexdigest(),
        "size_bytes": len(guest_input_raw),
    }
    profile["profile_record_id"] = paid_fixture.execution_profile._derive_record_id(profile)
    build = paid_fixture._build(profile)
    preflight = paid_fixture._preflight(profile)
    (artifact_root / "profiles/source_execution_profile.json").write_bytes(
        paid_shared.canonical_bytes(profile)
    )
    (artifact_root / "inputs/cuda_r0vm_build_attestation.json").write_bytes(
        paid_shared.canonical_bytes(build)
    )
    (artifact_root / "inputs/h100_preflight.json").write_bytes(
        paid_shared.canonical_bytes(preflight)
    )
    _refresh_fixture_publication_marker(
        plan,
        artifact_root,
        tmp_path / "packets",
        "source_execution_profile",
    )

    packet = handoff.build_execution_packet(
        plan,
        "source_spot_proof",
        artifact_root,
        repo,
        c0_commit=chain[0],
        c1_commit=chain[1],
        c2_commit=chain[2],
        governance_commit=chain[3],
    )
    budget = paid_fixture._budget(profile, build, preflight, packet)
    budget["execution_profile_sha256"] = hashlib.sha256(
        paid_shared.canonical_bytes(profile)
    ).hexdigest()
    budget["attempt_budget_microusd"] = paid_calibration.MAX_ATTEMPT_BUDGET_MICROUSD
    budget["price_microusd_per_hour"] = 2_890_000
    budget["hard_attempt_cap_milliseconds"] = paid_calibration.MAX_HARD_ATTEMPT_CAP_MILLISECONDS
    budget["attempt_budget_record_id"] = paid_calibration.derive_attempt_budget_record_id(budget)
    budget_path = tmp_path / "runtime/attempt-budget-and-price.json"
    budget_path.parent.mkdir(parents=True)
    budget_path.write_bytes(paid_shared.canonical_bytes(budget))
    runtime = {"attempt_budget_and_price": budget_path}
    return repo, plan, artifact_root, packet, tmp_path / "run", runtime


def test_source_proof_cpu_fallback_is_explicitly_disqualified(tmp_path: Path) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(
        tmp_path, stage_id="source_spot_proof"
    )

    with pytest.raises(worker.WorkerError, match="execution adapter is not implemented"):
        worker.execute_stage(plan, packet, repo, artifact_root, tmp_path / "run")


def _run_paid_calibration_checker(command: worker.ResolvedCommand) -> bytes:
    argv = list(command.argv)
    result = paid_calibration.check_qualification(
        Path(argv[argv.index("--source-execution-profile") + 1]),
        Path(argv[argv.index("--cuda-r0vm-build-attestation") + 1]),
        Path(argv[argv.index("--h100-preflight") + 1]),
        Path(argv[argv.index("--source-execution-packet") + 1]),
        Path(argv[argv.index("--attempt-budget-and-price") + 1]),
        trusted_current_epoch_seconds=int(argv[argv.index("--trusted-current-epoch-seconds") + 1]),
    )
    return paid_calibration.canonical_bytes(result) + b"\n"


def test_source_proof_runs_only_after_exact_paid_gate_and_uses_derived_deadline(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, packet, run_root, runtime = _source_calibration_context(tmp_path)
    seen: list[tuple[str, int]] = []

    def fake_source_calibration(
        command: worker.ResolvedCommand,
        policy: worker.ResourcePolicy,
        _environment: dict[str, str],
        _cwd: Path,
    ) -> worker.ProcessResult:
        argv = list(command.argv)
        if "tools/check_zrpf_initial_paid_calibration_attempt_v1.py" in argv:
            seen.append(("paid_gate", policy.timeout_seconds))
            return worker.ProcessResult(_run_paid_calibration_checker(command), b"", 0, 1)
        if "tools/check_zrpf_stage_execution_profile_v1.py" in argv:
            seen.append(("profile_gate", policy.timeout_seconds))
            return worker.ProcessResult(b"", b"", 0, 1)
        seen.append(("source_proof", policy.timeout_seconds))
        return worker.ProcessResult(b'{"candidate_receipt":"source"}\n', b"", 0, 2)

    monkeypatch.setattr(worker, "_run_bounded_command", fake_source_calibration)
    capture = worker.execute_stage(
        plan,
        packet,
        repo,
        artifact_root,
        run_root,
        runtime_bindings=runtime,
        trusted_current_epoch_seconds=paid_fixture.CURRENT_EPOCH,
    )

    assert seen == [("paid_gate", 60), ("profile_gate", 60), ("source_proof", 1_800)]
    outputs = {row["role"]: row for row in cast(list[dict[str, Any]], capture["outputs"])}
    assert outputs["source_calibration_qualification"]["size_bytes"] > 0
    assert outputs["source_proof"]["size_bytes"] > 0
    assert (run_root / "inputs/runtime/attempt-budget-and-price.json").read_bytes() == runtime[
        "attempt_budget_and_price"
    ].read_bytes()

    over_deadline = copy.deepcopy(capture)
    over_deadline_commands = cast(list[dict[str, object]], over_deadline["commands"])
    over_deadline_commands[-1]["duration_milliseconds"] = 1_800_001
    over_deadline["capture_id"] = worker.derive_capture_id(over_deadline)
    with pytest.raises(worker.WorkerError, match="duration exceeds"):
        worker.validate_worker_capture(
            plan,
            packet,
            over_deadline,
            repo,
            artifact_root,
            run_root,
            runtime_bindings=runtime,
            trusted_current_epoch_seconds=paid_fixture.CURRENT_EPOCH,
        )


def test_source_proof_never_starts_when_paid_gate_output_is_rebound(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, packet, run_root, runtime = _source_calibration_context(tmp_path)
    proof_started = False

    def rebound_paid_gate(
        command: worker.ResolvedCommand,
        _policy: worker.ResourcePolicy,
        _environment: dict[str, str],
        _cwd: Path,
    ) -> worker.ProcessResult:
        nonlocal proof_started
        argv = list(command.argv)
        if "tools/check_zrpf_initial_paid_calibration_attempt_v1.py" in argv:
            raw = _run_paid_calibration_checker(command)
            return worker.ProcessResult(
                raw.replace(b'"qualified":true', b'"qualified":false'), b"", 0, 1
            )
        if "tools/check_zrpf_stage_execution_profile_v1.py" in argv:
            return worker.ProcessResult(b"", b"", 0, 1)
        proof_started = True
        return worker.ProcessResult(b"unreachable", b"", 0, 1)

    monkeypatch.setattr(worker, "_run_bounded_command", rebound_paid_gate)
    with pytest.raises(worker.WorkerError, match="qualification output mismatch"):
        worker.execute_stage(
            plan,
            packet,
            repo,
            artifact_root,
            run_root,
            runtime_bindings=runtime,
            trusted_current_epoch_seconds=paid_fixture.CURRENT_EPOCH,
        )
    assert proof_started is False


def test_effective_command_policy_ratchets_worker_capture_and_rejects_v3(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    assert worker.CAPTURE_SCHEMA.endswith("/v4")
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    stale = copy.deepcopy(capture)
    stale["schema"] = "zenodex/zrpf_remote_reproof_worker_capture/v3"
    stale["capture_id"] = worker.derive_capture_id(stale)
    stage = worker.validate_stage_packet(plan, packet, repo, artifact_root)
    with pytest.raises(worker.WorkerError, match="schema"):
        worker.validate_capture_shape(stale, stage)
    assert (run_root / "outputs/proofs/v6_l1_receipt.json").is_file()


@pytest.mark.parametrize(
    "profile_id",
    (
        handoff.CPU_PROVER_COMPUTE_PROFILE_ID,
        handoff.CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID,
    ),
)
def test_execution_profile_checker_receives_the_authenticated_compute_profile_id(
    tmp_path: Path,
    profile_id: str,
) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(
        tmp_path,
        stage_id="v7_receipt",
        prover_compute_profile_id=profile_id,
    )
    stage = worker.validate_stage_packet(plan, packet, repo, artifact_root)

    assert (
        worker._resolve_argument(
            "@prover_compute_profile_id",
            stage,
            {},
            {},
            {},
        )
        == profile_id
    )


def test_cli_writes_one_content_addressed_capture(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, _chain, plan, artifact_root, packet_path, _packet = _stage_context(tmp_path)
    monkeypatch.setattr(worker, "_run_bounded_command", _fake_v6_l1_success)
    handoff_path = tmp_path / "handoff.json"
    handoff_path.write_bytes(handoff.canonical_json_bytes(plan))
    run_root = tmp_path / "run"
    capture_path = tmp_path / "capture.json"
    assert (
        worker.main(
            [
                "run-stage",
                "--repository",
                str(repo),
                "--handoff",
                str(handoff_path),
                "--packet",
                str(packet_path),
                "--artifact-root",
                str(artifact_root),
                "--run-root",
                str(run_root),
                "--capture-output",
                str(capture_path),
            ]
        )
        == 0
    )
    capture = handoff.load_canonical_json(capture_path, "worker capture")
    assert isinstance(capture, dict)
    assert capture["capture_id"] == worker.derive_capture_id(capture)


def test_command_and_resource_class_substitution_reject(tmp_path: Path) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(tmp_path)
    substituted = copy.deepcopy(plan)
    task = next(row for row in substituted["tasks"] if row["stage_id"] == "v6_l1_receipt")
    task["commands"][0]["runner"] = "/bin/true"
    task["resource_class"] = "light"
    task["task_id"] = handoff.derive_task_id(task)
    substituted["handoff_id"] = handoff.derive_handoff_id(substituted)
    with pytest.raises(handoff.HandoffError, match="governed source-derived plan"):
        worker.execute_stage(substituted, packet, repo, artifact_root, tmp_path / "run")


@pytest.mark.parametrize(
    ("profile_id", "expected_cuda_visible_devices"),
    (
        (handoff.CPU_PROVER_COMPUTE_PROFILE_ID, "-1"),
        (handoff.CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID, "0"),
    ),
)
def test_prover_compute_environment_is_exact_and_capture_bound(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    profile_id: str,
    expected_cuda_visible_devices: str | None,
) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(
        tmp_path,
        prover_compute_profile_id=profile_id,
    )
    run_root = tmp_path / "run"
    seen_environment: dict[str, str] = {}

    def capture_environment(
        command: worker.ResolvedCommand,
        policy: worker.ResourcePolicy,
        environment: dict[str, str],
        cwd: Path,
    ) -> worker.ProcessResult:
        seen_environment.update(environment)
        return _fake_v6_l1_success(command, policy, environment, cwd)

    monkeypatch.setattr(worker, "_run_bounded_command", capture_environment)
    capture = worker.execute_stage(plan, packet, repo, artifact_root, run_root)

    assert seen_environment["RISC0_PROVER"] == "ipc"
    assert seen_environment["RISC0_EXECUTOR"] == "ipc"
    assert seen_environment["RISC0_SERVER_PATH"] == str(
        run_root / "inputs/inputs/prover-risc0-home/bin/r0vm"
    )
    assert seen_environment.get("CUDA_VISIBLE_DEVICES") == expected_cuda_visible_devices
    assert "RISC0_DEFAULT_PROVER_NUM_GPUS" not in seen_environment
    captured_profile = cast(dict[str, object], capture["prover_compute_profile"])
    assert captured_profile["profile_id"] == profile_id
    worker.validate_worker_capture(
        plan,
        packet,
        capture,
        repo,
        artifact_root,
        run_root,
    )

    substituted = copy.deepcopy(capture)
    substituted_profile = dict(captured_profile)
    substituted["prover_compute_profile"] = substituted_profile
    substituted_profile["profile_id"] = (
        handoff.CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID
        if profile_id == handoff.CPU_PROVER_COMPUTE_PROFILE_ID
        else handoff.CPU_PROVER_COMPUTE_PROFILE_ID
    )
    substituted["capture_id"] = worker.derive_capture_id(substituted)
    with pytest.raises(worker.WorkerError, match="compute profile"):
        worker.validate_worker_capture(
            plan,
            packet,
            substituted,
            repo,
            artifact_root,
            run_root,
        )


@pytest.mark.parametrize(
    ("profile_id", "expected_cuda_visible_devices"),
    (
        (handoff.CPU_PROVER_COMPUTE_PROFILE_ID, "-1"),
        (handoff.CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID, "0"),
    ),
)
def test_ambient_cuda_device_selection_never_enters_worker_environment(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    profile_id: str,
    expected_cuda_visible_devices: str,
) -> None:
    monkeypatch.setenv("CUDA_VISIBLE_DEVICES", "7")
    monkeypatch.setenv("RISC0_PROVER", "bonsai")
    monkeypatch.setenv("RISC0_EXECUTOR", "local")
    monkeypatch.setenv("RISC0_SERVER_PATH", "/bin/true")
    monkeypatch.setenv("RISC0_DEFAULT_PROVER_NUM_GPUS", "8")
    monkeypatch.setenv("RISC0_DEV_MODE", "1")
    monkeypatch.setenv("BONSAI_API_URL", "https://example.invalid")
    monkeypatch.setenv("BONSAI_API_KEY", "must-not-cross-boundary")
    home = tmp_path / "home"
    home.mkdir()
    r0vm = tmp_path / "r0vm"
    r0vm.write_bytes(b"packet-bound-r0vm")

    environment = worker.clean_environment(
        home,
        None,
        worker.PROVER_COMPUTE_PROFILES[profile_id],
        r0vm,
    )

    assert environment["CUDA_VISIBLE_DEVICES"] == expected_cuda_visible_devices
    assert environment["RISC0_PROVER"] == "ipc"
    assert environment["RISC0_EXECUTOR"] == "ipc"
    assert environment["RISC0_SERVER_PATH"] == str(r0vm)
    for forbidden in (
        "RISC0_DEFAULT_PROVER_NUM_GPUS",
        "RISC0_DEV_MODE",
        "BONSAI_API_URL",
        "BONSAI_API_KEY",
    ):
        assert forbidden not in environment


def test_prover_profile_rejects_missing_packet_r0vm(tmp_path: Path) -> None:
    home = tmp_path / "home"
    home.mkdir()
    with pytest.raises(worker.WorkerError, match="r0vm"):
        worker.clean_environment(
            home,
            None,
            worker.PROVER_COMPUTE_PROFILES[handoff.CPU_PROVER_COMPUTE_PROFILE_ID],
            None,
        )


def test_packet_boolean_integer_aliasing_rejects(tmp_path: Path) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(tmp_path)
    packet["authority"]["production_authority"] = 0
    packet["ordinal"] = False
    packet["execution_packet_id"] = handoff.derive_execution_packet_id(packet)
    with pytest.raises(worker.WorkerError, match="exact current input artifacts"):
        worker.execute_stage(plan, packet, repo, artifact_root, tmp_path / "run")


def test_stale_run_root_rejects_before_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(tmp_path)
    run_root = tmp_path / "run"
    run_root.mkdir()
    called = False

    def forbidden(*_args: object, **_kwargs: object) -> worker.ProcessResult:
        nonlocal called
        called = True
        raise AssertionError("process runner must not be reached")

    monkeypatch.setattr(worker, "_run_bounded_command", forbidden)
    with pytest.raises(worker.WorkerError, match="begin absent"):
        worker.execute_stage(plan, packet, repo, artifact_root, run_root)
    assert called is False


@pytest.mark.parametrize("mode", ["missing", "surplus", "symlink"])
def test_output_inventory_rejects_missing_surplus_and_symlink(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mode: str
) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(tmp_path)
    run_root = tmp_path / "run"

    def malformed(
        command: worker.ResolvedCommand,
        _policy: worker.ResourcePolicy,
        _environment: dict[str, str],
        _cwd: Path,
    ) -> worker.ProcessResult:
        argv = list(command.argv)
        receipt_path = Path(argv[argv.index("--receipt-out") + 1])
        if mode == "surplus":
            receipt_path.write_bytes(b"receipt\n")
            (run_root / "outputs/proofs/surplus.bin").write_bytes(b"surplus\n")
        elif mode == "symlink":
            target = run_root / "target"
            target.write_bytes(b"receipt\n")
            receipt_path.symlink_to(target)
        return worker.ProcessResult(
            stdout=b'{"status":"candidate"}\n',
            stderr=b"",
            exit_code=0,
            duration_milliseconds=1,
        )

    monkeypatch.setattr(worker, "_run_bounded_command", malformed)
    expected = "missing" if mode == "missing" else mode
    with pytest.raises(worker.WorkerError, match=expected):
        worker.execute_stage(plan, packet, repo, artifact_root, run_root)


def test_output_path_escape_in_substituted_catalog_rejects(tmp_path: Path) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(tmp_path)
    substituted = copy.deepcopy(plan)
    contract = next(
        row for row in substituted["artifact_contracts"] if row["role"] == "v6_l1_receipt"
    )
    contract["path"] = "../escaped-receipt.json"
    contract["contract_id"] = handoff._derive_artifact_contract_id(contract)
    task = next(row for row in substituted["tasks"] if row["stage_id"] == "v6_l1_receipt")
    task["output_artifact_contract_ids"][0] = contract["contract_id"]
    task["task_id"] = handoff.derive_task_id(task)
    substituted["handoff_id"] = handoff.derive_handoff_id(substituted)
    with pytest.raises(handoff.HandoffError, match="governed source-derived plan"):
        worker.execute_stage(substituted, packet, repo, artifact_root, tmp_path / "run")


def test_timeout_and_capture_bounds_fail_closed(tmp_path: Path) -> None:
    home = tmp_path / "home"
    home.mkdir()
    base_policy = worker.RESOURCE_POLICIES["light"]
    timeout_policy = replace(base_policy, timeout_seconds=1)
    sleeping = worker.ResolvedCommand(
        argv=("/usr/bin/python3", "-c", "import time; time.sleep(60)"),
        stdin_path=None,
        stdout_artifact_role=None,
        stdout_maximum_bytes=64,
        command_template_sha256="0" * 64,
    )
    with pytest.raises(worker.WorkerError, match="timed out"):
        worker._run_bounded_command(
            sleeping,
            timeout_policy,
            worker.clean_environment(
                home,
                None,
                worker.PROVER_COMPUTE_PROFILES[handoff.NO_PROVER_COMPUTE_PROFILE_ID],
                None,
            ),
            tmp_path,
        )

    noisy_policy = replace(base_policy, maximum_stdout_bytes=16)
    noisy = worker.ResolvedCommand(
        argv=("/usr/bin/python3", "-c", "print('x' * 128)"),
        stdin_path=None,
        stdout_artifact_role=None,
        stdout_maximum_bytes=16,
        command_template_sha256="1" * 64,
    )
    with pytest.raises(worker.WorkerError, match="stdout exceeds"):
        worker._run_bounded_command(
            noisy,
            noisy_policy,
            worker.clean_environment(
                home,
                None,
                worker.PROVER_COMPUTE_PROFILES[handoff.NO_PROVER_COMPUTE_PROFILE_ID],
                None,
            ),
            tmp_path,
        )


def test_preexec_delay_rejects_after_total_elapsed_deadline(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    home = tmp_path / "home"
    home.mkdir()
    policy = replace(worker.RESOURCE_POLICIES["light"], timeout_seconds=1)
    command = worker.ResolvedCommand(
        argv=("/usr/bin/true",),
        stdin_path=None,
        stdout_artifact_role=None,
        stdout_maximum_bytes=64,
        command_template_sha256="9" * 64,
    )

    monkeypatch.setattr(worker, "_install_child_limits", lambda _policy: time.sleep(1.1))

    with pytest.raises(worker.WorkerError, match="total elapsed-time bound"):
        worker._run_bounded_command(
            command,
            policy,
            worker.clean_environment(
                home,
                None,
                worker.PROVER_COMPUTE_PROFILES[handoff.NO_PROVER_COMPUTE_PROFILE_ID],
                None,
            ),
            tmp_path,
        )


def test_timeout_kills_descendant_that_retains_process_group_pipes(tmp_path: Path) -> None:
    home = tmp_path / "home"
    home.mkdir()
    process_record = tmp_path / "process-record.txt"
    script = "\n".join(
        (
            "import os",
            "from pathlib import Path",
            "import subprocess",
            "import sys",
            f"record = Path({str(process_record)!r})",
            "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])",
            "record.write_text(f'{os.getpgrp()} {child.pid}', encoding='ascii')",
        )
    )
    command = worker.ResolvedCommand(
        argv=("/usr/bin/python3", "-c", script),
        stdin_path=None,
        stdout_artifact_role=None,
        stdout_maximum_bytes=64,
        command_template_sha256="3" * 64,
    )
    policy = replace(worker.RESOURCE_POLICIES["light"], timeout_seconds=1)
    with pytest.raises(worker.WorkerError, match="timed out"):
        worker._run_bounded_command(
            command,
            policy,
            worker.clean_environment(
                home,
                None,
                worker.PROVER_COMPUTE_PROFILES[handoff.NO_PROVER_COMPUTE_PROFILE_ID],
                None,
            ),
            tmp_path,
        )

    process_group, child_pid = (int(value) for value in process_record.read_text().split())
    deadline = time.monotonic() + 5
    while _process_or_group_is_live(child_pid, process_group) and time.monotonic() < deadline:
        time.sleep(0.01)
    assert _process_or_group_is_live(child_pid, process_group) is False


def _process_or_group_is_live(process_id: int, process_group: int) -> bool:
    process_live = True
    group_live = True
    try:
        os.kill(process_id, 0)
    except ProcessLookupError:
        process_live = False
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        group_live = False
    return process_live or group_live


def test_nonzero_exit_rejects(tmp_path: Path) -> None:
    home = tmp_path / "home"
    home.mkdir()
    command = worker.ResolvedCommand(
        argv=("/usr/bin/python3", "-c", "raise SystemExit(7)"),
        stdin_path=None,
        stdout_artifact_role=None,
        stdout_maximum_bytes=64,
        command_template_sha256="2" * 64,
    )
    with pytest.raises(worker.WorkerError, match="exit status 7"):
        worker._run_bounded_command(
            command,
            worker.RESOURCE_POLICIES["light"],
            worker.clean_environment(
                home,
                None,
                worker.PROVER_COMPUTE_PROFILES[handoff.NO_PROVER_COMPUTE_PROFILE_ID],
                None,
            ),
            tmp_path,
        )


def test_capture_digest_and_output_record_substitution_reject(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)

    wrong_id = copy.deepcopy(capture)
    wrong_id["capture_id"] = "0" * 64
    with pytest.raises(worker.WorkerError, match="capture ID"):
        worker.validate_worker_capture(
            plan, cast(dict[str, Any], packet), wrong_id, repo, artifact_root, run_root
        )

    substituted = copy.deepcopy(capture)
    substituted["outputs"][0]["sha256"] = "1" * 64
    substituted["capture_id"] = worker.derive_capture_id(substituted)
    with pytest.raises(worker.WorkerError, match="output artifact inventory"):
        worker.validate_worker_capture(
            plan, cast(dict[str, Any], packet), substituted, repo, artifact_root, run_root
        )


def _position_distinct_payload(role: str, ordinal: int) -> bytes:
    size = 603 + 4 * ordinal
    seed = hashlib.sha256(f"{ordinal}:{role}:active-witness".encode("ascii")).digest()
    body = (seed * ((size // len(seed)) + 1))[:size]
    payload = bytes((ordinal + 1,)) + body[1:-1] + bytes((0xE0 - ordinal,))
    assert len(payload) == size
    assert payload != payload[::-1]
    return payload


def test_worker_build_stage_resolves_exact_g_runtime_and_output_positions(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo, chain, plan, artifact_root, _packet_path, packet = _stage_context(
        tmp_path, "worker_prover_build"
    )
    assert chain[0] != chain[3]
    runtime = {
        "risc0_home": tmp_path / "runtime/risc0-home",
        "cargo_registry_dir": tmp_path / "runtime/cargo-registry",
        "docker": tmp_path / "runtime/docker",
    }
    runtime["risc0_home"].mkdir(parents=True)
    runtime["cargo_registry_dir"].mkdir(parents=True)
    runtime["docker"].write_bytes(b"docker-client-active-witness")
    runtime["docker"].chmod(0o500)
    output_bindings = (
        ("--v2-adapter-prover-out", "v2_adapter_prover", "worker/bin/prove_v2_leaf_adapter"),
        ("--v6-leaf-prover-out", "v6_leaf_prover", "worker/bin/prove_spot_value_leaf_v6"),
        (
            "--v6-l1-prover-out",
            "v6_l1_prover",
            "worker/bin/prove_spot_value_aggregate_l1_v6",
        ),
        (
            "--v6-l2-prover-out",
            "v6_l2_prover",
            "worker/bin/prove_spot_value_aggregate_l2_v6",
        ),
        (
            "--v6-settlement-prover-out",
            "v6_settlement_prover",
            "worker/bin/prove_source_opened_spot_settlement_v6",
        ),
        (
            "--v6-host-verifier-out",
            "v6_host_verifier",
            "worker/bin/source-opened-spot-settlement-verifier-v6",
        ),
        (
            "--mutation-verifier-out",
            "mutation_verifier",
            "worker/bin/verify-spot-v7-remote-mutations",
        ),
        ("--v7-program-out", "v7_program", "worker/programs/spot_settlement_v7.bin"),
        ("--v7-prover-out", "v7_prover", "worker/bin/prove_spot_settlement_v7"),
        ("--worker-build-report-out", "worker_build_report", "worker/build-report.json"),
    )
    run_root = tmp_path / "worker-build-run"
    seen: list[tuple[str, ...]] = []

    def fake_worker_build(
        command: worker.ResolvedCommand,
        _policy: worker.ResourcePolicy,
        _environment: dict[str, str],
        _cwd: Path,
    ) -> worker.ProcessResult:
        seen.append(command.argv)
        argv = list(command.argv)
        assert argv[argv.index("--source-commit") + 1] == chain[3]
        assert argv[argv.index("--post-pin-governance") + 1] == str(
            run_root / "inputs/ancestry/post_pin_governance.json"
        )
        assert argv[argv.index("--packet-r0vm") + 1] == str(
            run_root / "inputs/inputs/risc0-home/bin/r0vm"
        )
        assert argv[argv.index("--risc0-home") + 1] == str(runtime["risc0_home"])
        assert argv[argv.index("--cargo-registry-dir") + 1] == str(runtime["cargo_registry_dir"])
        assert argv[argv.index("--docker") + 1] == str(runtime["docker"])
        for ordinal, (flag, role, relative) in enumerate(output_bindings):
            expected = run_root / "outputs" / relative
            assert argv[argv.index(flag) + 1] == str(expected)
            expected.write_bytes(_position_distinct_payload(role, ordinal))
        return worker.ProcessResult(b"", b"", 0, 11)

    monkeypatch.setattr(worker, "_run_bounded_command", fake_worker_build)
    capture = worker.execute_stage(
        plan,
        packet,
        repo,
        artifact_root,
        run_root,
        runtime_bindings=runtime,
    )

    assert len(seen) == 1
    records = {row["role"]: row for row in cast(list[dict[str, Any]], capture["outputs"])}
    for ordinal, (_flag, role, relative) in enumerate(output_bindings):
        payload = _position_distinct_payload(role, ordinal)
        assert records[role]["size_bytes"] == len(payload)
        assert records[role]["sha256"] == hashlib.sha256(payload).hexdigest()
        assert (run_root / "outputs" / relative).read_bytes() == payload
    worker.validate_worker_capture(
        plan,
        packet,
        capture,
        repo,
        artifact_root,
        run_root,
        runtime_bindings=runtime,
    )


def test_identity_stage_requires_exact_runtime_bindings_and_captures_all_outputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo, chain, plan, artifact_root, _packet_path, packet = _stage_context(
        tmp_path, "identity_rebuild"
    )
    assert chain[0] != chain[3]
    runtime = {
        "risc0_home": tmp_path / "runtime/risc0-home",
        "cargo_registry_dir": tmp_path / "runtime/cargo-registry",
        "docker": tmp_path / "runtime/docker",
    }
    runtime["risc0_home"].mkdir(parents=True)
    runtime["cargo_registry_dir"].mkdir(parents=True)
    runtime["docker"].write_bytes(b"docker")
    runtime["docker"].chmod(0o500)

    with pytest.raises(worker.WorkerError, match="runtime binding inventory"):
        worker.execute_stage(plan, packet, repo, artifact_root, tmp_path / "missing-runtime")

    output_bindings = (
        ("--identity-plan-out", "identity_plan", "identity/plan.json"),
        (
            "--identity-observations-out",
            "identity_observations",
            "identity/run/rebuild-observations.json",
        ),
        (
            "--identity-candidate-report-out",
            "identity_candidate_report",
            "identity/run/rebuild-candidate-report.json",
        ),
        (
            "--source-program-out",
            "source_program",
            "identity/run/outputs/01-source-spot/source_spot.bin",
        ),
        (
            "--source-cli-out",
            "source_cli",
            "identity/run/outputs/01-source-spot/tau-state-proof-risc0-cli",
        ),
        (
            "--v2-adapter-program-out",
            "v2_adapter_program",
            "identity/run/outputs/02-v2-adapter/v2_adapter.bin",
        ),
        (
            "--v6-leaf-program-out",
            "v6_leaf_program",
            "identity/run/outputs/03-v6-leaf/spot_value_leaf_v6.bin",
        ),
        (
            "--v6-l1-program-out",
            "v6_l1_program",
            "identity/run/outputs/04-v6-l1/spot_value_aggregate_l1_v6.bin",
        ),
        (
            "--v6-l2-program-out",
            "v6_l2_program",
            "identity/run/outputs/05-v6-l2/spot_value_aggregate_l2_v6.bin",
        ),
        (
            "--v6-settlement-program-out",
            "v6_settlement_program",
            "identity/run/outputs/06-v6-settlement/source_opened_spot_settlement_v6.bin",
        ),
    )
    seen: list[tuple[str, ...]] = []
    run_root = tmp_path / "run"

    def fake_identity(
        command: worker.ResolvedCommand,
        _policy: worker.ResourcePolicy,
        _environment: dict[str, str],
        _cwd: Path,
    ) -> worker.ProcessResult:
        seen.append(command.argv)
        argv = list(command.argv)
        assert argv[argv.index("--source-commit") + 1] == chain[0]
        for ordinal, (flag, role, relative) in enumerate(output_bindings):
            path = Path(argv[argv.index(flag) + 1])
            assert path == run_root / "outputs" / relative
            path.write_bytes(_position_distinct_payload(role, ordinal))
        return worker.ProcessResult(b"", b"", 0, 7)

    monkeypatch.setattr(worker, "_run_bounded_command", fake_identity)
    capture = worker.execute_stage(
        plan,
        packet,
        repo,
        artifact_root,
        run_root,
        runtime_bindings=runtime,
    )

    assert len(seen) == 1
    assert [row["role"] for row in cast(list[dict[str, object]], capture["outputs"])] == [
        "identity_plan",
        "identity_observations",
        "identity_candidate_report",
        "source_program",
        "source_cli",
        "v2_adapter_program",
        "v6_leaf_program",
        "v6_l1_program",
        "v6_l2_program",
        "v6_settlement_program",
    ]
    records = {row["role"]: row for row in cast(list[dict[str, Any]], capture["outputs"])}
    for ordinal, (_flag, role, _relative) in enumerate(output_bindings):
        payload = _position_distinct_payload(role, ordinal)
        assert records[role]["size_bytes"] == len(payload)
        assert records[role]["sha256"] == hashlib.sha256(payload).hexdigest()
    worker.validate_worker_capture(
        plan,
        packet,
        capture,
        repo,
        artifact_root,
        run_root,
        runtime_bindings=runtime,
    )

    substituted = dict(runtime)
    substituted["surplus"] = tmp_path / "runtime/surplus"
    with pytest.raises(worker.WorkerError, match="runtime binding inventory"):
        worker.validate_worker_capture(
            plan,
            packet,
            capture,
            repo,
            artifact_root,
            run_root,
            runtime_bindings=substituted,
        )

    for role, original in runtime.items():
        alternate = tmp_path / "alternate" / role
        if original.is_dir():
            alternate.mkdir(parents=True)
        else:
            alternate.parent.mkdir(parents=True, exist_ok=True)
            alternate.write_bytes(original.read_bytes())
            alternate.chmod(0o500)
        rebound = dict(runtime)
        rebound[role] = alternate
        with pytest.raises(worker.WorkerError, match="resolved argv digest mismatch"):
            worker.validate_worker_capture(
                plan,
                packet,
                capture,
                repo,
                artifact_root,
                run_root,
                runtime_bindings=rebound,
            )


def test_mutation_stage_uses_exact_artifact_runner_and_complete_output_inventory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, _chain, plan, artifact_root, _packet_path, packet = _stage_context(
        tmp_path, "mutation_verification"
    )
    seen: list[tuple[str, ...]] = []

    def exact_mutation_success(
        command: worker.ResolvedCommand,
        _policy: worker.ResourcePolicy,
        _environment: dict[str, str],
        _cwd: Path,
    ) -> worker.ProcessResult:
        seen.append(command.argv)
        argv = list(command.argv)
        for flag in (
            "--leaf-mutation-out",
            "--level-one-mutation-out",
            "--level-two-mutation-out",
        ):
            Path(argv[argv.index(flag) + 1]).write_bytes(flag.encode("ascii") + b"\n")
        return worker.ProcessResult(
            stdout=b'{"schema":"zenodex/zrpf_remote_mutation_verification/v1"}\n',
            stderr=b"",
            exit_code=0,
            duration_milliseconds=3,
        )

    monkeypatch.setattr(worker, "_run_bounded_command", exact_mutation_success)
    run_root = tmp_path / "run"
    capture = worker.execute_stage(plan, packet, repo, artifact_root, run_root)
    assert len(seen) == 1
    assert seen[0][0].endswith("worker/bin/verify-spot-v7-remote-mutations")
    outputs = cast(list[dict[str, object]], capture["outputs"])
    assert [row["role"] for row in outputs] == [
        "v6_leaf_seal_mutation",
        "v6_l1_seal_mutation",
        "v6_l2_seal_mutation",
        "mutation_report",
    ]


def test_worker_capture_authority_requires_exact_false_values(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/07-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    capture["authority"]["proof_authority"] = 0
    capture["capture_id"] = worker.derive_capture_id(capture)
    with pytest.raises(worker.WorkerError, match="exact Boolean false"):
        worker.validate_worker_capture(
            plan, cast(dict[str, Any], packet), capture, repo, artifact_root, run_root
        )
