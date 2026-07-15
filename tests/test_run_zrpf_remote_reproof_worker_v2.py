from __future__ import annotations

import copy
import hashlib
import os
import subprocess
import time
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

from tests import test_plan_zrpf_remote_reproof_handoff_v2 as handoff_fixture
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools import run_zrpf_remote_reproof_worker_v2 as worker


def _stage_context(
    tmp_path: Path, stage_id: str = "v6_l1_receipt"
) -> tuple[Path, list[str], dict[str, Any], Path, Path, dict[str, Any]]:
    repo, chain = handoff_fixture._ancestry_repo(tmp_path)
    subprocess.run(["git", "-C", str(repo), "reset", "--hard", "-q", chain[3]], check=True)
    plan = handoff_fixture._plan_for_chain(repo, chain)
    artifact_root = tmp_path / "artifacts"
    handoff_fixture._write_complete_artifacts(plan, artifact_root, repo)
    packet_directory = tmp_path / "packets"
    handoff_fixture._write_execution_packets(plan, artifact_root, repo, chain, packet_directory)
    task = next(row for row in plan["tasks"] if row["stage_id"] == stage_id)
    packet_path = packet_directory / f"{task['ordinal']:02d}-{stage_id}.json"
    packet = handoff.load_canonical_json(packet_path, "execution packet")
    assert isinstance(packet, dict)
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


def test_worker_executes_exact_packet_into_clean_output_stage(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet_path = tmp_path / "packets/06-v6_l1_receipt.json"
    packet = handoff.load_canonical_json(packet_path, "execution packet")
    assert isinstance(packet, dict)
    assert capture["capture_id"] == worker.derive_capture_id(capture)
    assert capture["authority"] == worker.false_authority()
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
            worker.clean_environment(home, None),
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
            worker.clean_environment(home, None),
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
            worker.clean_environment(home, None),
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
            worker.clean_environment(home, None),
            tmp_path,
        )


def test_capture_digest_and_output_record_substitution_reject(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, plan, artifact_root, run_root, capture = _capture_v6_l1(tmp_path, monkeypatch)
    packet = handoff.load_canonical_json(
        tmp_path / "packets/06-v6_l1_receipt.json", "execution packet"
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
        tmp_path / "packets/06-v6_l1_receipt.json", "execution packet"
    )
    assert isinstance(packet, dict)
    capture["authority"]["proof_authority"] = 0
    capture["capture_id"] = worker.derive_capture_id(capture)
    with pytest.raises(worker.WorkerError, match="exact Boolean false"):
        worker.validate_worker_capture(
            plan, cast(dict[str, Any], packet), capture, repo, artifact_root, run_root
        )
