from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

import pytest

from tests.test_execute_zrpf_source_opened_spot_v6_identity_rebuild import FakeRunner
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import run_zrpf_remote_identity_rebuild_stage_v2 as stage

SOURCE_COMMIT = subprocess.check_output(
    ["git", "-C", str(planner.REPO_ROOT), "rev-parse", "HEAD"],
    text=True,
).strip()


def _outputs(tmp_path: Path) -> dict[str, Path]:
    return {role: tmp_path / "outputs" / f"{role}.bin" for role in stage.OUTPUT_ROLES}


def test_identity_stage_materializes_exact_checked_outputs_and_removes_work_root(
    tmp_path: Path,
) -> None:
    outputs = _outputs(tmp_path)
    identity_run_root = tmp_path / "identity-run"

    stage.execute_identity_stage(
        source_commit=SOURCE_COMMIT,
        identity_run_root=identity_run_root,
        output_paths=outputs,
        runner=FakeRunner(),
        repo_root=planner.REPO_ROOT,
    )

    assert not identity_run_root.exists()
    plan = planner.load_canonical_json(outputs["identity_plan"], "identity plan")
    observations = planner.load_canonical_json(
        outputs["identity_observations"], "identity observations"
    )
    report = planner.load_canonical_json(outputs["identity_candidate_report"], "identity report")
    assert plan == planner.build_plan(SOURCE_COMMIT, identity_run_root.as_posix())
    assert report == planner.check_observations(plan, observations)
    assert all(value is False for value in report["authority"].values())

    for observed, role in zip(
        observations["stages"],
        stage.PROGRAM_OUTPUT_ROLES,
        strict=True,
    ):
        raw = outputs[role].read_bytes()
        assert hashlib.sha256(raw).hexdigest() == observed["program"]["program_binary_sha256"]
        assert len(raw) == observed["program"]["program_binary_bytes"]
    source_cli = outputs["source_cli"].read_bytes()
    companion = observations["stages"][0]["companion_host_binary"]
    assert hashlib.sha256(source_cli).hexdigest() == companion["binary_sha256"]
    assert len(source_cli) == companion["binary_bytes"]


def test_identity_stage_rejects_output_alias_existing_output_and_wrong_source(
    tmp_path: Path,
) -> None:
    outputs = _outputs(tmp_path)
    aliased = dict(outputs)
    aliased["source_cli"] = aliased["source_program"]
    with pytest.raises(stage.IdentityStageError, match="unique"):
        stage.execute_identity_stage(
            source_commit=SOURCE_COMMIT,
            identity_run_root=tmp_path / "alias-run",
            output_paths=aliased,
            runner=FakeRunner(),
            repo_root=planner.REPO_ROOT,
        )

    outputs["identity_plan"].parent.mkdir(parents=True, exist_ok=True)
    outputs["identity_plan"].write_bytes(b"stale")
    with pytest.raises(stage.IdentityStageError, match="begin absent"):
        stage.execute_identity_stage(
            source_commit=SOURCE_COMMIT,
            identity_run_root=tmp_path / "stale-run",
            output_paths=outputs,
            runner=FakeRunner(),
            repo_root=planner.REPO_ROOT,
        )

    fresh = _outputs(tmp_path / "fresh")
    with pytest.raises(stage.IdentityStageError, match="source commit"):
        stage.execute_identity_stage(
            source_commit="0" * 40,
            identity_run_root=tmp_path / "wrong-source-run",
            output_paths=fresh,
            runner=FakeRunner(),
            repo_root=planner.REPO_ROOT,
        )

    nested = _outputs(tmp_path / "nested")
    nested["identity_plan"] = tmp_path / "nested-run" / "identity-plan.json"
    with pytest.raises(stage.IdentityStageError, match="outside the disposable run root"):
        stage.execute_identity_stage(
            source_commit=SOURCE_COMMIT,
            identity_run_root=tmp_path / "nested-run",
            output_paths=nested,
            runner=FakeRunner(),
            repo_root=planner.REPO_ROOT,
        )


def test_cli_runtime_r0vm_must_equal_private_packet_snapshot(tmp_path: Path) -> None:
    runtime = tmp_path / "risc0-home"
    extension = runtime / "extensions" / stage.RISC0_EXTENSION_DIRECTORY
    extension.mkdir(parents=True)
    runtime_r0vm = extension / "r0vm"
    runtime_r0vm.write_bytes(b"runtime")
    packet_r0vm = tmp_path / "packet-r0vm"
    packet_r0vm.write_bytes(b"substituted")

    with pytest.raises(stage.IdentityStageError, match="r0vm differs"):
        stage.require_exact_runtime_r0vm(runtime, packet_r0vm)
