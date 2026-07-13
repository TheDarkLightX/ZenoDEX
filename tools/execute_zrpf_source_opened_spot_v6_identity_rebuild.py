#!/usr/bin/env python3
"""Execute the governed, authority-neutral Spot V6 identity rebuild plan.

The functional core consumes only the deterministic planner output.  Source
capture and process execution sit behind narrow adapters.  Successful output
remains candidate evidence: this tool generates no proof, verifies no receipt,
and grants no release, settlement, or production authority.
"""

from __future__ import annotations

import argparse
import os
import shutil
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Sequence

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner  # noqa: E402
from tools import zrpf_v6_identity_artifacts as artifacts  # noqa: E402
from tools.zrpf_v6_identity_docker_runner import DockerBuildRunner  # noqa: E402
from tools.zrpf_v6_identity_executor_types import (  # noqa: E402
    BuildKind,
    BuildRequest,
    BuildResult,
    BuildRunner,
    ExecutionError,
)
from tools.zrpf_v6_identity_source_snapshot import (  # noqa: E402
    SOURCE_SNAPSHOT_DIRECTORY,
    V2_CANDIDATE_PATHS,
    GitSnapshotter,
    MaterializedSnapshot,
    create_private_directory,
    protected_historical_hashes,
    require_historical_unchanged,
    require_snapshot_unchanged,
    resolve_snapshot_path,
    snapshot_root,
    validate_initial_snapshot,
)

__all__ = [
    "BuildKind",
    "BuildRequest",
    "BuildResult",
    "ExecutionError",
    "execute_plan",
    "repin_rust_constant",
    "resolve_snapshot_path",
]

repin_rust_constant = artifacts.repin_rust_constant

OBSERVATIONS_FILE = "rebuild-observations.json"
CANDIDATE_REPORT_FILE = "rebuild-candidate-report.json"


def execute_plan(
    plan: dict[str, Any],
    *,
    runner: BuildRunner,
    snapshotter: GitSnapshotter | None = None,
    repo_root: Path = planner.REPO_ROOT,
) -> dict[str, Any]:
    """Execute one deterministic plan and return checker-accepted observations."""

    planner._validate_plan(plan)
    run_root = _prepare_run_root(Path(plan["host_run_root"]), repo_root)
    try:
        materialized = (snapshotter or GitSnapshotter()).materialize(
            repo_root,
            plan["source_commit"],
            run_root / SOURCE_SNAPSHOT_DIRECTORY,
        )
        validate_initial_snapshot(materialized, plan)
        protected = protected_historical_hashes(materialized.root)
        stages, programs = _execute_primary_stages(
            plan,
            materialized,
            runner,
            run_root,
        )
        observations = _finish_observations(
            plan,
            materialized,
            runner,
            run_root,
            stages,
            programs,
        )
        require_historical_unchanged(materialized.root, protected)
        report = planner.check_observations(plan, observations)
        _write_new(run_root / OBSERVATIONS_FILE, planner.canonical_bytes(observations))
        _write_new(run_root / CANDIDATE_REPORT_FILE, planner.canonical_bytes(report))
        return observations
    except BaseException:
        shutil.rmtree(run_root, ignore_errors=True)
        raise


def _finish_observations(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
    stages: list[dict[str, Any]],
    programs: list[dict[str, Any]],
) -> dict[str, Any]:
    two_pass = _execute_settlement_second_pass(
        plan,
        snapshot,
        runner,
        run_root,
        programs[-1],
    )
    final_rebuild = _execute_final_rebuild(plan, snapshot, runner, run_root)
    host_verifier = _execute_host_verifier(
        plan,
        snapshot,
        runner,
        run_root,
        programs[-1],
    )
    return {
        "schema": planner.OBSERVATION_SCHEMA,
        "plan_sha256": planner.canonical_sha256(plan),
        "source_commit": plan["source_commit"],
        "toolchain": dict(planner.TOOLCHAIN),
        "stages": stages,
        "settlement_self_image_two_pass": two_pass,
        "final_clean_rebuild": final_rebuild,
        "host_verifier": host_verifier,
    }


def _execute_primary_stages(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    stages: list[dict[str, Any]] = []
    programs: list[dict[str, Any]] = []
    anchor: dict[str, Any] | None = None
    for spec, stage_plan in zip(planner.STAGES, plan["stages"], strict=True):
        row = _run_primary_guest_stage(
            plan,
            snapshot,
            runner,
            run_root,
            spec,
            stage_plan,
            programs,
        )
        stages.append(row)
        programs.append(row["program"])
        artifacts.apply_stage_repins(snapshot.root, spec, row)
        if spec.stage_id == "source_spot":
            anchor = planner.build_current_source_anchor_candidate(plan, row)
            artifacts.write_candidate_document(
                snapshot.root,
                V2_CANDIDATE_PATHS[0],
                anchor,
            )
        elif spec.stage_id == "v2_adapter":
            if anchor is None:
                raise ExecutionError("source anchor candidate is unavailable")
            policy = planner.build_v2_adapter_source_policy_candidate(
                plan,
                stages[0],
                row,
                anchor,
            )
            artifacts.write_candidate_document(
                snapshot.root,
                V2_CANDIDATE_PATHS[1],
                policy,
            )
    return stages, programs


def _run_primary_guest_stage(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
    spec: planner.StageSpec,
    stage_plan: dict[str, Any],
    preceding_programs: list[dict[str, Any]],
) -> dict[str, Any]:
    pass_id = f"primary:{spec.stage_id}"
    program, companion, source_root = _run_guest_build(
        plan,
        snapshot,
        runner,
        run_root,
        spec,
        stage_plan,
        pass_id,
        f"{spec.ordinal:02d}-{spec.stage_id.replace('_', '-')}",
    )
    source_tree_root = (
        plan["source_guest_source_coverage"]["inventory_root_sha256"]
        if spec.stage_id == "source_spot"
        else None
    )
    child_pin = _child_pin(spec, preceding_programs)
    repins = [
        {
            "path": repin.path,
            "symbol": repin.symbol,
            "value_kind": repin.value_kind,
            "visibility": repin.visibility,
            "value": planner._repin_value(repin.value_kind, program, source_tree_root),
        }
        for repin in spec.repins
    ]
    return {
        "stage_id": spec.stage_id,
        "ordinal": spec.ordinal,
        "source_snapshot_root_sha256": source_root,
        "source_tree_root_sha256": source_tree_root,
        "canonical_source_root": planner.CANONICAL_SOURCE_ROOT,
        "target_was_absent": True,
        "output_was_absent": True,
        "network_disabled": True,
        "cargo_locked": True,
        "cargo_offline": True,
        "build_jobs": planner.BUILD_JOBS,
        "build_cpus": planner.BUILD_CPUS,
        "build_memory_bytes": planner.BUILD_MEMORY_BYTES,
        "program": program,
        "companion_host_binary": companion,
        "child_pin": child_pin,
        "repins": repins,
    }


def _run_guest_build(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
    spec: planner.StageSpec,
    stage_plan: dict[str, Any],
    pass_id: str,
    directory_name: str,
) -> tuple[dict[str, Any], dict[str, Any] | None, str]:
    before = snapshot_root(snapshot)
    target = run_root / "targets" / directory_name
    output = run_root / "outputs" / directory_name
    request = _guest_request(
        plan,
        snapshot.root,
        target,
        output,
        spec,
        stage_plan,
        pass_id,
    )
    result = runner.run(request)
    try:
        program, companion = artifacts.collect_guest_outputs(request, result)
        require_snapshot_unchanged(snapshot, before, pass_id)
    finally:
        _remove_target(target)
    return program, companion, before


def _child_pin(
    spec: planner.StageSpec,
    preceding_programs: list[dict[str, Any]],
) -> dict[str, Any] | None:
    if not preceding_programs:
        return None
    predecessor = planner.STAGES[spec.ordinal - 2]
    return {
        "stage_id": predecessor.stage_id,
        "image_id": preceding_programs[-1]["image_id"],
        "program_binary_sha256": preceding_programs[-1]["program_binary_sha256"],
    }


def _execute_settlement_second_pass(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
    primary_settlement: dict[str, Any],
) -> dict[str, Any]:
    spec = planner.STAGES[-1]
    program, _companion, source_root = _run_guest_build(
        plan,
        snapshot,
        runner,
        run_root,
        spec,
        plan["stages"][-1],
        "settlement-second-pass",
        "settlement-second-pass",
    )
    repin = spec.repins[0]
    return {
        "host_only_policy_path": repin.path,
        "host_only_policy_symbol": repin.symbol,
        "settlement_guest_depends_on_host_only_policy": program != primary_settlement,
        "second_pass_source_snapshot_root_sha256": source_root,
        "second_pass_program": program,
    }


def _execute_final_rebuild(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
) -> dict[str, Any]:
    root = snapshot_root(snapshot)
    programs: list[dict[str, Any]] = []
    for spec, stage_plan in zip(planner.STAGES, plan["stages"], strict=True):
        program, _companion, observed_root = _run_guest_build(
            plan,
            snapshot,
            runner,
            run_root,
            spec,
            stage_plan,
            f"final:{spec.stage_id}",
            f"final-{spec.ordinal:02d}-{spec.stage_id}",
        )
        if observed_root != root:
            raise ExecutionError("final rebuild source root changed between stages")
        programs.append(program)
    return {
        "final_source_snapshot_root_sha256": root,
        "canonical_source_root": planner.CANONICAL_SOURCE_ROOT,
        "network_disabled": True,
        "cargo_locked": True,
        "cargo_offline": True,
        "fresh_target_per_stage": True,
        "fresh_output_per_stage": True,
        "programs": programs,
    }


def _execute_host_verifier(
    plan: dict[str, Any],
    snapshot: MaterializedSnapshot,
    runner: BuildRunner,
    run_root: Path,
    settlement: dict[str, Any],
) -> dict[str, Any]:
    before = snapshot_root(snapshot)
    target = run_root / "targets" / "host-verifier"
    output = run_root / "outputs" / "host-verifier"
    host_plan = plan["host_verifier"]
    request = BuildRequest(
        kind=BuildKind.HOST_VERIFIER,
        pass_id="host-verifier",
        stage_id="host_verifier",
        source_commit=plan["source_commit"],
        source_snapshot=snapshot.root,
        target_directory=target,
        output_directory=output,
        container_target_directory="/build/host-verifier/target",
        container_output_directory="/build/host-verifier/output",
        artifact_file=host_plan["binary"],
        command=tuple(host_plan["command"]),
        extraction_source=f"/build/host-verifier/target/release/{host_plan['binary']}",
    )
    result = runner.run(request)
    try:
        binary = artifacts.collect_host_output(request, result)
        require_snapshot_unchanged(snapshot, before, "host-verifier")
    finally:
        _remove_target(target)
    return {
        "source_snapshot_root_sha256": before,
        "expected_settlement_image_id": settlement["image_id"],
        "binary_file": binary["binary_file"],
        "binary_bytes": binary["binary_bytes"],
        "binary_sha256": binary["binary_sha256"],
        "canonical_source_root": planner.CANONICAL_SOURCE_ROOT,
        "target_was_absent": True,
        "cargo_locked": True,
        "cargo_offline": True,
        "network_disabled": True,
    }


def _guest_request(
    plan: dict[str, Any],
    snapshot: Path,
    target: Path,
    output: Path,
    spec: planner.StageSpec,
    stage_plan: dict[str, Any],
    pass_id: str,
) -> BuildRequest:
    companion = stage_plan["companion_host_binary"]
    return BuildRequest(
        kind=BuildKind.GUEST,
        pass_id=pass_id,
        stage_id=spec.stage_id,
        source_commit=plan["source_commit"],
        source_snapshot=snapshot,
        target_directory=target,
        output_directory=output,
        container_target_directory=str(
            PurePosixPath(stage_plan["extraction"]["source"]).parents[5]
        ),
        container_output_directory=str(
            PurePosixPath(stage_plan["extraction"]["destination"]).parent
        ),
        artifact_file=spec.artifact_file,
        command=tuple(stage_plan["command"]),
        extraction_source=stage_plan["extraction"]["source"],
        companion_artifact_file=(
            PurePosixPath(companion["destination"]).name if companion else None
        ),
        companion_extraction_source=companion["source"] if companion else None,
    )


def _prepare_run_root(path: Path, repo_root: Path) -> Path:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise ExecutionError("run root must be an absent absolute path")
    try:
        parent = path.parent.resolve(strict=True)
        repository = repo_root.resolve(strict=True)
    except OSError as exc:
        raise ExecutionError("run root parent is unavailable") from exc
    candidate = parent / path.name
    if candidate != path or candidate == repository or repository in candidate.parents:
        raise ExecutionError("run root must be canonical and external")
    create_private_directory(candidate)
    (candidate / "targets").mkdir(mode=0o700)
    (candidate / "outputs").mkdir(mode=0o700)
    return candidate


def _remove_target(path: Path) -> None:
    try:
        shutil.rmtree(path)
    except OSError as exc:
        raise ExecutionError("fresh target cleanup failed") from exc


def _write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--risc0-home", type=Path, required=True)
    parser.add_argument("--cargo-registry-dir", type=Path, required=True)
    parser.add_argument("--docker", type=Path, default=Path("/usr/bin/docker"))
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        plan = planner.load_canonical_json(args.plan, "rebuild plan")
        runner = DockerBuildRunner(
            risc0_home=args.risc0_home,
            cargo_registry_directory=args.cargo_registry_dir,
            docker=args.docker,
        )
        execute_plan(plan, runner=runner)
        run_root = Path(plan["host_run_root"])
        result = {
            "candidate_report": (run_root / CANDIDATE_REPORT_FILE).as_posix(),
            "observations": (run_root / OBSERVATIONS_FILE).as_posix(),
            "status": "candidate_identity_rebuild_completed_without_authority",
        }
        sys.stdout.buffer.write(planner.canonical_bytes(result))
    except (ExecutionError, OSError, planner.RebuildPlanError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
