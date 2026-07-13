from __future__ import annotations

import json
import subprocess
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import test_plan_zrpf_source_opened_spot_v6_identity_rebuild as fixtures
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_identity_artifacts as artifacts
from tools import zrpf_v6_identity_materialization as materializer
from tools.zrpf_v6_identity_executor_types import ExecutionError
from tools.zrpf_v6_identity_source_snapshot import (
    SOURCE_SNAPSHOT_DIRECTORY,
    GitSnapshotter,
    snapshot_root,
)


@dataclass(frozen=True)
class _Candidate:
    repo: Path
    plan: Path
    observations: Path
    report: Path
    snapshot: Path
    manifest: Path


def _git(root: Path, *arguments: str) -> bytes:
    completed = subprocess.run(
        ["/usr/bin/git", "-C", str(root), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    assert completed.returncode == 0, completed.stderr.decode(errors="replace")
    return completed.stdout


def test_cli_help_works_without_pythonpath() -> None:
    completed = subprocess.run(
        [
            "/usr/bin/python3",
            "tools/materialize_zrpf_source_opened_spot_v6_identity.py",
            "--help",
        ],
        cwd=planner.REPO_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env={
            "HOME": "/nonexistent",
            "LC_ALL": "C",
            "PATH": "/usr/bin:/bin",
            "PYTHONDONTWRITEBYTECODE": "1",
            "TZ": "UTC",
        },
        check=False,
        timeout=30,
    )

    assert completed.returncode == 0
    assert b"{check,apply}" in completed.stdout
    assert not completed.stderr


def _replacement_commit(repo: Path) -> str:
    source = repo / "zk/zrpf_protocol/protocol/src/lib.rs"
    source.write_bytes(source.read_bytes() + b"\n// replacement-source attack\n")
    _git(repo, "add", source.relative_to(repo).as_posix())
    _git(
        repo,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "replacement source",
    )
    replacement = _git(repo, "rev-parse", "HEAD").decode().strip()
    _git(repo, "checkout", "--detach", fixtures.SOURCE_COMMIT)
    return replacement


def _clone_at_source_commit(destination: Path) -> None:
    completed = subprocess.run(
        [
            "/usr/bin/git",
            "clone",
            "--shared",
            "--no-checkout",
            "--quiet",
            str(planner.REPO_ROOT),
            str(destination),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    assert completed.returncode == 0, completed.stderr.decode(errors="replace")
    _git(destination, "sparse-checkout", "init", "--no-cone")
    _git(
        destination,
        "sparse-checkout",
        "set",
        "--no-cone",
        *planner.RELEVANT_WORKSPACE_ROOTS,
        *planner.PROTECTED_HISTORICAL_ARTIFACTS,
        *materializer.V2_CANDIDATE_PATHS,
    )
    _git(destination, "checkout", "--detach", fixtures.SOURCE_COMMIT)


def _apply_observed_transition(
    snapshot: Path,
    plan: dict,
    observations: dict,
) -> None:
    for spec, row in zip(planner.STAGES, observations["stages"], strict=True):
        artifacts.apply_stage_repins(snapshot, spec, row)
    anchor = planner.build_current_source_anchor_candidate(
        plan, observations["stages"][0]
    )
    policy = planner.build_v2_adapter_source_policy_candidate(
        plan,
        observations["stages"][0],
        observations["stages"][1],
        anchor,
    )
    artifacts.write_candidate_document(snapshot, materializer.V2_CANDIDATE_PATHS[0], anchor)
    artifacts.write_candidate_document(snapshot, materializer.V2_CANDIDATE_PATHS[1], policy)


def _write_json(path: Path, document: dict) -> None:
    path.write_bytes(planner.canonical_bytes(document))


def _candidate(tmp_path: Path) -> _Candidate:
    repo = tmp_path / "checkout"
    _clone_at_source_commit(repo)
    run_root = tmp_path / "run"
    plan = planner.build_plan(
        fixtures.SOURCE_COMMIT,
        run_root.as_posix(),
        repo_root=repo,
    )
    observations = fixtures._observations(plan)
    run_root.mkdir(mode=0o700)
    snapshot = GitSnapshotter().materialize(
        repo,
        fixtures.SOURCE_COMMIT,
        run_root / SOURCE_SNAPSHOT_DIRECTORY,
    )
    _apply_observed_transition(snapshot.root, plan, observations)
    final_root = snapshot_root(snapshot)
    observations["final_clean_rebuild"][
        "final_source_snapshot_root_sha256"
    ] = final_root
    observations["host_verifier"]["source_snapshot_root_sha256"] = final_root
    report = planner.check_observations(plan, observations, repo_root=repo)
    plan_path = tmp_path / "plan.json"
    observations_path = tmp_path / "observations.json"
    report_path = tmp_path / "report.json"
    _write_json(plan_path, plan)
    _write_json(observations_path, observations)
    _write_json(report_path, report)
    return _Candidate(
        repo=repo,
        plan=plan_path,
        observations=observations_path,
        report=report_path,
        snapshot=snapshot.root,
        manifest=tmp_path / "materialization-manifest.json",
    )


def _check(candidate: _Candidate) -> dict:
    return materializer.check_materialization(
        materializer.MaterializationRequest(
            repo_root=candidate.repo,
            plan_path=candidate.plan,
            observations_path=candidate.observations,
            report_path=candidate.report,
            run_snapshot_root=candidate.snapshot,
        )
    )


def test_check_then_apply_stages_only_the_eight_reconstructed_paths(
    tmp_path: Path,
) -> None:
    candidate = _candidate(tmp_path)

    checked = _check(candidate)
    applied = materializer.apply_materialization(
        materializer.MaterializationRequest(
            repo_root=candidate.repo,
            plan_path=candidate.plan,
            observations_path=candidate.observations,
            report_path=candidate.report,
            run_snapshot_root=candidate.snapshot,
        ),
        manifest_output=candidate.manifest,
    )

    assert checked["status"] == "checked_not_applied"
    assert checked["checkout_index_tree"] is None
    assert applied["status"] == "applied_indexed_candidate"
    assert applied["checkout_index_tree"] is not None
    assert all(value is False for value in applied["authority"].values())
    assert [row["path"] for row in applied["materialized_paths"]] == list(
        materializer.MATERIALIZED_PATHS
    )
    assert json.loads(candidate.manifest.read_text()) == applied
    staged = tuple(
        sorted(
            item.decode()
            for item in _git(
                candidate.repo, "diff", "--cached", "--name-only", "-z"
            ).split(b"\0")
            if item
        )
    )
    assert staged == materializer.MATERIALIZED_PATHS


def test_rejects_coherently_reformatted_but_false_candidate_report(
    tmp_path: Path,
) -> None:
    candidate = _candidate(tmp_path)
    report = json.loads(candidate.report.read_text())
    report["authority"]["release_authority"] = True
    _write_json(candidate.report, report)

    with pytest.raises(
        materializer.MaterializationError,
        match="independent recomposition",
    ):
        _check(candidate)


def test_rejects_extra_run_snapshot_entry(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    extra = candidate.snapshot / "unexpected"
    extra.write_bytes(b"unexpected")

    with pytest.raises(ExecutionError, match="inventory mismatch"):
        _check(candidate)


def test_rejects_dirty_checkout_before_reading_candidate(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    (candidate.repo / "untracked.txt").write_text("dirty", encoding="utf-8")

    with pytest.raises(materializer.MaterializationError, match="clean checkout"):
        _check(candidate)


def test_apply_rejects_untracked_path_created_during_patch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    original = materializer.git_boundary._run_git_apply

    def raced(repo_root: Path, patch: bytes, *, check_only: bool) -> None:
        original(repo_root, patch, check_only=check_only)
        if not check_only:
            (repo_root / "intruder").write_bytes(b"race")

    monkeypatch.setattr(materializer.git_boundary, "_run_git_apply", raced)

    with pytest.raises(
        materializer.MaterializationPartialStateError,
        match="external checkout changes remain",
    ):
        materializer.apply_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
                run_snapshot_root=candidate.snapshot,
            ),
            manifest_output=candidate.manifest,
        )

    assert not _git(candidate.repo, "diff", "--cached", "--name-only")
    assert (candidate.repo / "intruder").read_bytes() == b"race"
    assert not candidate.manifest.exists()


def test_rejects_checkout_switch_after_patch_check(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    replacement = _replacement_commit(candidate.repo)
    original = materializer.git_boundary._expected_materialized_tree

    def switched(
        repo_root: Path,
        source_commit: str,
        after: Mapping[str, bytes],
        paths: Sequence[str],
    ) -> str:
        expected = original(repo_root, source_commit, after, paths)
        _git(candidate.repo, "checkout", "--detach", replacement)
        return expected

    monkeypatch.setattr(
        materializer.git_boundary,
        "_expected_materialized_tree",
        switched,
    )

    with pytest.raises(
        materializer.MaterializationPartialStateError,
        match="rollback could not be verified",
    ):
        materializer.apply_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
                run_snapshot_root=candidate.snapshot,
            ),
            manifest_output=candidate.manifest,
        )

    assert not candidate.manifest.exists()


def test_rejects_manifest_parent_rename_and_redirect(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    output_parent = tmp_path / "manifest-parent"
    output_parent.mkdir(mode=0o700)
    output = output_parent / "manifest.json"
    moved_parent = tmp_path / "manifest-parent-moved"
    redirect = tmp_path / "manifest-redirect"
    original = materializer.git_boundary.require_materialized_state

    def redirected(
        repo_root: Path,
        source_commit: str,
        expected_tree: str,
        after: Mapping[str, bytes],
        paths: Sequence[str],
    ) -> None:
        original(repo_root, source_commit, expected_tree, after, paths)
        output_parent.rename(moved_parent)
        redirect.mkdir(mode=0o700)
        output_parent.symlink_to(redirect, target_is_directory=True)

    monkeypatch.setattr(
        materializer.git_boundary,
        "require_materialized_state",
        redirected,
    )

    with pytest.raises(
        materializer.MaterializationError,
        match="manifest output parent path changed",
    ):
        materializer.apply_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
                run_snapshot_root=candidate.snapshot,
            ),
            manifest_output=output,
        )

    assert not (redirect / "manifest.json").exists()
    assert not (moved_parent / "manifest.json").exists()
    assert not _git(candidate.repo, "status", "--porcelain")


def test_planner_and_snapshot_reject_git_replace_refs(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    replacement = _replacement_commit(candidate.repo)
    _git(candidate.repo, "replace", fixtures.SOURCE_COMMIT, replacement)

    with pytest.raises(planner.RebuildPlanError, match="replace refs"):
        planner.build_plan(
            fixtures.SOURCE_COMMIT,
            (tmp_path / "replacement-run").as_posix(),
            repo_root=candidate.repo,
        )
    with pytest.raises(planner.RebuildPlanError, match="replace refs"):
        GitSnapshotter().materialize(
            candidate.repo,
            fixtures.SOURCE_COMMIT,
            tmp_path / "replacement-snapshot",
        )
