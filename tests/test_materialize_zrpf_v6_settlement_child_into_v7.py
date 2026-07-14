from __future__ import annotations

import copy
import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import test_materialize_zrpf_source_opened_spot_v6_identity as v6_fixtures
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_identity_materialization as v6_materializer
from tools import zrpf_v6_v7_child_policy_materialization as materializer
from tools.zrpf_v6_identity_source_snapshot import GitSnapshotter, snapshot_root


@dataclass(frozen=True)
class _Candidate:
    repo: Path
    c1_commit: str
    plan: Path
    observations: Path
    report: Path
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


def _candidate(tmp_path: Path) -> _Candidate:
    source = v6_fixtures._candidate(tmp_path)
    _git(
        source.repo,
        "sparse-checkout",
        "add",
        materializer.V7_CHILD_POLICY_PATH,
    )
    v6_materializer.apply_materialization(
        v6_materializer.MaterializationRequest(
            repo_root=source.repo,
            plan_path=source.plan,
            observations_path=source.observations,
            report_path=source.report,
            run_snapshot_root=source.snapshot,
        ),
        manifest_output=source.manifest,
    )
    _git(
        source.repo,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "materialize V6 identities",
    )
    return _Candidate(
        repo=source.repo,
        c1_commit=_git(source.repo, "rev-parse", "HEAD").decode().strip(),
        plan=source.plan,
        observations=source.observations,
        report=source.report,
        manifest=tmp_path / "v6-to-v7-materialization-manifest.json",
    )


def _request(candidate: _Candidate) -> materializer.MaterializationRequest:
    return materializer.MaterializationRequest(
        repo_root=candidate.repo,
        c1_commit=candidate.c1_commit,
        plan_path=candidate.plan,
        observations_path=candidate.observations,
        report_path=candidate.report,
    )


def _stage_v6_transition_at_c0(
    candidate: _Candidate,
    *,
    manifest_output: Path,
) -> str:
    plan = json.loads(candidate.plan.read_text(encoding="utf-8"))
    c0_commit = plan["source_commit"]
    _git(candidate.repo, "checkout", "--detach", c0_commit)
    v6_materializer.apply_materialization(
        v6_materializer.MaterializationRequest(
            repo_root=candidate.repo,
            plan_path=candidate.plan,
            observations_path=candidate.observations,
            report_path=candidate.report,
            run_snapshot_root=Path(plan["host_run_root"]) / "source-snapshot",
        ),
        manifest_output=manifest_output,
    )
    return c0_commit


def _settlement_program(candidate: _Candidate) -> dict:
    report = json.loads(candidate.report.read_text(encoding="utf-8"))
    return next(row for row in report["programs"] if row["stage_id"] == "v6_settlement")


def test_cli_help_works_without_pythonpath() -> None:
    completed = subprocess.run(
        [
            "/usr/bin/python3",
            "tools/materialize_zrpf_v6_settlement_child_into_v7.py",
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


def test_v7_policy_unit_test_accepts_placeholder_and_materialized_states() -> None:
    source = (planner.REPO_ROOT / materializer.V7_CHILD_POLICY_PATH).read_text(encoding="utf-8")

    assert "assert_eq!(FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1, [0; 8]);" not in source
    assert "if configured.iter().all(|word| *word == 0)" in source
    assert "assert_eq!(result, Ok(configured));" in source


def test_check_is_nonmutating_and_binds_exact_c1_and_settlement_image(
    tmp_path: Path,
) -> None:
    candidate = _candidate(tmp_path)
    before = (candidate.repo / materializer.V7_CHILD_POLICY_PATH).read_bytes()

    manifest = materializer.check_materialization(_request(candidate))

    assert manifest["status"] == "checked_not_applied"
    assert manifest["c1_commit"] == candidate.c1_commit
    assert manifest["c0_commit"] == json.loads(candidate.plan.read_text())["source_commit"]
    assert manifest["v6_settlement_image_id"] == _settlement_program(candidate)["image_id"]
    assert manifest["checkout_index_tree"] is None
    assert all(value is False for value in manifest["authority"].values())
    assert (candidate.repo / materializer.V7_CHILD_POLICY_PATH).read_bytes() == before
    assert not _git(candidate.repo, "status", "--porcelain")


def test_apply_stages_only_v7_child_policy_and_emits_canonical_manifest(
    tmp_path: Path,
) -> None:
    candidate = _candidate(tmp_path)
    expected = _settlement_program(candidate)

    manifest = materializer.apply_materialization(
        _request(candidate),
        manifest_output=candidate.manifest,
    )

    assert manifest["status"] == "applied_indexed_candidate"
    assert manifest["v6_settlement_image_id_words"] == expected["image_id_words"]
    assert json.loads(candidate.manifest.read_text(encoding="utf-8")) == manifest
    assert _git(candidate.repo, "diff", "--cached", "--name-only").decode().splitlines() == [
        materializer.V7_CHILD_POLICY_PATH
    ]
    updated = (candidate.repo / materializer.V7_CHILD_POLICY_PATH).read_text()
    assert "FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1" in updated
    assert "= [0; 8];" not in updated


def test_rejects_checkout_that_is_not_the_exact_supplied_c1(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)

    with pytest.raises(materializer.MaterializationError, match="differs from supplied C1"):
        materializer.check_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                c1_commit="f" * 40,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
            )
        )


def test_rejects_noncanonical_repository_root(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    linked_root = tmp_path / "checkout-link"
    linked_root.symlink_to(candidate.repo, target_is_directory=True)

    with pytest.raises(materializer.MaterializationError, match="exact canonical path"):
        materializer.check_materialization(
            materializer.MaterializationRequest(
                repo_root=linked_root,
                c1_commit=candidate.c1_commit,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
            )
        )


def test_rejects_c1_with_an_extra_transition_path(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    readme = candidate.repo / "zk/spot_settlement_v7_risc0/README.md"
    _git(
        candidate.repo,
        "sparse-checkout",
        "add",
        "zk/spot_settlement_v7_risc0/README.md",
    )
    c0_commit = _stage_v6_transition_at_c0(
        candidate,
        manifest_output=tmp_path / "extra-path-v6-manifest.json",
    )
    readme.write_bytes(readme.read_bytes() + b"\nextra C1 change\n")
    _git(candidate.repo, "add", readme.relative_to(candidate.repo).as_posix())
    _git(
        candidate.repo,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "V6 materialization with unrelated C1 transition",
    )
    altered = _git(candidate.repo, "rev-parse", "HEAD").decode().strip()
    parents = _git(candidate.repo, "rev-list", "--parents", "-n", "1", altered)
    assert parents.decode().strip().split() == [altered, c0_commit]

    with pytest.raises(materializer.MaterializationError, match="path set differs"):
        materializer.check_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                c1_commit=altered,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
            )
        )


def test_rejects_git_graft_that_forges_direct_c1_parent(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    c0_commit = json.loads(candidate.plan.read_text(encoding="utf-8"))["source_commit"]
    _git(
        candidate.repo,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "--allow-empty",
        "-m",
        "unrelated real C1 parent",
    )
    grafted = _git(candidate.repo, "rev-parse", "HEAD").decode().strip()
    actual_parents = _git(
        candidate.repo,
        "cat-file",
        "commit",
        grafted,
    ).split(b"\n\n", 1)[0]
    assert f"parent {candidate.c1_commit}".encode() in actual_parents.splitlines()
    graft_path = Path(
        _git(
            candidate.repo,
            "rev-parse",
            "--path-format=absolute",
            "--git-path",
            "info/grafts",
        )
        .decode()
        .strip()
    )
    graft_path.parent.mkdir(parents=True, exist_ok=True)
    graft_path.write_text(f"{grafted} {c0_commit}\n", encoding="ascii")
    _git(candidate.repo, "config", "advice.graftFileDeprecated", "false")

    with pytest.raises(materializer.MaterializationError, match="grafts are forbidden"):
        materializer.check_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                c1_commit=grafted,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
            )
        )


def test_rejects_c1_with_expected_paths_but_wrong_materialized_bytes(
    tmp_path: Path,
) -> None:
    candidate = _candidate(tmp_path)
    _stage_v6_transition_at_c0(
        candidate,
        manifest_output=tmp_path / "wrong-byte-v6-manifest.json",
    )
    altered_path = candidate.repo / v6_materializer.MATERIALIZED_PATHS[0]
    altered_path.write_bytes(altered_path.read_bytes() + b"\nwrong materialized byte\n")
    _git(candidate.repo, "add", altered_path.relative_to(candidate.repo).as_posix())
    _git(
        candidate.repo,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "wrong V6 materialization",
    )
    altered_c1 = _git(candidate.repo, "rev-parse", "HEAD").decode().strip()

    with pytest.raises(materializer.MaterializationError, match="bytes differ"):
        materializer.check_materialization(
            materializer.MaterializationRequest(
                repo_root=candidate.repo,
                c1_commit=altered_c1,
                plan_path=candidate.plan,
                observations_path=candidate.observations,
                report_path=candidate.report,
            )
        )


def test_requires_exactly_one_settlement_program() -> None:
    row = {
        "stage_id": "v6_settlement",
        "image_id": "01" * 32,
        "image_id_words": [1] * 8,
        "program_binary_file": "source_opened_spot_settlement_v6.bin",
        "program_binary_bytes": 1,
        "program_binary_sha256": "02" * 32,
    }

    with pytest.raises(materializer.MaterializationError, match="exactly one"):
        materializer._select_settlement_program([row, dict(row)])


def test_rejects_zero_settlement_image_before_v7_render() -> None:
    row = {
        "stage_id": "v6_settlement",
        "image_id": "00" * 32,
        "image_id_words": [0] * 8,
    }

    with pytest.raises(materializer.MaterializationError, match="must be nonzero"):
        materializer._select_settlement_program([row])


def test_rejects_zero_settlement_image_end_to_end(tmp_path: Path) -> None:
    source = v6_fixtures._candidate(tmp_path)
    _git(
        source.repo,
        "sparse-checkout",
        "add",
        materializer.V7_CHILD_POLICY_PATH,
    )
    plan = json.loads(source.plan.read_text(encoding="utf-8"))
    observations = json.loads(source.observations.read_text(encoding="utf-8"))
    zero_program = copy.deepcopy(observations["stages"][-1]["program"])
    zero_program["image_id"] = "00" * 32
    zero_program["image_id_words"] = [0] * 8
    observations["stages"][-1]["program"] = copy.deepcopy(zero_program)
    observations["stages"][-1]["repins"][0]["value"] = [0] * 8
    observations["settlement_self_image_two_pass"]["second_pass_program"] = copy.deepcopy(
        zero_program
    )
    observations["final_clean_rebuild"]["programs"][-1] = copy.deepcopy(zero_program)
    observations["host_verifier"]["expected_settlement_image_id"] = "00" * 32

    shutil.rmtree(source.snapshot)
    snapshot = GitSnapshotter().materialize(
        source.repo,
        plan["source_commit"],
        source.snapshot,
    )
    v6_fixtures._apply_observed_transition(snapshot.root, plan, observations)
    final_root = snapshot_root(snapshot)
    observations["final_clean_rebuild"]["final_source_snapshot_root_sha256"] = final_root
    observations["host_verifier"]["source_snapshot_root_sha256"] = final_root
    report = planner.check_observations(plan, observations, repo_root=source.repo)
    source.observations.write_bytes(planner.canonical_bytes(observations))
    source.report.write_bytes(planner.canonical_bytes(report))
    v6_materializer.apply_materialization(
        v6_materializer.MaterializationRequest(
            repo_root=source.repo,
            plan_path=source.plan,
            observations_path=source.observations,
            report_path=source.report,
            run_snapshot_root=source.snapshot,
        ),
        manifest_output=source.manifest,
    )
    _git(
        source.repo,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "materialize zero V6 settlement candidate",
    )
    c1_commit = _git(source.repo, "rev-parse", "HEAD").decode().strip()

    with pytest.raises(materializer.MaterializationError, match="must be nonzero"):
        materializer.check_materialization(
            materializer.MaterializationRequest(
                repo_root=source.repo,
                c1_commit=c1_commit,
                plan_path=source.plan,
                observations_path=source.observations,
                report_path=source.report,
            )
        )


def test_rejects_nonzero_v7_placeholder() -> None:
    raw = (
        b"pub const FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1: "
        b"[u32; 8] = [1, 0, 0, 0, 0, 0, 0, 0];\n"
    )

    with pytest.raises(materializer.MaterializationError, match="all-zero placeholder"):
        materializer._require_zero_v7_placeholder(raw)


def test_apply_rolls_back_if_manifest_write_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    before = (candidate.repo / materializer.V7_CHILD_POLICY_PATH).read_bytes()

    def fail_write(*_args: object, **_kwargs: object) -> None:
        raise materializer.MaterializationError("injected manifest failure")

    monkeypatch.setattr(materializer.output_boundary, "write_external_output", fail_write)

    with pytest.raises(materializer.MaterializationError, match="injected manifest"):
        materializer.apply_materialization(
            _request(candidate),
            manifest_output=candidate.manifest,
        )

    assert (candidate.repo / materializer.V7_CHILD_POLICY_PATH).read_bytes() == before
    assert not _git(candidate.repo, "status", "--porcelain")
    assert not candidate.manifest.exists()


def test_close_failure_after_manifest_commit_preserves_success(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate(tmp_path)
    original = materializer.output_boundary.close_external_output

    def close_then_fail(output: materializer.output_boundary.ExternalOutput) -> None:
        original(output)
        raise OSError("injected post-commit close failure")

    monkeypatch.setattr(
        materializer.output_boundary,
        "close_external_output",
        close_then_fail,
    )

    manifest = materializer.apply_materialization(
        _request(candidate),
        manifest_output=candidate.manifest,
    )

    assert manifest["status"] == "applied_indexed_candidate"
    assert json.loads(candidate.manifest.read_text(encoding="utf-8")) == manifest
    assert _git(candidate.repo, "diff", "--cached", "--name-only").decode().splitlines() == [
        materializer.V7_CHILD_POLICY_PATH
    ]
