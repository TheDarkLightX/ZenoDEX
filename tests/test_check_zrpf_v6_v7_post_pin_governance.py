from __future__ import annotations

import copy
import json
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import pytest

from tests import test_materialize_zrpf_v6_settlement_child_into_v7 as materializer_fixtures
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v6_v7_child_policy_materialization as materializer
from tools import zrpf_v6_v7_post_pin_governance as governance


@dataclass(frozen=True)
class _PostPinCandidate:
    repo: Path
    c1_commit: str
    c2_commit: str
    governance_commit: str
    plan: dict
    observations: dict
    report: dict
    manifest: dict


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


def _commit(root: Path, message: str) -> str:
    _git(
        root,
        "-c",
        "user.name=ZRPF Test",
        "-c",
        "user.email=zrpf-test@example.invalid",
        "commit",
        "--quiet",
        "-m",
        message,
    )
    return _git(root, "rev-parse", "HEAD").decode("ascii").strip()


def _write_canonical(root: Path, relative: str, document: dict) -> None:
    path = root / relative
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    path.write_bytes(planner.canonical_bytes(document))


def _candidate(
    tmp_path: Path,
    *,
    mutate_staged_pin: Callable[[Path], None] | None = None,
    add_c2_path: bool = False,
    mutate_manifest: Callable[[dict], None] | None = None,
    add_governance_path: bool = False,
    canonical_manifest: bool = True,
) -> _PostPinCandidate:
    source = materializer_fixtures._candidate(tmp_path)
    manifest = materializer.apply_materialization(
        materializer_fixtures._request(source),
        manifest_output=source.manifest,
    )
    if mutate_staged_pin is not None:
        mutate_staged_pin(source.repo)
        _git(source.repo, "add", materializer.V7_CHILD_POLICY_PATH)
    if add_c2_path:
        extra = "zk/spot_settlement_v7_risc0/README.md"
        _git(source.repo, "sparse-checkout", "add", extra)
        path = source.repo / extra
        path.write_bytes(path.read_bytes() + b"\nextra post-pin transition\n")
        _git(source.repo, "add", extra)
    c2_commit = _commit(source.repo, "materialize governed V7 child pin")

    _git(source.repo, "sparse-checkout", "add", *governance.EVIDENCE_PATHS)
    plan = json.loads(source.plan.read_text(encoding="utf-8"))
    observations = json.loads(source.observations.read_text(encoding="utf-8"))
    report = json.loads(source.report.read_text(encoding="utf-8"))
    committed_manifest = copy.deepcopy(manifest)
    if mutate_manifest is not None:
        mutate_manifest(committed_manifest)
    _write_canonical(source.repo, governance.PLAN_PATH, plan)
    _write_canonical(source.repo, governance.OBSERVATIONS_PATH, observations)
    _write_canonical(source.repo, governance.REPORT_PATH, report)
    if canonical_manifest:
        _write_canonical(source.repo, governance.MANIFEST_PATH, committed_manifest)
    else:
        path = source.repo / governance.MANIFEST_PATH
        path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        path.write_text(json.dumps(committed_manifest), encoding="utf-8")
    _git(source.repo, "add", "--", *governance.EVIDENCE_PATHS)
    if add_governance_path:
        extra = "evidence/zrpf_v6_to_v7_post_pin_v1/unexpected.json"
        _git(source.repo, "sparse-checkout", "add", extra)
        (source.repo / extra).write_bytes(planner.canonical_bytes({"unexpected": True}))
        _git(source.repo, "add", extra)
    governance_commit = _commit(source.repo, "commit V6 to V7 post-pin evidence")
    return _PostPinCandidate(
        repo=source.repo,
        c1_commit=source.c1_commit,
        c2_commit=c2_commit,
        governance_commit=governance_commit,
        plan=plan,
        observations=observations,
        report=report,
        manifest=committed_manifest,
    )


def test_cli_help_works_without_pythonpath() -> None:
    completed = subprocess.run(
        [
            "/usr/bin/python3",
            "tools/check_zrpf_v6_v7_post_pin_governance.py",
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
    assert b"authority-neutral" in completed.stdout
    assert not completed.stderr


def test_accepts_exact_four_commit_chain_and_preserves_all_nonclaims(
    tmp_path: Path,
) -> None:
    candidate = _candidate(tmp_path)

    result = governance.check_post_pin_governance(candidate.repo)

    assert result["status"] == "committed_post_pin_governance_binding_checked"
    assert result["c0_commit"] == candidate.plan["source_commit"]
    assert result["c1_commit"] == candidate.c1_commit
    assert result["c2_commit"] == candidate.c2_commit
    assert result["governance_commit"] == candidate.governance_commit
    assert result["v6_settlement_image_id"] == candidate.manifest["v6_settlement_image_id"]
    assert result["v7_child_policy_tree"] == candidate.manifest["checkout_index_tree"]
    assert all(value is True for value in result["validated_facts"].values())
    assert all(value is False for value in result["authority"].values())
    assert result["non_claims"] == list(governance.NON_CLAIMS)


def test_rejects_manual_post_pin_source_edit_even_when_committed(tmp_path: Path) -> None:
    def mutate(root: Path) -> None:
        path = root / materializer.V7_CHILD_POLICY_PATH
        path.write_bytes(path.read_bytes() + b"\n// unauthorized post-pin edit\n")

    candidate = _candidate(tmp_path, mutate_staged_pin=mutate)

    with pytest.raises(governance.GovernanceError, match="C2 child-policy bytes"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_extra_path_in_child_pin_commit(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path, add_c2_path=True)

    with pytest.raises(governance.GovernanceError, match="C2 transition path set"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_extra_path_in_governance_commit(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path, add_governance_path=True)

    with pytest.raises(governance.GovernanceError, match="governance transition path set"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_manifest_that_promotes_authority(tmp_path: Path) -> None:
    def mutate(manifest: dict) -> None:
        manifest["authority"]["release_authority"] = True

    candidate = _candidate(tmp_path, mutate_manifest=mutate)

    with pytest.raises(governance.GovernanceError, match="authority fields"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_manifest_image_words_that_do_not_match_report(tmp_path: Path) -> None:
    def mutate(manifest: dict) -> None:
        manifest["v6_settlement_image_id_words"][0] ^= 1

    candidate = _candidate(tmp_path, mutate_manifest=mutate)

    with pytest.raises(governance.GovernanceError, match="image words"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_noncanonical_committed_manifest(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path, canonical_manifest=False)

    with pytest.raises(planner.RebuildPlanError, match="canonical JSON"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_git_graft_even_when_it_preserves_visible_parent(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    graft_path = Path(
        _git(
            candidate.repo,
            "rev-parse",
            "--path-format=absolute",
            "--git-path",
            "info/grafts",
        )
        .decode("utf-8")
        .strip()
    )
    graft_path.parent.mkdir(parents=True, exist_ok=True)
    graft_path.write_text(
        f"{candidate.governance_commit} {candidate.c2_commit}\n",
        encoding="ascii",
    )
    _git(candidate.repo, "config", "advice.graftFileDeprecated", "false")

    with pytest.raises(governance.GovernanceError, match="grafts are forbidden"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_dirty_checkout_after_governance_commit(tmp_path: Path) -> None:
    candidate = _candidate(tmp_path)
    path = candidate.repo / governance.MANIFEST_PATH
    path.write_bytes(path.read_bytes() + b" ")

    with pytest.raises(governance.GovernanceError, match="clean checkout"):
        governance.check_post_pin_governance(candidate.repo)


def test_rejects_zero_settlement_identity_in_committed_manifest(tmp_path: Path) -> None:
    def mutate(manifest: dict) -> None:
        manifest["v6_settlement_image_id"] = "00" * 32
        manifest["v6_settlement_image_id_words"] = [0] * 8

    candidate = _candidate(tmp_path, mutate_manifest=mutate)

    with pytest.raises(governance.GovernanceError, match="image ID"):
        governance.check_post_pin_governance(candidate.repo)
