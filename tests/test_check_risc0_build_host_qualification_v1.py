from __future__ import annotations

import os
import subprocess
from pathlib import Path
from typing import cast

import pytest

from tools import build_risc0_build_host_qualification_v1 as builder
from tools import check_risc0_build_host_qualification_v1 as checker
from tools.risc0_build_host_qualification_v1 import (
    ARTIFACT_PATH_V1,
    BUILDER_PATH_V1,
    CHECKER_PATH_V1,
    CORE_PATH_V1,
    DEPENDENCY_AUDIT_CHECKER_PATH_V1,
    DEPENDENCY_INVENTORY_PATH_V1,
    DEPENDENCY_POLICY_PATH_V1,
    EXACT_O008A_PLAN_ROW_V1,
    LEGACY_LOCK_PATH_V1,
    PLAN_PATH_V1,
    REQUIRED_RISC0_VERSION_V1,
    TEST_PATH_V1,
    QualificationRejectV1,
    QualificationSourceSnapshotV1,
    ResourceObservationV1,
    build_qualification_artifact_v1,
    canonical_json_bytes_v1,
    decode_json_object_v1,
)

ROOT = Path(__file__).resolve().parents[1]


def _json_object(value: object) -> dict[str, object]:
    if type(value) is not dict:
        raise TypeError("test fixture expected an exact JSON object")
    return cast(dict[str, object], value)


def _json_array(value: object) -> list[object]:
    if type(value) is not list:
        raise TypeError("test fixture expected an exact JSON array")
    return cast(list[object], value)


def _expect(condition: bool, message: str) -> None:
    """Keep the replay tests effective when Python executes with -O."""

    if not condition:
        raise AssertionError(message)


def _git(repo: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ("git", *arguments),
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return completed.stdout.strip()


def _write(repo: Path, relative_path: str, raw: bytes) -> None:
    destination = repo / relative_path
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(raw)


def _cargo_manifest(requirement: str) -> bytes:
    return (
        "[workspace]\n"
        "members = []\n"
        "resolver = \"2\"\n\n"
        "[dependencies]\n"
        f"risc0-build = \"{requirement}\"\n"
        f"risc0-zkvm = \"{requirement}\"\n"
    ).encode("utf-8")


def _cargo_lock(version: str) -> bytes:
    checksum = "0" * 64
    return (
        "version = 4\n\n"
        "[[package]]\n"
        "name = \"risc0-build\"\n"
        f"version = \"{version}\"\n"
        "source = \"registry+https://github.com/rust-lang/crates.io-index\"\n"
        f"checksum = \"{checksum}\"\n\n"
        "[[package]]\n"
        "name = \"risc0-zkvm\"\n"
        f"version = \"{version}\"\n"
        "source = \"registry+https://github.com/rust-lang/crates.io-index\"\n"
        f"checksum = \"{checksum}\"\n"
    ).encode("utf-8")


def _bootstrap_two_commit_subject(
    tmp_path: Path,
    *,
    manifest_requirement: str = "1.2",
    lock_version: str = "1.2.6",
) -> tuple[Path, str, str]:
    """Create P then C in a private Git repo; E is intentionally absent."""

    repo = tmp_path / "o008a-replay"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "o008a@example.invalid")
    _git(repo, "config", "user.name", "O008A Test")
    _write(repo, PLAN_PATH_V1, canonical_json_bytes_v1({"next_obligations": [EXACT_O008A_PLAN_ROW_V1]}))
    for relative_path in (
        DEPENDENCY_POLICY_PATH_V1,
        DEPENDENCY_INVENTORY_PATH_V1,
        DEPENDENCY_AUDIT_CHECKER_PATH_V1,
    ):
        _write(repo, relative_path, (ROOT / relative_path).read_bytes())
    _write(repo, "zk/state_proof_risc0/Cargo.toml", _cargo_manifest(manifest_requirement))
    _write(repo, LEGACY_LOCK_PATH_V1, _cargo_lock(lock_version))
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "P fixture")
    base_commit = _git(repo, "rev-parse", "HEAD")

    for relative_path in (CORE_PATH_V1, BUILDER_PATH_V1, CHECKER_PATH_V1, TEST_PATH_V1):
        _write(repo, relative_path, (ROOT / relative_path).read_bytes())
    _git(repo, "add", CORE_PATH_V1, BUILDER_PATH_V1, CHECKER_PATH_V1, TEST_PATH_V1)
    _git(repo, "commit", "-qm", "C implementation subject")
    implementation_commit = _git(repo, "rev-parse", "HEAD")
    return repo, base_commit, implementation_commit


def _create_artifact_only_e(repo: Path, base_commit: str) -> str:
    outcome = builder.build_artifact_for_head_v1(repo, expected_parent=base_commit)
    _expect(outcome.replay_ready is True, "C must produce a replay-ready artifact")
    raw = canonical_json_bytes_v1(outcome.artifact)
    builder.write_artifact_atomically_v1(repo, raw)
    _git(repo, "add", ARTIFACT_PATH_V1)
    _git(repo, "commit", "-qm", "E source-bound O-008A artifact")
    return _git(repo, "rev-parse", "HEAD")


def _toolchain_passing_snapshot() -> QualificationSourceSnapshotV1:
    """Build a pure C fixture for resource replay without a Rust invocation."""

    exact_manifest_rows: tuple[dict[str, object], ...] = (
        {
            "manifest": "zk/state_proof_risc0/Cargo.toml",
            "package": "risc0-build",
            "requirement": "=3.0.6",
        },
        {
            "manifest": "zk/state_proof_risc0/Cargo.toml",
            "package": "risc0-zkvm",
            "requirement": "=3.0.6",
        },
    )
    exact_lock_rows: tuple[dict[str, object], ...] = (
        {"package": "risc0-build", "versions": [REQUIRED_RISC0_VERSION_V1]},
        {"package": "risc0-zkvm", "versions": [REQUIRED_RISC0_VERSION_V1]},
    )
    return QualificationSourceSnapshotV1(
        base_commit="a" * 40,
        implementation_commit="b" * 40,
        implementation_tree="c" * 40,
        source_entries=(),
        exact_plan_row=dict(EXACT_O008A_PLAN_ROW_V1),
        required_version_source=REQUIRED_RISC0_VERSION_V1,
        dependency_policy_report={"ok": True},
        legacy_manifest_requirements=exact_manifest_rows,
        legacy_lock_versions=exact_lock_rows,
    )


def _replay_resource_projection(snapshot: QualificationSourceSnapshotV1, resource: ResourceObservationV1) -> dict[str, object]:
    """Use the builder's parser as the independent replay boundary."""

    artifact = build_qualification_artifact_v1(snapshot, resource=resource)
    recovered = builder.resource_observation_from_artifact_v1(artifact)
    replayed = build_qualification_artifact_v1(snapshot, resource=recovered)
    _expect(
        canonical_json_bytes_v1(replayed) == canonical_json_bytes_v1(artifact),
        "artifact resource projection must replay byte-for-byte",
    )
    return artifact


def test_given_exact_p_c_e_when_replayed_then_the_blocked_artifact_is_source_bound(tmp_path: Path) -> None:
    # Given the exact P -> C -> E evidence chain.
    repo, base_commit, implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    artifact_commit = _create_artifact_only_e(repo, base_commit)

    # When the checker receives E itself.
    report = checker.check_risc0_build_host_qualification_v1(root=repo, expected_parent=base_commit)

    # Then it verifies the E blob, Git mode, live bytes, and blocked projection.
    _expect(report["artifact_valid"] is True, "exact P -> C -> E replay must validate")
    _expect(report["status"] == "BLOCKED_TOOLCHAIN_VERSION_MISMATCH", "legacy toolchain must remain blocked")
    _expect(
        _json_object(report["claim_scope"])["build_host_qualified"] is False,
        "replay must not qualify the build host",
    )
    artifact = decode_json_object_v1(
        _git(repo, "show", f"{artifact_commit}:{ARTIFACT_PATH_V1}").encode("utf-8"),
        ARTIFACT_PATH_V1,
    )
    _expect(_json_object(artifact["replay"])["base_commit"] == base_commit, "artifact must bind P")
    _expect(
        _json_object(artifact["replay"])["implementation_commit"] == implementation_commit,
        "artifact must bind C",
    )
    _expect(
        _json_object(artifact["execution"])["network"] == "NETWORK_NOT_REQUESTED",
        "network must remain unrequested",
    )
    _expect(
        _json_object(artifact["trust_nonclaims"])["git_object_store_trust"] == "NOT_CLAIMED",
        "object-store trust must remain a nonclaim",
    )
    _expect(
        _json_object(report["trust_nonclaims"])["immutable_checker_bootstrap"]
        == "EXTERNAL_PINNED_LAUNCHER_REQUIRED",
        "the checker must name its immutable bootstrap prerequisite",
    )
    evidence = _json_object(report["exact_evidence"])
    _expect(evidence["evidence_commit"] == artifact_commit, "the report must bind the exact E commit")
    _expect(evidence["artifact_git_mode"] == "100644", "the report must bind E's exact Git mode")
    _expect(type(evidence["artifact_blob_oid"]) is str, "the report must bind E's artifact blob")
    _expect(type(evidence["artifact_size_bytes"]) is int, "the report must bind E's artifact size")


def test_ripr_given_descendant_source_mutation_when_checked_then_replay_rejects_before_descendant_execution(
    tmp_path: Path,
) -> None:
    # Reach and infect a source path after an otherwise valid E.
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    _create_artifact_only_e(repo, base_commit)
    with (repo / CORE_PATH_V1).open("ab") as source_file:
        source_file.write(b"\n# descendant source drift\n")
    _git(repo, "add", CORE_PATH_V1)
    _git(repo, "commit", "-qm", "D relevant source drift")

    # Propagation and reveal occur at exact-E admission, before any D replay.
    report = checker.check_risc0_build_host_qualification_v1(root=repo, expected_parent=base_commit)

    _expect(report["artifact_valid"] is False, "a descendant must invalidate exact-E replay")
    _expect(report["status"] == "REJECTED_DESCENDANT_REPLAY", "descendant replay needs a typed reject")
    _expect(
        report["findings"]
        == [
            {
                "code": "DESCENDANT_REPLAY_FORBIDDEN",
                "path": _git(repo, "rev-parse", "HEAD"),
                "detail": "HEAD is not exact artifact commit E",
            }
        ],
        "the reject must bind the descendant commit rather than execute its source",
    )


def test_ripr_given_legacy_manifests_at_1_2_and_lock_mutated_to_3_0_6_then_manifest_still_blocks(tmp_path: Path) -> None:
    # A lock-only mutant used to reach a later gate. The independent manifest observation kills it.
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(
        tmp_path,
        manifest_requirement="1.2",
        lock_version=REQUIRED_RISC0_VERSION_V1,
    )

    outcome = builder.build_artifact_for_head_v1(repo, expected_parent=base_commit)

    _expect(outcome.replay_ready is True, "C must remain replay-ready while blocked")
    _expect(
        _json_object(outcome.artifact["result"])["status"] == "BLOCKED_TOOLCHAIN_VERSION_MISMATCH",
        "manifest 1.2 must block even after a lock-only 3.0.6 mutation",
    )
    _expect(
        _json_object(outcome.artifact["toolchain"])["legacy_manifest_risc0_requirements"]
        == [
            {
                "manifest": "zk/state_proof_risc0/Cargo.toml",
                "package": "risc0-build",
                "requirement": "1.2",
            },
            {
                "manifest": "zk/state_proof_risc0/Cargo.toml",
                "package": "risc0-zkvm",
                "requirement": "1.2",
            },
        ],
        "artifact must record the independent manifest observations",
    )
    _expect(
        _json_object(outcome.artifact["resource_preflight"])["capture_state"]
        == "DEFERRED_UNTIL_TOOLCHAIN_GATES_PASS",
        "resource capture must be deferred before toolchain success",
    )


def test_given_lone_or_mixed_surrogate_json_escapes_when_decoded_then_typed_rejection_is_returned() -> None:
    for raw in (br'{"x":"\ud800"}', br'{"x":"safe\ud800\u0061"}'):
        with pytest.raises(QualificationRejectV1) as raised:
            decode_json_object_v1(raw, "hostile.json")
        _expect(raised.value.code == "JSON_STRING_SURROGATE", "surrogates need a typed rejection")


def test_given_duplicate_plan_key_when_decoded_then_typed_rejection_is_returned() -> None:
    with pytest.raises(QualificationRejectV1) as raised:
        decode_json_object_v1(b'{"next_obligations":[],"next_obligations":[]}', PLAN_PATH_V1)
    _expect(raised.value.code == "JSON_DUPLICATE_KEY", "duplicate plan keys need a typed rejection")


def test_given_only_p_when_built_then_a_stale_untrusted_placeholder_is_written(tmp_path: Path) -> None:
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    _git(repo, "reset", "--hard", base_commit)

    outcome = builder.build_artifact_for_head_v1(repo, expected_parent=base_commit)

    _expect(outcome.replay_ready is False, "P cannot be treated as C")
    _expect(
        outcome.artifact["artifact_state"] == "STALE_UNTRUSTED_IMPLEMENTATION_AND_ARTIFACT_COMMITS_REQUIRED",
        "P-only output must be visibly untrusted",
    )
    _expect(
        _json_object(outcome.artifact["result"])["status"] == "BLOCKED_IMPLEMENTATION_COMMIT_REQUIRED",
        "P-only output must name the coordinator blocker",
    )


def test_given_e_with_an_extra_path_when_replayed_then_exact_artifact_only_shape_rejects(tmp_path: Path) -> None:
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    outcome = builder.build_artifact_for_head_v1(repo, expected_parent=base_commit)
    _expect(outcome.replay_ready is True, "C must produce a replay-ready artifact")
    builder.write_artifact_atomically_v1(repo, canonical_json_bytes_v1(outcome.artifact))
    _write(repo, "extra-e-path.txt", b"E must not carry this path\n")
    _git(repo, "add", ARTIFACT_PATH_V1, "extra-e-path.txt")
    _git(repo, "commit", "-qm", "malformed E with extra path")

    report = checker.check_risc0_build_host_qualification_v1(root=repo, expected_parent=base_commit)

    _expect(report["artifact_valid"] is False, "non-artifact E contents must reject replay")
    _expect(report["status"] == "REJECTED_ARTIFACT_COMMIT_SHAPE", "E shape needs a typed rejection")


def test_ripr_given_symlink_artifact_at_e_when_checked_then_git_mode_rejects(tmp_path: Path) -> None:
    # Arrange a direct E whose artifact is a Git symlink instead of mode 100644.
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    outcome = builder.build_artifact_for_head_v1(repo, expected_parent=base_commit)
    _expect(outcome.replay_ready is True, "C must produce a blocked E candidate")
    outside = tmp_path / "outside-artifact.json"
    outside.write_bytes(canonical_json_bytes_v1(outcome.artifact))
    artifact_path = repo / ARTIFACT_PATH_V1
    artifact_path.symlink_to(outside)
    _git(repo, "add", ARTIFACT_PATH_V1)
    _git(repo, "commit", "-qm", "E symlink artifact mutant")

    # Act.
    report = checker.check_risc0_build_host_qualification_v1(root=repo, expected_parent=base_commit)

    # Assert the Git tree mode, rather than mutable path resolution, owns admission.
    _expect(report["artifact_valid"] is False, "symlink artifact cannot be evidence")
    _expect(report["status"] == "REJECTED_ARTIFACT_GIT_MODE", "symlink needs an exact mode reject")
    _expect(
        _json_object(_json_array(report["findings"])[0])["code"]
        == "ARTIFACT_GIT_MODE",
        "the Git-mode mutant must propagate to the observable reject",
    )


def test_ripr_given_committed_artifact_replacement_after_e_when_checked_then_descendant_rejects(tmp_path: Path) -> None:
    # Arrange valid E followed by an attacker-controlled artifact replacement in D.
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    _create_artifact_only_e(repo, base_commit)
    _write(repo, ARTIFACT_PATH_V1, b'{"attacker_claim":"QUALIFIED"}')
    _git(repo, "add", ARTIFACT_PATH_V1)
    _git(repo, "commit", "-qm", "D artifact replacement mutant")

    # Act.
    report = checker.check_risc0_build_host_qualification_v1(root=repo, expected_parent=base_commit)

    # Assert historical E cannot be replayed through the mutable descendant.
    _expect(report["artifact_valid"] is False, "a replacement descendant cannot inherit E validity")
    _expect(report["status"] == "REJECTED_DESCENDANT_REPLAY", "replacement needs an exact-E reject")


def test_ripr_given_uncommitted_artifact_replacement_at_e_when_checked_then_live_ambiguity_rejects(
    tmp_path: Path,
) -> None:
    # Arrange an exact E with only its live artifact bytes replaced.
    repo, base_commit, _implementation_commit = _bootstrap_two_commit_subject(tmp_path)
    _create_artifact_only_e(repo, base_commit)
    _write(repo, ARTIFACT_PATH_V1, b'{"attacker_claim":"QUALIFIED"}')

    # Act.
    report = checker.check_risc0_build_host_qualification_v1(root=repo, expected_parent=base_commit)

    # Assert the clean-worktree guard closes the historical/live ambiguity.
    _expect(report["artifact_valid"] is False, "dirty live artifact cannot inherit E validity")
    _expect(report["status"] == "REJECTED_LIVE_ARTIFACT_AMBIGUITY", "live replacement needs a typed reject")
    _expect(
        _json_object(_json_array(report["findings"])[0])["code"]
        == "LIVE_WORKTREE_AMBIGUITY",
        "the dirty artifact must reach the live-binding reject",
    )


def test_ripr_given_unavailable_resource_observation_when_projected_then_insufficient_replays(tmp_path: Path) -> None:
    del tmp_path  # The pure projection requires no filesystem or subprocess observation.
    snapshot = _toolchain_passing_snapshot()
    unavailable = ResourceObservationV1(
        tmpdir_matches_required=True,
        free_tmp_bytes=None,
        available_memory_bytes=128 * 1024 * 1024,
    )

    artifact = _replay_resource_projection(snapshot, unavailable)

    projection = _json_object(artifact["resource_preflight"])
    _expect(
        projection["capture_state"] == "INSUFFICIENT_AFTER_TOOLCHAIN_GATES_PASS",
        "missing resource observation must use the canonical insufficient state",
    )
    _expect(
        _json_object(artifact["result"])["status"] == "BLOCKED_RESOURCE_EVIDENCE_INSUFFICIENT",
        "unavailable observation must retain the blocked status after replay",
    )
    _expect(
        "observed_tmp_free_bytes" not in projection and "observed_available_memory_bytes" not in projection,
        "insufficient projection must not serialize nullable observed values",
    )


def test_ripr_given_below_bound_resources_when_projected_then_budget_block_replays(tmp_path: Path) -> None:
    del tmp_path  # The pure projection requires no filesystem or subprocess observation.
    snapshot = _toolchain_passing_snapshot()
    below_bound = ResourceObservationV1(
        tmpdir_matches_required=True,
        free_tmp_bytes=50 * 1024 * 1024 - 1,
        available_memory_bytes=128 * 1024 * 1024,
    )

    artifact = _replay_resource_projection(snapshot, below_bound)

    projection = _json_object(artifact["resource_preflight"])
    _expect(
        projection["capture_state"] == "OBSERVED_AFTER_TOOLCHAIN_GATES_PASS",
        "integer observations below budget retain a replayable observed state",
    )
    _expect(
        _json_object(artifact["result"])["status"] == "BLOCKED_RESOURCE_BUDGET",
        "the one-byte-below temporary-space boundary must block",
    )


def test_given_a_symlink_target_when_writing_then_atomic_writer_refuses_it(tmp_path: Path) -> None:
    repo = tmp_path / "writer-repo"
    (repo / "docs/research").mkdir(parents=True)
    outside = tmp_path / "outside.json"
    (repo / ARTIFACT_PATH_V1).symlink_to(outside)

    with pytest.raises(builder.QualificationInputErrorV1) as raised:
        builder.write_artifact_atomically_v1(repo, b"{}")

    _expect(raised.value.code == "ARTIFACT_TARGET", "writer must reject a symlink target")
    _expect(os.path.lexists(repo / ARTIFACT_PATH_V1), "writer must leave the symlink untouched")
