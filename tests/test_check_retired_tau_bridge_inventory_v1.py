from __future__ import annotations

import copy
import json
import shlex
import subprocess
import time
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools import build_retired_tau_bridge_inventory_v1 as builder_module
from tools import check_retired_tau_bridge_inventory_v1 as checker_module
from tools.build_retired_tau_bridge_inventory_v1 import (
    _run_git_v1,
    build_inventory_object_v1,
)
from tools.check_retired_tau_bridge_inventory_v1 import (
    validate_inventory_bytes_v1,
    validate_inventory_object_v1,
)
from tools.retired_tau_bridge_inventory_v1 import (
    EXPECTED_ARTIFACT_SHA256_V1,
    EXPECTED_CANDIDATE_FINGERPRINT_V1,
    INVENTORY_PATH_V1,
    PARENT_COMMIT_V1,
    PARENT_TREE_V1,
    REQUIRED_CLOSURE_PATHS_V1,
    InventoryRejectV1,
    canonical_json_bytes_v1,
    discover_source_signals_v1,
    scope_classes_v1,
    sha256_prefixed_v1,
    verify_route_static_guards_v1,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
EXPECTED_CLASS_COUNTS = {
    "ADAPTER": 267,
    "GENERATED": 112,
    "LAUNCHER_MANIFEST_CONFIG": 113,
    "PYTHON": 2450,
    "RUST": 221,
    "SHELL": 52,
    "TAU": 345,
    "TEST": 1319,
    "TEXT_SOURCE": 3731,
}
EXPECTED_SOURCE_SCOPE_ROOT = (
    "sha256:b0dbfb8c4c449b1a63ed43edd1fb7134601eea973f231e3db2e2ff01e36ebd6e"
)
CANDIDATE_PATHS = {
    INVENTORY_PATH_V1.as_posix(),
    "tests/integration/test_retired_tau_bridge_startup_refusal_v1.py",
    "tests/test_check_retired_tau_bridge_inventory_v1.py",
    "tools/build_retired_tau_bridge_inventory_v1.py",
    "tools/check_retired_tau_bridge_inventory_v1.py",
    "tools/retired_tau_bridge_inventory_v1.py",
}


@dataclass(frozen=True)
class ReplaySnapshot:
    raw: bytes
    artifact: dict[str, object]
    expected: dict[str, object]


@pytest.fixture(scope="module")
def replay_snapshot() -> ReplaySnapshot:
    raw = (REPO_ROOT / INVENTORY_PATH_V1).read_bytes()
    artifact: dict[str, object] = json.loads(raw)
    expected = build_inventory_object_v1(REPO_ROOT)
    return ReplaySnapshot(raw=raw, artifact=artifact, expected=expected)


@pytest.fixture(scope="module")
def closure_sources() -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    for path in sorted(REQUIRED_CLOSURE_PATHS_V1):
        completed = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "show", f"{PARENT_COMMIT_V1}:{path}"],
            check=True,
            capture_output=True,
            timeout=10,
        )
        result[path] = completed.stdout
    return result


def _object(value: object) -> dict[str, object]:
    assert type(value) is dict
    return value


def _list(value: object) -> list[object]:
    assert type(value) is list
    return value


def _reject_code(call: Callable[[], object], expected: str) -> None:
    with pytest.raises(InventoryRejectV1) as raised:
        call()
    assert raised.value.code == expected


def _replace_once(raw: bytes, old: bytes, new: bytes) -> bytes:
    assert raw.count(old) == 1
    return raw.replace(old, new, 1)


def _test_git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=True,
        capture_output=True,
        text=True,
        timeout=10,
    )
    return result.stdout.strip()


def _commit_test_repo(root: Path, message: str) -> str:
    _test_git(root, "add", ".")
    _test_git(
        root,
        "-c",
        "user.name=O003B Test",
        "-c",
        "user.email=o003b@example.invalid",
        "commit",
        "-m",
        message,
    )
    return _test_git(root, "rev-parse", "HEAD")


def test_git_boundary_ignores_replacement_refs(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    source = repo / "source.txt"
    source.write_text("trusted\n", encoding="utf-8")
    subject = _commit_test_repo(repo, "trusted subject")
    trusted_blob = _test_git(repo, "rev-parse", f"{subject}:source.txt")
    source.write_text("replacement\n", encoding="utf-8")
    replacement = _commit_test_repo(repo, "replacement subject")
    _test_git(repo, "replace", subject, replacement)

    # Act
    observed = _run_git_v1(
        repo,
        ("ls-tree", "-z", subject, "--", "source.txt"),
        max_stdout_bytes=256,
    ).stdout

    # Assert
    assert trusted_blob.encode("ascii") in observed


def test_git_boundary_forbids_helper_sensitive_status(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    (repo / "tracked.txt").write_text("value\n", encoding="utf-8")
    _commit_test_repo(repo, "subject")
    marker = tmp_path / "fsmonitor-ran"
    monitor = tmp_path / "fsmonitor.sh"
    monitor.write_text(
        f"#!/bin/sh\nprintf invoked > '{marker}'\nprintf '\\n'\n",
        encoding="utf-8",
    )
    monitor.chmod(0o700)
    _test_git(repo, "config", "core.fsmonitor", str(monitor))

    # Act
    _reject_code(
        lambda: _run_git_v1(
            repo,
            ("status", "--porcelain=v1"),
            max_stdout_bytes=1024,
        ),
        "GIT_COMMAND_FAILED",
    )
    assert not marker.exists()


def test_git_boundary_rejects_commands_outside_closed_read_only_set(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")

    # Act and Assert
    _reject_code(
        lambda: _run_git_v1(
            repo,
            ("reset", "--hard"),
            max_stdout_bytes=1024,
        ),
        "GIT_COMMAND_FAILED",
    )


def test_raw_worktree_verifier_uses_supplied_root_not_core_worktree_decoy(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    decoy = tmp_path / "decoy"
    repo.mkdir()
    decoy.mkdir()
    _test_git(repo, "init", "-q")
    (repo / "tracked.txt").write_text("value\n", encoding="utf-8")
    _commit_test_repo(repo, "subject")
    (decoy / "tracked.txt").write_text("malicious\n", encoding="utf-8")
    _test_git(repo, "config", "core.worktree", str(decoy))

    # Act
    head = _test_git(repo, "rev-parse", "HEAD")
    entries = builder_module._complete_tree_entries_v1(repo, head, None)

    # Assert
    builder_module._verify_raw_worktree_v1(repo, entries, frozenset())


@pytest.mark.parametrize("index_flag", ("--skip-worktree", "--assume-unchanged"))
def test_raw_worktree_verifier_detects_bytes_despite_hidden_index_flags(
    tmp_path: Path,
    index_flag: str,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    (repo / "tracked.txt").write_text("value\n", encoding="utf-8")
    head = _commit_test_repo(repo, "subject")
    _test_git(repo, "update-index", index_flag, "tracked.txt")
    (repo / "tracked.txt").write_text("malicious\n", encoding="utf-8")
    entries = builder_module._complete_tree_entries_v1(repo, head, None)

    # Act and Assert
    _reject_code(
        lambda: builder_module._verify_raw_worktree_v1(repo, entries, frozenset()),
        "EVALUATOR_RAW_FILE_MISMATCH",
    )


def test_raw_worktree_verifier_detects_mode_despite_core_filemode(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    tracked = repo / "tracked.txt"
    tracked.write_text("value\n", encoding="utf-8")
    head = _commit_test_repo(repo, "subject")
    tracked.chmod(0o755)
    _test_git(repo, "config", "core.fileMode", "false")
    entries = builder_module._complete_tree_entries_v1(repo, head, None)

    # Act and Assert
    _reject_code(
        lambda: builder_module._verify_raw_worktree_v1(repo, entries, frozenset()),
        "EVALUATOR_TRACKED_BLOB_MISMATCH",
    )


@pytest.mark.parametrize("non_git_executable_mode", (0o410, 0o401))
def test_raw_worktree_verifier_rejects_group_or_other_only_execute_bits(
    tmp_path: Path,
    non_git_executable_mode: int,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    tracked = repo / "tracked.sh"
    tracked.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    tracked.chmod(0o700)
    head = _commit_test_repo(repo, "executable subject")
    tracked.chmod(non_git_executable_mode)
    entries = builder_module._complete_tree_entries_v1(repo, head, None)

    # Act and Assert
    _reject_code(
        lambda: builder_module._verify_raw_worktree_v1(repo, entries, frozenset()),
        "EVALUATOR_TRACKED_BLOB_MISMATCH",
    )


def test_raw_worktree_verifier_neither_executes_nor_trusts_clean_filter(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    tracked = repo / "tracked.txt"
    tracked.write_text("trusted\n", encoding="utf-8")
    head = _commit_test_repo(repo, "subject")
    marker = tmp_path / "clean-filter-ran"
    clean_filter = tmp_path / "clean-filter.sh"
    clean_filter.write_text(
        f"#!/bin/sh\nprintf invoked > {shlex.quote(str(marker))}\nprintf 'trusted\\n'\n",
        encoding="utf-8",
    )
    clean_filter.chmod(0o700)
    (repo / ".git/info/attributes").write_text("tracked.txt filter=hostile\n", encoding="utf-8")
    _test_git(repo, "config", "filter.hostile.clean", str(clean_filter))
    tracked.write_text("malicious\n", encoding="utf-8")
    _test_git(repo, "add", "tracked.txt")
    assert marker.exists()
    marker.unlink()
    entries = builder_module._complete_tree_entries_v1(repo, head, None)

    # Act and Assert
    _reject_code(
        lambda: builder_module._verify_raw_worktree_v1(repo, entries, frozenset()),
        "EVALUATOR_RAW_FILE_MISMATCH",
    )
    assert not marker.exists()


def test_git_name_status_parser_uses_nul_separated_status_path_pairs() -> None:
    # Arrange
    raw = b"A\0tools/evidence.py\0M\0tests/evidence.py\0"

    # Act
    rows = builder_module._parse_git_name_status_v1(raw)

    # Assert
    assert rows == (("A", "tools/evidence.py"), ("M", "tests/evidence.py"))


@pytest.mark.parametrize(
    "raw",
    (
        b"A\0tools/evidence.py",
        b"A\0",
        b"R100\0old.py\0new.py\0",
    ),
)
def test_git_name_status_parser_rejects_malformed_or_ambiguous_rows(raw: bytes) -> None:
    _reject_code(
        lambda: builder_module._parse_git_name_status_v1(raw),
        "EVALUATOR_DIFF_MALFORMED",
    )


def test_git_timeout_kills_descendant_process_group(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    marker = tmp_path / "escaped-descendant"
    hostile_git = tmp_path / "hostile-git.sh"
    hostile_git.write_text(
        "#!/bin/sh\n"
        f"(sleep 0.8; printf escaped > {shlex.quote(str(marker))}) &\n"
        "sleep 60\n",
        encoding="utf-8",
    )
    hostile_git.chmod(0o700)
    monkeypatch.setattr(builder_module, "_git_binary_v1", lambda: str(hostile_git))
    monkeypatch.setattr(builder_module, "GIT_COMMAND_TIMEOUT_SECONDS_V1", 0.2)

    # Act and Assert
    _reject_code(
        lambda: builder_module._run_git_v1(
            tmp_path,
            ("rev-parse", "HEAD"),
            max_stdout_bytes=128,
        ),
        "GIT_COMMAND_TIMEOUT",
    )
    time.sleep(1.0)
    assert not marker.exists()


def test_git_timeout_includes_nonreading_stdin(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    hostile_git = tmp_path / "hostile-git.sh"
    hostile_git.write_text("#!/bin/sh\nsleep 60\n", encoding="utf-8")
    hostile_git.chmod(0o700)
    monkeypatch.setattr(builder_module, "_git_binary_v1", lambda: str(hostile_git))
    monkeypatch.setattr(builder_module, "GIT_COMMAND_TIMEOUT_SECONDS_V1", 0.2)
    started = time.monotonic()

    # Act and Assert
    _reject_code(
        lambda: builder_module._run_git_v1(
            tmp_path,
            ("cat-file", "--batch"),
            max_stdout_bytes=128,
            stdin_bytes=b"x" * (1024 * 1024),
        ),
        "GIT_COMMAND_TIMEOUT",
    )
    assert time.monotonic() - started < 1.0


def test_git_command_budget_rejects_command_above_declared_max(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _test_git(repo, "init", "-q")
    (repo / "tracked.txt").write_text("value\n", encoding="utf-8")
    _commit_test_repo(repo, "subject")
    budget = builder_module.GitCommandBudgetV1(limit=1)
    builder_module._run_git_v1(
        repo,
        ("rev-parse", "HEAD"),
        max_stdout_bytes=128,
        budget=budget,
    )

    # Act and Assert
    _reject_code(
        lambda: builder_module._run_git_v1(
            repo,
            ("rev-parse", "HEAD"),
            max_stdout_bytes=128,
            budget=budget,
        ),
        "GIT_COMMAND_BUDGET_EXCEEDED",
    )
    assert budget.used == 1


def test_parent_commit_scope_matches_fixed_independent_oracle(
    replay_snapshot: ReplaySnapshot,
) -> None:
    artifact = replay_snapshot.artifact
    subject = _object(artifact["inventory_subject"])
    summary = _object(artifact["scope_summary"])

    assert subject == {
        "evaluator_head_requirement": "DESCENDANT_OR_EQUAL_TO_PARENT",
        "git_parent_commit": PARENT_COMMIT_V1,
        "git_parent_tree": PARENT_TREE_V1,
        "model": "PARENT_COMMIT_STATIC_TREE_DESCENDANT_EVALUATOR_V1",
        "source_origin": "GIT_BLOBS_AT_PARENT_COMMIT",
    }
    assert summary == {
        "class_file_counts": EXPECTED_CLASS_COUNTS,
        "dependency_file_count": 91,
        "scanned_file_count": 3731,
        "semantic_work_units": 6_414_792,
        "source_file_count": 3731,
        "total_source_bytes": 61_785_763,
    }
    assert artifact["source_scope_root"] == EXPECTED_SOURCE_SCOPE_ROOT
    parent_paths = set(
        subprocess.run(
            ["git", "-C", str(REPO_ROOT), "ls-tree", "-r", "--name-only", PARENT_COMMIT_V1],
            check=True,
            capture_output=True,
            timeout=10,
        ).stdout.decode().splitlines()
    )
    assert CANDIDATE_PATHS.isdisjoint(parent_paths)


def test_exact_artifact_replays_with_zero_authority(
    replay_snapshot: ReplaySnapshot,
) -> None:
    artifact = validate_inventory_bytes_v1(replay_snapshot.raw, root=REPO_ROOT)

    assert artifact == replay_snapshot.artifact
    assert sha256_prefixed_v1(replay_snapshot.raw) == EXPECTED_ARTIFACT_SHA256_V1
    assert artifact["candidate_fingerprint"] == EXPECTED_CANDIDATE_FINGERPRINT_V1
    assert artifact["authority"] == {
        "production": "NONE",
        "release": "NONE",
        "settlement": "NONE",
        "value_movement": "NONE",
    }
    assert artifact["vm_gates_closed"] == []
    assert "NO_DYNAMIC_REACHABILITY_PROOF" in _list(artifact["nonclaims"])
    assert "NO_STATIC_GRAMMAR_COMPLETENESS_PROOF" in _list(artifact["nonclaims"])
    assert "NO_DEPENDENCY_INVENTORY_COMPLETENESS_PROOF" in _list(artifact["nonclaims"])
    assert "NO_OPERATION_DERIVED_DEPENDENCY_COMPLETENESS_PROOF" in _list(
        artifact["nonclaims"]
    )
    assert "NO_GIT_EXECUTABLE_INTEGRITY_PROOF" in _list(artifact["nonclaims"])
    assert "NO_SELF_BOOTSTRAP_INTEGRITY_PROOF" in _list(artifact["nonclaims"])
    assert "NO_HOST_RUNTIME_INTEGRITY_PROOF" in _list(artifact["nonclaims"])
    assert "NO_ESCAPE_RESISTANT_PROCESS_CONTAINMENT" in _list(artifact["nonclaims"])
    assert _object(artifact["route_static_guard_evidence"])["dynamic_reachability"] == (
        "NOT_PROVEN"
    )


def test_checker_reports_only_bounded_static_non_authority() -> None:
    report = checker_module.check_retired_tau_bridge_inventory_v1(REPO_ROOT)

    assert report == {
        "artifact_sha256": EXPECTED_ARTIFACT_SHA256_V1,
        "classifications": ["QUARANTINED"],
        "dependency_count": 91,
        "findings": [],
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": "zenodex/retired-tau-bridge-dependency-inventory-check/v1",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


@pytest.mark.parametrize(
    ("field", "replacement", "reject_code"),
    (
        (
            "authority",
            {
                "production": "GRANTED",
                "release": "NONE",
                "settlement": "NONE",
                "value_movement": "NONE",
            },
            "AUTHORITY_PROMOTION_FORBIDDEN",
        ),
        ("status", "PRODUCTION_READY", "STATUS_PROMOTION_FORBIDDEN"),
        ("vm_gates_closed", ["VM-1"], "VM_GATE_PROMOTION_FORBIDDEN"),
    ),
)
def test_authority_promotion_mutants_fail_closed(
    replay_snapshot: ReplaySnapshot,
    field: str,
    replacement: object,
    reject_code: str,
) -> None:
    mutant = copy.deepcopy(replay_snapshot.artifact)
    mutant[field] = replacement

    _reject_code(
        lambda: validate_inventory_object_v1(mutant, expected=replay_snapshot.expected),
        reject_code,
    )


def test_dependency_reclassification_and_duplication_mutants_fail_closed(
    replay_snapshot: ReplaySnapshot,
) -> None:
    reclassified = copy.deepcopy(replay_snapshot.artifact)
    rows = _list(reclassified["dependencies"])
    first = _object(rows[0])
    first["classification"] = "REMOVED"
    _reject_code(
        lambda: validate_inventory_object_v1(
            reclassified,
            expected=replay_snapshot.expected,
        ),
        "SUBJECT_REPLAY_MISMATCH",
    )

    duplicated = copy.deepcopy(replay_snapshot.artifact)
    duplicated_rows = _list(duplicated["dependencies"])
    duplicated_rows.append(copy.deepcopy(duplicated_rows[0]))
    _reject_code(
        lambda: validate_inventory_object_v1(
            duplicated,
            expected=replay_snapshot.expected,
        ),
        "DEPENDENCY_ORDER_OR_DUPLICATE",
    )


def test_noncanonical_duplicate_key_and_malformed_artifacts_fail_closed(
    replay_snapshot: ReplaySnapshot,
) -> None:
    noncanonical = json.dumps(replay_snapshot.artifact, sort_keys=True).encode("utf-8")
    _reject_code(
        lambda: validate_inventory_bytes_v1(noncanonical, root=REPO_ROOT),
        "NONCANONICAL_ARTIFACT",
    )
    _reject_code(
        lambda: validate_inventory_bytes_v1(b'{"schema":"a","schema":"b"}\n', root=REPO_ROOT),
        "DUPLICATE_JSON_KEY",
    )
    _reject_code(
        lambda: validate_inventory_bytes_v1(b'{"schema":', root=REPO_ROOT),
        "INVALID_JSON",
    )


def test_named_mutant_api_mount_from_config_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "src/integration/api_server.py"
    mutant[path] = _replace_once(
        mutant[path],
        b"httpd.perps_wallet_api_enabled = False",
        b"httpd.perps_wallet_api_enabled = config.perps_wallet_enabled",
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "MOUNT_NOT_HARD_DISABLED",
    )


def test_named_mutant_startup_guard_after_server_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "src/integration/api_server.py"
    moved = _replace_once(
        mutant[path],
        b"    _ = argv\n    environment_refusals =",
        b"    _ = argv\n    _prewarm_api_modules()\n    environment_refusals =",
    )
    mutant[path] = _replace_once(
        moved,
        b"\n    _prewarm_api_modules()\n    httpd =",
        b"\n    httpd =",
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "STARTUP_GUARD_ORDER_MISMATCH",
    )


def test_named_mutant_startup_guard_empty_mapping_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "src/integration/api_server.py"
    mutant[path] = _replace_once(
        mutant[path],
        b"quarantined_route_environment_rejections_v1(dict(os.environ))",
        b"quarantined_route_environment_rejections_v1({})",
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "STARTUP_ENVIRONMENT_REFUSAL_MISMATCH",
    )


def test_named_mutant_route_path_uses_endswith_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "src/integration/api_server.py"
    mutant[path] = _replace_once(
        mutant[path],
        b'if not path.startswith("/api/perps/wallet/"):\n            return False',
        b'if not path.endswith("/api/perps/wallet/"):\n            return False',
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "ROUTE_PATH_GUARD_MISMATCH",
    )


def test_named_mutant_route_mount_defaults_true_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "src/integration/api_server.py"
    mutant[path] = _replace_once(
        mutant[path],
        b'getattr(self.server, "perps_wallet_api_enabled", False)',
        b'getattr(self.server, "perps_wallet_api_enabled", True)',
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "ROUTE_MOUNT_GUARD_MISMATCH",
    )


def test_named_mutant_local_compose_reenables_route_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "docker-compose.local-testnet.yml"
    mutant[path] = _replace_once(
        mutant[path],
        b'PERPS_WALLET_API_ENABLED: "false"',
        b'PERPS_WALLET_API_ENABLED: "true"',
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "COMPOSE_ROUTE_NOT_DISABLED",
    )


def test_named_mutant_local_manifest_mounts_retired_lane_is_killed(
    closure_sources: Mapping[str, bytes],
) -> None:
    mutant = dict(closure_sources)
    path = "tools/zenoctl_testnet_local/manifest.py"
    mutant[path] = _replace_once(
        mutant[path],
        b'    "CONFIDENTIAL_ATTESTATION_API_ENABLED",\n)',
        b'    "CONFIDENTIAL_ATTESTATION_API_ENABLED",\n'
        b'    "PERPS_WALLET_API_ENABLED",\n)',
    )

    _reject_code(
        lambda: verify_route_static_guards_v1(mutant),
        "LOCAL_MOUNTABLE_LANES_MISMATCH",
    )


def test_named_rust_and_comment_mutants_prove_structural_discovery() -> None:
    rust_signals, _work_units = discover_source_signals_v1(
        "zk/mutant.rs",
        b"use src.integration.perps_wallet_api;\n",
    )
    comment_signals, _work_units = discover_source_signals_v1(
        "src/comment_only.py",
        b"# src.integration.perps_wallet_api\nVALUE = 1\n",
    )
    prose_signals, _work_units = discover_source_signals_v1(
        "src/prose_only.py",
        b'VALUE = "mentions src.integration.perps_wallet_api only as prose"\n',
    )

    assert rust_signals == ("module:src.integration.perps_wallet_api",)
    assert comment_signals == ()
    assert prose_signals == ()


def test_extended_bounded_source_universe_includes_launchers_and_configs() -> None:
    assert "LAUNCHER_MANIFEST_CONFIG" in scope_classes_v1("bin/zenodex-local-testnet", "100755")
    assert scope_classes_v1("bin/zenodex-local-testnet", "100644") == ()
    assert "TEXT_SOURCE" in scope_classes_v1("bin/zenodex-public-testnet.command", "100755")
    assert "TEXT_SOURCE" in scope_classes_v1("scripts/install_zenodex.ps1", "100644")
    assert "TEXT_SOURCE" in scope_classes_v1(".docker/nginx.conf", "100644")


def test_syntax_aware_signals_cover_imports_rust_globs_and_literal_concatenation() -> None:
    from_import, _ = discover_source_signals_v1(
        "src/mutant.py",
        b"from src.integration import perps_wallet_api as bridge\n",
    )
    rust_import, _ = discover_source_signals_v1(
        "zk/mutant.rs",
        b"use src::integration::perps_wallet_api;\n",
    )
    playwright_route, _ = discover_source_signals_v1(
        "tools/dex-ui/tests/mutant.mjs",
        b"page.route('**/api/perps/wallet/status**', handler);\n",
    )
    python_plus, _ = discover_source_signals_v1(
        "src/mutant.py",
        b'ROUTE = "/api/zusd/" + "monetary/status"\n',
    )
    lexical_plus, _ = discover_source_signals_v1(
        "tools/mutant.mjs",
        b"const route = '/api/zusd/' + 'wallet/status';\n",
    )
    yaml_key, _ = discover_source_signals_v1(
        "docker-compose.mutant.yml",
        b'PERPS_WALLET_API_ENABLED: "false"\n',
    )
    shell_assignment, _ = discover_source_signals_v1(
        "scripts/mutant.sh",
        b"export ZUSD_TAU_WALLET_API_ENABLED=false\n",
    )
    slash_source, _ = discover_source_signals_v1(
        "tools/mutant.json",
        b'{"path":"src/integration/tau_net_client.py"}\n',
    )
    spaced_rust, _ = discover_source_signals_v1(
        "zk/mutant.rs",
        b"use src :: integration :: perps_wallet_api;\n",
    )
    yaml_comment, _ = discover_source_signals_v1(
        "docker-compose.mutant.yml",
        b"# PERPS_WALLET_API_ENABLED: false\nSAFE: true\n",
    )

    assert from_import == ("module:src.integration.perps_wallet_api",)
    assert rust_import == ("module:src.integration.perps_wallet_api",)
    assert playwright_route == ("endpoint:/api/perps/wallet",)
    assert python_plus == ("endpoint:/api/zusd/monetary",)
    assert lexical_plus == ("endpoint:/api/zusd/wallet",)
    assert yaml_key == ("identifier:PERPS_WALLET_API_ENABLED",)
    assert shell_assignment == ("identifier:ZUSD_TAU_WALLET_API_ENABLED",)
    assert slash_source == ("module:src.integration.tau_net_client",)
    assert spaced_rust == ("module:src.integration.perps_wallet_api",)
    assert yaml_comment == ()


def test_parent_operational_reference_oracle_is_present(
    replay_snapshot: ReplaySnapshot,
) -> None:
    dependencies = {
        _object(row)["source_path"]: tuple(_list(_object(row)["signals"]))
        for row in _list(replay_snapshot.artifact["dependencies"])
    }
    expected = {
        "docker-compose.local-testnet.yml": (
            "identifier:PERPS_WALLET_API_ENABLED",
            "identifier:ZUSD_MONETARY_WALLET_API_ENABLED",
            "identifier:ZUSD_TAU_WALLET_API_ENABLED",
        ),
        "tests/integration/test_api_server_json_boundary.py": (
            "identifier:perps_wallet_api_enabled",
        ),
        "tests/integration/test_autogov_live_apply_api.py": (
            "identifier:perps_wallet_api_enabled",
            "identifier:zusd_monetary_wallet_api_enabled",
            "identifier:zusd_tau_wallet_api_enabled",
        ),
        "tests/test_check_current_tau_compatibility_v1.py": (
            "module:src.integration.tau_net_client",
        ),
        "tools/build_current_tau_compatibility_v1.py": (
            "module:src.integration.tau_net_client",
        ),
        "tools/check_dex_live_product_goal.py": (
            "module:src.integration.perps_wallet_api",
            "module:src.integration.zusd_monetary_wallet_api",
        ),
        "tools/current_tau_compatibility_pins_v1.py": (
            "module:src.integration.tau_net_client",
        ),
    }

    assert {path: dependencies.get(path) for path in expected} == expected


def test_globals_main_override_is_a_static_guard_survivor_and_nonclaim(
    closure_sources: Mapping[str, bytes],
    replay_snapshot: ReplaySnapshot,
) -> None:
    survivor = dict(closure_sources)
    survivor["src/integration/api_server.py"] += b'\nglobals()["main"] = lambda _argv=None: 0\n'

    assert verify_route_static_guards_v1(survivor)
    nonclaims = _list(replay_snapshot.artifact["nonclaims"])
    assert "NO_DYNAMIC_ENTRYPOINT_BINDING_PROOF" in nonclaims
    assert "O_003B_NOT_CLOSED" in nonclaims


def test_canonical_encoding_is_stable(replay_snapshot: ReplaySnapshot) -> None:
    assert canonical_json_bytes_v1(replay_snapshot.artifact) == replay_snapshot.raw
