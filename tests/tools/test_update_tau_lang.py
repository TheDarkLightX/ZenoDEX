from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

SCRIPT = Path(__file__).parents[2] / "tools" / "update_tau_lang.sh"


def _run(*args: str, cwd: Path, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args),
        cwd=cwd,
        check=check,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def _git(cwd: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return _run("git", *args, cwd=cwd, check=check)


def _commit(repo: Path, message: str) -> str:
    _git(repo, "add", "--all")
    _git(repo, "commit", "-m", message)
    return _git(repo, "rev-parse", "HEAD").stdout.strip()


def _init_repo(path: Path) -> Path:
    path.mkdir(parents=True)
    _git(path, "init", "-q")
    _git(path, "config", "user.name", "Updater Test")
    _git(path, "config", "user.email", "updater-test@example.invalid")
    return path


@pytest.fixture()
def harness(tmp_path: Path) -> dict[str, Path | str]:
    workspace = _init_repo(tmp_path / "workspace")
    (workspace / "tools").mkdir()
    shutil.copy2(SCRIPT, workspace / "tools" / "update_tau_lang.sh")
    (workspace / "tools" / "update_tau_lang.sh").chmod(0o755)

    parser = _init_repo(tmp_path / "parser")
    (parser / "parser.txt").write_text("parser-v1\n")
    parser_commit = _commit(parser, "parser v1")
    parser_origin = tmp_path / "parser-origin.git"
    _run("git", "clone", "--bare", str(parser), str(parser_origin), cwd=tmp_path)

    source_seed = _init_repo(tmp_path / "source-seed")
    _git(source_seed, "branch", "-M", "main")
    _run(
        "git",
        "-c",
        "protocol.file.allow=always",
        "submodule",
        "add",
        "file://" + str(parser_origin),
        "external/parser",
        cwd=source_seed,
    )
    (source_seed / "VERSION").write_text("0.0.0\n")
    old_commit = _commit(source_seed, "tau v1")
    source_origin = tmp_path / "source-origin.git"
    _run("git", "clone", "--bare", str(source_seed), str(source_origin), cwd=tmp_path)
    _git(source_seed, "remote", "add", "origin", str(source_origin))

    old_workspace_tau = workspace / "external" / "tau-lang"
    old_workspace_tau.parent.mkdir(parents=True)
    _run("git", "clone", str(source_origin), str(old_workspace_tau), cwd=workspace)

    replacement = _init_repo(tmp_path / "replacement")
    _git(replacement, "branch", "-M", "main")
    _run(
        "git",
        "-c",
        "protocol.file.allow=always",
        "submodule",
        "add",
        "file://" + str(parser_origin),
        "external/parser",
        cwd=replacement,
    )
    (replacement / "VERSION").write_text("0.0.1\n")
    new_commit = _commit(replacement, "tau replacement v2")
    _git(source_origin, "fetch", str(replacement), "main")
    _git(source_origin, "update-ref", "refs/heads/main", new_commit, old_commit)

    stubs = workspace / "stubs"
    stubs.mkdir()
    (stubs / "cmake").write_text(
        "#!/usr/bin/env bash\n"
        "set -euo pipefail\n"
        "printf '%s\\n' \"$*\" >> \"${TAU_CMAKE_LOG:?}\"\n"
        'if [[ "$1" == "-S" ]]; then\n'
        '  mkdir -p "$4"\n'
        'elif [[ "$1" == "--build" ]]; then\n'
        '  build="$2"\n'
        '  mkdir -p "$build"\n'
        '  { printf \'#!/usr/bin/env bash\\n\'; printf \'printf \\"Tau Language Framework version 0.0.0 (%s)\\\\n\\" \\"${TAU_STUB_HASH:?}\\"\\n\' "${TAU_STUB_HASH}"; } > "$build/tau"\n'
        '  chmod +x "$build/tau"\n'
        "fi\n"
    )
    (stubs / "cmake").chmod(0o755)

    return {
        "workspace": workspace,
        "tau": old_workspace_tau,
        "old_commit": old_commit,
        "new_commit": new_commit,
        "parser_commit": parser_commit,
        "parser_origin": parser_origin,
        "source_origin": source_origin,
        "stubs": stubs,
        "cmake_log": workspace / "cmake.log",
    }


def _invoke(
    harness: dict[str, Path | str],
    *extra: str,
    stub_hash: str | None = None,
    jobs: str | None = None,
) -> subprocess.CompletedProcess[str]:
    workspace = Path(harness["workspace"])
    env = os.environ.copy()
    env["PATH"] = str(harness["stubs"]) + os.pathsep + env["PATH"]
    env["GIT_ALLOW_PROTOCOL"] = "file"
    env["TAU_STUB_HASH"] = stub_hash or str(harness["new_commit"])[:7]
    env["TAU_CMAKE_LOG"] = str(harness["cmake_log"])
    if jobs is not None:
        env["TAU_BUILD_JOBS"] = jobs
    return subprocess.run(
        [
            str(workspace / "tools" / "update_tau_lang.sh"),
            "--ref",
            "main",
            "--tau-dir",
            "external/tau-lang",
            "--build-dir",
            "build-test",
            "--expected-origin-url",
            str(harness["source_origin"]),
            "--expected-parser-origin-url",
            "file://" + str(harness["parser_origin"]),
            *extra,
        ],
        cwd=workspace,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def _pins(harness: dict[str, Path | str]) -> tuple[str, str]:
    return str(harness["new_commit"]), str(harness["parser_commit"])


def test_force_pushed_non_ancestral_remote_and_shadowing_local_branch(
    harness: dict[str, Path | str],
) -> None:
    root_pin, parser_pin = _pins(harness)
    result = _invoke(
        harness,
        "--expected-commit",
        root_pin,
        "--expected-parser-commit",
        parser_pin,
    )
    assert result.returncode == 0, result.stderr
    assert _git(Path(harness["tau"]), "rev-parse", "HEAD").stdout.strip() == root_pin
    assert f"source SHA: {root_pin}" in result.stdout
    assert f"parser SHA: {parser_pin}" in result.stdout
    assert "binary SHA-256:" in result.stdout


def test_wrong_expected_root_is_rejected_before_build(harness: dict[str, Path | str]) -> None:
    result = _invoke(harness, "--expected-commit", "0" * 40)
    assert result.returncode != 0
    assert "expected root commit" in result.stderr


def test_local_commit_not_reachable_from_origin_is_rejected(
    harness: dict[str, Path | str],
) -> None:
    tau = Path(harness["tau"])
    _git(tau, "config", "user.name", "Updater Test")
    _git(tau, "config", "user.email", "updater-test@example.invalid")
    (tau / "local-only.txt").write_text("not from origin\n")
    local_only = _commit(tau, "local only")

    result = _invoke(harness, "--ref", local_only, "--expected-commit", local_only)
    assert result.returncode != 0
    assert "not reachable from an origin remote-tracking ref" in result.stderr


def test_wrong_expected_parser_pin_is_rejected(harness: dict[str, Path | str]) -> None:
    root_pin, _ = _pins(harness)
    result = _invoke(
        harness,
        "--expected-commit",
        root_pin,
        "--expected-parser-commit",
        "1" * 40,
    )
    assert result.returncode != 0
    assert "expected parser commit" in result.stderr


def test_dirty_source_checkout_is_rejected(harness: dict[str, Path | str]) -> None:
    tau = Path(harness["tau"])
    (tau / "dirty.txt").write_text("untrusted\n")
    result = _invoke(harness)
    assert result.returncode != 0
    assert "source worktree is dirty" in result.stderr


def test_dirty_parser_checkout_is_rejected(harness: dict[str, Path | str]) -> None:
    tau = Path(harness["tau"])
    _run(
        "git",
        "-c",
        "protocol.file.allow=always",
        "submodule",
        "update",
        "--init",
        "--recursive",
        cwd=tau,
    )
    parser = tau / "external" / "parser"
    (parser / "dirty.txt").write_text("untrusted\n")
    result = _invoke(harness)
    assert result.returncode != 0
    assert "parser worktree is dirty" in result.stderr


def test_stale_binary_version_is_rejected(harness: dict[str, Path | str]) -> None:
    root_pin, parser_pin = _pins(harness)
    result = _invoke(
        harness,
        "--expected-commit",
        root_pin,
        "--expected-parser-commit",
        parser_pin,
        stub_hash=str(harness["old_commit"])[:7],
    )
    assert result.returncode != 0
    assert "does not contain resolved source commit" in result.stderr


def test_expected_commit_arguments_require_full_hex_pins(harness: dict[str, Path | str]) -> None:
    result = _invoke(harness, "--expected-commit", "deadbeef")
    assert result.returncode != 0
    assert "full 40-hex" in result.stderr


@pytest.mark.parametrize(
    ("option", "value", "message"),
    [
        ("--tau-dir", "../../outside", "--tau-dir must resolve inside"),
        ("--build-dir", "../../outside", "--build-dir must resolve inside"),
    ],
)
def test_paths_cannot_escape_the_workspace_or_tau_checkout(
    harness: dict[str, Path | str],
    option: str,
    value: str,
    message: str,
) -> None:
    result = _invoke(harness, option, value)
    assert result.returncode != 0
    assert message in result.stderr


def test_tau_dir_symlink_cannot_escape_workspace(harness: dict[str, Path | str]) -> None:
    workspace = Path(harness["workspace"])
    outside = workspace.parent / "outside-tau"
    outside.mkdir()
    escape = workspace / "external" / "escape"
    escape.symlink_to(outside, target_is_directory=True)

    result = _invoke(harness, "--tau-dir", "external/escape")
    assert result.returncode != 0
    assert "--tau-dir must resolve inside" in result.stderr


def test_root_origin_substitution_is_rejected(harness: dict[str, Path | str]) -> None:
    tau = Path(harness["tau"])
    substituted = tau.parent / "substituted-origin.git"
    _run("git", "clone", "--bare", str(tau), str(substituted), cwd=tau.parent)
    _git(tau, "remote", "set-url", "origin", str(substituted))

    result = _invoke(harness)
    assert result.returncode != 0
    assert "Tau origin URL mismatch" in result.stderr


def test_parser_origin_substitution_is_rejected(harness: dict[str, Path | str]) -> None:
    tau = Path(harness["tau"])
    _run(
        "git",
        "-c",
        "protocol.file.allow=always",
        "submodule",
        "update",
        "--init",
        "--recursive",
        cwd=tau,
    )
    parser = tau / "external" / "parser"
    substituted = tau.parent / "substituted-parser.git"
    _run("git", "clone", "--bare", str(parser), str(substituted), cwd=tau.parent)
    _git(parser, "remote", "set-url", "origin", str(substituted))

    result = _invoke(harness)
    assert result.returncode != 0
    assert "parser origin URL mismatch" in result.stderr


def test_build_jobs_are_explicit_and_bounded(harness: dict[str, Path | str]) -> None:
    root_pin, parser_pin = _pins(harness)
    result = _invoke(
        harness,
        "--expected-commit",
        root_pin,
        "--expected-parser-commit",
        parser_pin,
        jobs="3",
    )
    assert result.returncode == 0, result.stderr
    assert "--build" in Path(harness["cmake_log"]).read_text()
    assert "-j 3" in Path(harness["cmake_log"]).read_text()


@pytest.mark.parametrize("jobs", ["0", "-1", "many"])
def test_invalid_build_jobs_fail_closed(
    harness: dict[str, Path | str], jobs: str
) -> None:
    result = _invoke(harness, jobs=jobs)
    assert result.returncode != 0
    assert "TAU_BUILD_JOBS must be a positive integer" in result.stderr
