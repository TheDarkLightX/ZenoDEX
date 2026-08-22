from __future__ import annotations

import subprocess
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "update_tau_lang.sh"


def _git(cwd: Path, *args: str) -> str:
    result = subprocess.run(
        ("git", *args),
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _commit_file(repo: Path, name: str, content: str, message: str) -> str:
    (repo / name).write_text(content, encoding="utf-8")
    _git(repo, "add", name)
    _git(repo, "commit", "-m", message)
    return _git(repo, "rev-parse", "HEAD")


def _configure_identity(repo: Path) -> None:
    _git(repo, "config", "user.email", "tau-updater-test@example.invalid")
    _git(repo, "config", "user.name", "Tau Updater Test")


def _make_fixture(tmp_path: Path) -> tuple[Path, Path, Path]:
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    _git(workspace, "init", "-b", "main")
    _configure_identity(workspace)
    _commit_file(workspace, "README.md", "workspace\n", "workspace")

    remote = tmp_path / "tau-origin.git"
    _git(tmp_path, "init", "--bare", "--initial-branch=main", str(remote))
    seed = tmp_path / "tau-seed"
    _git(tmp_path, "clone", str(remote), str(seed))
    _configure_identity(seed)
    _commit_file(seed, "tau.txt", "one\n", "tau one")
    _git(seed, "push", "origin", "main")

    tau_dir = workspace / "external" / "tau-lang"
    tau_dir.parent.mkdir(parents=True)
    _git(tau_dir.parent, "clone", str(remote), str(tau_dir))
    _configure_identity(tau_dir)
    return workspace, seed, tau_dir


def _run_updater(workspace: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        (str(SCRIPT), "--resolve-only"),
        cwd=workspace,
        check=False,
        capture_output=True,
        text=True,
    )


def test_resolve_only_fast_forwards_an_ordinary_upstream_update(tmp_path: Path) -> None:
    workspace, seed, tau_dir = _make_fixture(tmp_path)
    expected = _commit_file(seed, "tau.txt", "two\n", "tau two")
    _git(seed, "push", "origin", "main")

    result = _run_updater(workspace)

    assert result.returncode == 0, result.stderr
    assert _git(tau_dir, "rev-parse", "HEAD") == expected
    assert f"tau-lang git: {expected}" in result.stdout
    assert "resolve-only" in result.stdout


def test_resolve_only_rejects_rewritten_history_without_changing_head(
    tmp_path: Path,
) -> None:
    workspace, _seed, tau_dir = _make_fixture(tmp_path)
    _git(tau_dir, "checkout", "--orphan", "rewritten-main")
    _git(tau_dir, "rm", "-f", "tau.txt")
    local_head = _commit_file(tau_dir, "tau.txt", "local rewrite\n", "local rewrite")
    _git(tau_dir, "branch", "-M", "main")

    result = _run_updater(workspace)

    assert result.returncode == 1
    assert "have no common ancestor" in result.stderr
    assert "use a separate --tau-dir" in result.stderr
    assert _git(tau_dir, "rev-parse", "HEAD") == local_head


def test_resolve_only_rejects_dirty_checkout_without_changing_head(tmp_path: Path) -> None:
    workspace, _seed, tau_dir = _make_fixture(tmp_path)
    original_head = _git(tau_dir, "rev-parse", "HEAD")
    (tau_dir / "tau.txt").write_text("dirty\n", encoding="utf-8")

    result = _run_updater(workspace)

    assert result.returncode == 1
    assert "local tracked or untracked changes" in result.stderr
    assert _git(tau_dir, "rev-parse", "HEAD") == original_head
    assert (tau_dir / "tau.txt").read_text(encoding="utf-8") == "dirty\n"
