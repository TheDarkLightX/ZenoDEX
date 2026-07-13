from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import os
import sys
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_risc0_recursive_toolchain_lock",
    ROOT / "tools/check_risc0_recursive_toolchain_lock.py",
)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)

Runner = Callable[
    [Sequence[str], Mapping[str, str], tuple[int, ...]], Any
]


def test_committed_recursive_toolchain_lock_policy_passes() -> None:
    report = checker.check_risc0_recursive_toolchain_lock()

    assert report["ok"], report["errors"]
    assert report["mode"] == "manifest"
    assert report["claim"] == "manifest_policy_valid"
    assert report["sdk_version"] == "3.0.5"
    assert report["guest_rust_release"] == "r0.1.94.1"
    assert report["artifact_count"] == 6
    assert report["crate_count"] == 4
    assert report["non_claims"] == [
        "reproducible_build",
        "production_readiness",
        "settlement_authorization",
    ]


def test_committed_lock_contains_no_machine_specific_paths() -> None:
    manifest = checker.load_lock_manifest()
    encoded = json.dumps(manifest, sort_keys=True)

    assert "/home/" not in encoded
    assert "/Users/" not in encoded
    assert "C:\\" not in encoded
    for artifact in manifest["installed_artifacts"]:
        path = artifact["relative_path"]
        assert not Path(path).is_absolute()
        assert ".." not in Path(path).parts


@pytest.mark.parametrize(
    ("mutation", "expected_error"),
    [
        (
            lambda value: value["claims"].__setitem__("production_ready", True),
            "claims policy mismatch",
        ),
        (
            lambda value: value["security_policy"].__setitem__(
                "required_sdk_version", "1.2.6"
            ),
            "security policy mismatch",
        ),
        (
            lambda value: value["installed_artifacts"][0].__setitem__(
                "sha256", "0" * 64
            ),
            "canonical lock policy digest mismatch",
        ),
        (
            lambda value: value["installed_artifacts"][0].__setitem__(
                "relative_path", "/tmp/cargo-risczero"
            ),
            "path must not be absolute or traverse parents",
        ),
        (
            lambda value: value.__setitem__("unexpected", True),
            "canonical lock policy digest mismatch",
        ),
    ],
)
def test_manifest_mutations_fail_closed(
    mutation: Callable[[dict[str, Any]], None], expected_error: str
) -> None:
    manifest = copy.deepcopy(checker.load_lock_manifest())
    mutation(manifest)

    report = checker.validate_lock_manifest(manifest)

    assert not report["ok"]
    assert report["claim"] == "none"
    assert any(expected_error in error for error in report["errors"])


def test_lock_loader_rejects_duplicate_json_keys(tmp_path: Path) -> None:
    path = tmp_path / "lock.json"
    path.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    with pytest.raises(checker.LockError, match="duplicate JSON key: schema"):
        checker.load_lock_manifest(path)


def test_installed_mode_requires_explicit_risc0_home() -> None:
    report = checker.check_risc0_recursive_toolchain_lock(
        verify_installed=True,
        risc0_home=None,
    )

    assert not report["ok"]
    assert report["mode"] == "installed"
    assert report["claim"] == "none"
    assert report["errors"] == ["RISC0_HOME is required with --verify-installed"]


def test_hermetic_installed_toolchain_fixture_passes(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
) -> None:
    manifest, risc0_home, rustup_path, runner = installed_fixture

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=runner,
        rustup_path=rustup_path,
    )

    assert report["errors"] == []
    assert report["settings_verified"] is True
    assert report["verified_artifacts"] == list(checker.EXPECTED_ARTIFACT_IDS)
    assert report["rustup_aliases_verified"] == ["rustc", "cargo"]


def test_installed_verifier_rejects_symlink_artifact(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
    tmp_path: Path,
) -> None:
    manifest, risc0_home, rustup_path, runner = installed_fixture
    artifact = _artifact(manifest, "guest-libcore")
    artifact_path = risc0_home / artifact["relative_path"]
    target = tmp_path / "substituted-libcore.rlib"
    target.write_bytes(b"guest-libcore\n")
    artifact_path.unlink()
    artifact_path.symlink_to(target)

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=runner,
        rustup_path=rustup_path,
    )

    assert any("guest-libcore" in error and "symbolic link" in error for error in report["errors"])
    assert "guest-libcore" not in report["verified_artifacts"]


def test_installed_verifier_rejects_non_regular_artifact(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
) -> None:
    manifest, risc0_home, rustup_path, runner = installed_fixture
    artifact = _artifact(manifest, "guest-libcore")
    artifact_path = risc0_home / artifact["relative_path"]
    artifact_path.unlink()
    artifact_path.mkdir()

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=runner,
        rustup_path=rustup_path,
    )

    assert any("guest-libcore" in error and "not a regular file" in error for error in report["errors"])
    assert "guest-libcore" not in report["verified_artifacts"]


def test_installed_verifier_rejects_oversized_artifact(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
) -> None:
    manifest, risc0_home, rustup_path, runner = installed_fixture
    artifact = _artifact(manifest, "guest-libcore")
    artifact["max_size_bytes"] = 1

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=runner,
        rustup_path=rustup_path,
    )

    assert any("guest-libcore" in error and "maximum size" in error for error in report["errors"])


def test_installed_verifier_rejects_hash_mismatch(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
) -> None:
    manifest, risc0_home, rustup_path, runner = installed_fixture
    artifact = _artifact(manifest, "guest-libcore")
    artifact_path = risc0_home / artifact["relative_path"]
    artifact_path.write_bytes(b"altered-libcore\n")
    artifact["size_bytes"] = artifact_path.stat().st_size

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=runner,
        rustup_path=rustup_path,
    )

    assert any("guest-libcore" in error and "sha256 mismatch" in error for error in report["errors"])


def test_installed_verifier_requires_exact_rzup_defaults(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
) -> None:
    manifest, risc0_home, rustup_path, runner = installed_fixture
    (risc0_home / "settings.toml").write_text(
        '[default_versions]\nrust = "1.94.1"\ncargo-risczero = "3.0.5"\n',
        encoding="utf-8",
    )

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=runner,
        rustup_path=rustup_path,
    )

    assert "rzup_settings: settings.toml defaults mismatch" in report["errors"]
    assert report["settings_verified"] is False


def test_installed_verifier_rejects_sanitized_version_drift(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
) -> None:
    manifest, risc0_home, rustup_path, base_runner = installed_fixture

    def drifting_runner(
        argv: Sequence[str], env: Mapping[str, str], pass_fds: tuple[int, ...]
    ) -> Any:
        if pass_fds and os.pread(pass_fds[0], 64, 0) == b"r0vm\n":
            return checker.CommandResult(0, b"risc0-r0vm 3.0.6\n", b"")
        return base_runner(argv, env, pass_fds)

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=drifting_runner,
        rustup_path=rustup_path,
    )

    assert any("r0vm" in error and "version output mismatch" in error for error in report["errors"])
    assert "r0vm" not in report["verified_artifacts"]


def test_installed_verifier_rejects_rustup_alias_outside_pin(
    installed_fixture: tuple[dict[str, Any], Path, Path, Runner],
    tmp_path: Path,
) -> None:
    manifest, risc0_home, rustup_path, base_runner = installed_fixture
    outside = tmp_path / "outside-rustc"
    outside.write_bytes(b"outside\n")

    def diverted_runner(
        argv: Sequence[str], env: Mapping[str, str], pass_fds: tuple[int, ...]
    ) -> Any:
        if not pass_fds and argv[-2:] == ["which", "rustc"]:
            return checker.CommandResult(0, f"{outside}\n".encode("ascii"), b"")
        return base_runner(argv, env, pass_fds)

    report = checker._verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=diverted_runner,
        rustup_path=rustup_path,
    )

    assert any("rustup" in error and "outside the pinned toolchain" in error for error in report["errors"])
    assert report["rustup_aliases_verified"] == []


@pytest.fixture
def installed_fixture(tmp_path: Path) -> tuple[dict[str, Any], Path, Path, Runner]:
    manifest = copy.deepcopy(checker.load_lock_manifest())
    risc0_home = tmp_path / "risc0-home"
    risc0_home.mkdir()
    (risc0_home / "settings.toml").write_text(
        "[default_versions]\n"
        'cpp = "2024.1.5"\n'
        'rust = "1.94.1"\n'
        'cargo-risczero = "3.0.5"\n'
        'r0vm = "3.0.5"\n',
        encoding="utf-8",
    )

    for artifact in manifest["installed_artifacts"]:
        artifact_id = artifact["id"]
        content = f"{artifact_id}\n".encode("ascii")
        path = risc0_home / artifact["relative_path"]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        if artifact["executable"]:
            path.chmod(0o755)
        artifact["sha256"] = hashlib.sha256(content).hexdigest()
        artifact["size_bytes"] = len(content)
        artifact["max_size_bytes"] = max(64, len(content))

    rustup_path = tmp_path / "rustup"
    rustup_path.write_bytes(b"fixture rustup\n")
    rustup_path.chmod(0o755)

    version_outputs = {
        "cargo-risczero": b"cargo-risczero 3.0.5\n",
        "r0vm": b"risc0-r0vm 3.0.5\n",
        "rustc": (
            b"rustc 1.94.1-dev (06e01cb0d 2026-04-09)\n"
            b"binary: rustc\n"
            b"commit-hash: 06e01cb0d0077cdbda6b930b2f23c2f05c8a2421\n"
            b"commit-date: 2026-04-09\n"
            b"host: x86_64-unknown-linux-gnu\n"
            b"release: 1.94.1-dev\n"
            b"LLVM version: 21.1.8\n"
        ),
        "rustdoc": b"rustdoc 1.94.1-dev (06e01cb0d 2026-04-09)\n",
        "cargo": (
            b"cargo 1.94.1-dev (29ea6fb6a 2026-03-24)\n"
            b"release: 1.94.1-dev\n"
            b"commit-hash: 29ea6fb6a5db279426f4cc4e17aa385f05a0cfbc\n"
            b"commit-date: 2026-03-24\n"
            b"host: x86_64-unknown-linux-gnu\n"
            b"os: fixture\n"
        ),
    }

    def runner(
        argv: Sequence[str], env: Mapping[str, str], pass_fds: tuple[int, ...]
    ) -> Any:
        assert set(env) <= {"HOME", "LANG", "LC_ALL", "PATH", "RUSTUP_HOME", "TZ"}
        if pass_fds:
            artifact_id = os.pread(pass_fds[0], 64, 0).decode("ascii").strip()
            return checker.CommandResult(0, version_outputs[artifact_id], b"")
        artifact_id = argv[-1]
        artifact = _artifact(manifest, artifact_id)
        resolved = risc0_home / artifact["relative_path"]
        return checker.CommandResult(0, f"{resolved}\n".encode("ascii"), b"")

    return manifest, risc0_home, rustup_path, runner


def _artifact(manifest: dict[str, Any], artifact_id: str) -> dict[str, Any]:
    return next(
        artifact
        for artifact in manifest["installed_artifacts"]
        if artifact["id"] == artifact_id
    )
