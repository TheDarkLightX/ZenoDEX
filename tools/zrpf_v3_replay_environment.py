"""Minimal subprocess environments for retained ZRPF V3 replay checks."""

from __future__ import annotations

import os
import pwd
import stat
from pathlib import Path

SYSTEM_PATH = "/usr/bin:/bin"


def clean_environment() -> dict[str, str]:
    return {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": SYSTEM_PATH,
        "TZ": "UTC",
    }


def create_private_target(target_directory: Path) -> Path:
    if target_directory.exists() or target_directory.is_symlink():
        raise RuntimeError("target directory must not pre-exist")
    parent = target_directory.parent.resolve(strict=True)
    metadata = parent.lstat()
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != os.getuid()
        or metadata.st_mode & 0o022
    ):
        raise RuntimeError("target parent is not a private owned directory")
    target = parent / target_directory.name
    target.mkdir(mode=0o700)
    created = target.lstat()
    if (
        stat.S_ISLNK(created.st_mode)
        or not stat.S_ISDIR(created.st_mode)
        or created.st_uid != os.getuid()
        or stat.S_IMODE(created.st_mode) != 0o700
    ):
        raise RuntimeError("target directory creation was not private")
    return target


def build_environment(
    tool_paths: dict[str, Path],
    target_directory: Path,
) -> dict[str, str]:
    cargo_home = target_directory / "cargo-home"
    isolated_home = target_directory / "home"
    temporary = target_directory / "tmp"
    for directory in (cargo_home, isolated_home, temporary):
        directory.mkdir()
    _link_cargo_sources(cargo_home)

    env = clean_environment()
    env.update(
        {
            "CARGO_HOME": str(cargo_home),
            "CARGO_ENCODED_RUSTFLAGS": "\x1f".join(
                (
                    "--remap-path-prefix",
                    f"{target_directory}=/zrpf/build",
                )
            ),
            "CARGO_NET_OFFLINE": "true",
            "CARGO_TARGET_DIR": str(target_directory),
            "HOME": str(isolated_home),
            "PATH": SYSTEM_PATH,
            "RISC0_SKIP_BUILD": "1",
            "RUSTC": str(tool_paths["rustc"]),
            "RUSTDOC": str(tool_paths["rustdoc"]),
            "SOURCE_DATE_EPOCH": "1783641600",
            "TMPDIR": str(temporary),
        }
    )
    return env


def validate_cargo_config_ancestors(workspace: Path) -> None:
    allowed = workspace / ".cargo/config.toml"
    cursor = workspace
    while True:
        for name in ("config", "config.toml"):
            candidate = cursor / ".cargo" / name
            if (candidate.exists() or candidate.is_symlink()) and candidate != allowed:
                raise RuntimeError("unpinned Cargo config is reachable from snapshot")
        if cursor.parent == cursor:
            break
        cursor = cursor.parent


def _link_cargo_sources(cargo_home: Path) -> None:
    account_home = Path(pwd.getpwuid(os.getuid()).pw_dir)
    source_home = account_home / ".cargo"
    for name in ("registry", "git"):
        source = source_home / name
        if not source.exists():
            continue
        metadata = source.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
            raise RuntimeError(f"Cargo source cache is not a real directory: {name}")
        (cargo_home / name).symlink_to(source, target_is_directory=True)
