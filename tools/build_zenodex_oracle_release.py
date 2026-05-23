#!/usr/bin/env python3
"""Build a deterministic pre-MVP ZenoOracle reporter/validator bundle."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
CLI = REPO_ROOT / "tools" / "zenodex_oracle.py"
WRAPPER = REPO_ROOT / "tools" / "zenodex-oracle"
BRANDING_DIR = REPO_ROOT / "assets" / "branding" / "zeno-oracle"
DEFAULT_OUT_DIR = REPO_ROOT / "dist"

BRANDING_FILES = (
    "zeno_oracle_favicon.ico",
    "zeno_oracle_full_transparent_1024.png",
    "zeno_oracle_icon_256.png",
    "zeno_oracle_icon_512.png",
    "zeno_oracle_icon_embedded.svg",
)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _read_cli_version() -> str:
    match = re.search(r'^CLI_VERSION\s*=\s*"([^"]+)"', CLI.read_text(encoding="utf-8"), re.M)
    if match is None:
        raise RuntimeError("could not read CLI_VERSION from tools/zenodex_oracle.py")
    return match.group(1)


def _git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "--short=12", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except Exception:
        return "unknown"


def _copy_file(src: Path, dst: Path, *, executable: bool = False) -> None:
    if not src.is_file():
        raise FileNotFoundError(src)
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    if executable:
        mode = dst.stat().st_mode
        dst.chmod(mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def _copy_tree(src: Path, dst: Path) -> None:
    if not src.is_dir():
        raise FileNotFoundError(src)
    ignore = shutil.ignore_patterns("__pycache__", "*.pyc")
    shutil.copytree(src, dst, ignore=ignore)


def _manifest_files(bundle_dir: Path) -> list[dict[str, Any]]:
    files: list[dict[str, Any]] = []
    for path in sorted(bundle_dir.rglob("*")):
        if not path.is_file() or path.name == "manifest.json":
            continue
        rel = path.relative_to(bundle_dir).as_posix()
        files.append(
            {
                "path": rel,
                "sha256": _sha256_file(path),
                "size_bytes": path.stat().st_size,
                "executable": bool(path.stat().st_mode & stat.S_IXUSR),
            }
        )
    return files


def _write_readme(bundle_dir: Path, *, native_binary: bool = False) -> None:
    entrypoint = "./bin/zenodex-oracle" if native_binary else "./zenodex-oracle"
    (bundle_dir / "README.md").write_text(
        "\n".join(
            [
                "# ZenoOracle Reporter/Validator Bundle",
                "",
                "This is a pre-MVP local reporter/validator bundle. It is not production authority.",
                "",
                "Run:",
                "",
                "```bash",
                f"{entrypoint} --json version",
                f"{entrypoint} init --home ./oracle-home",
                f"{entrypoint} verify local-state --home ./oracle-home",
                "```",
                "",
                "Branding assets are included under `assets/branding/zeno-oracle/`.",
                "The bundle manifest pins file hashes and the official icon paths.",
                "",
            ]
        ),
        encoding="utf-8",
    )


def _write_root_launcher(bundle_dir: Path) -> None:
    launcher = bundle_dir / "zenodex-oracle"
    launcher.write_text(
        "\n".join(
            [
                "#!/usr/bin/env bash",
                "set -euo pipefail",
                'SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"',
                'exec python3 "$SCRIPT_DIR/tools/zenodex_oracle.py" "$@"',
                "",
            ]
        ),
        encoding="utf-8",
    )
    launcher.chmod(launcher.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def _pyinstaller_command() -> list[str]:
    if importlib.util.find_spec("PyInstaller") is not None:
        return [sys.executable, "-m", "PyInstaller"]
    binary = shutil.which("pyinstaller")
    if binary:
        return [binary]
    raise RuntimeError("PyInstaller is required for --native-binary; install pyinstaller or build the default Python-local bundle")


def _build_native_binary(*, bundle_dir: Path, work_dir: Path) -> Path:
    icon = BRANDING_DIR / "zeno_oracle_favicon.ico"
    binary_dir = bundle_dir / "bin"
    binary_dir.mkdir(parents=True, exist_ok=True)
    work_dir.mkdir(parents=True, exist_ok=True)
    command = [
        *_pyinstaller_command(),
        "--clean",
        "--noconfirm",
        "--onefile",
        "--name",
        "zenodex-oracle",
        "--distpath",
        str(binary_dir),
        "--workpath",
        str(work_dir / "build"),
        "--specpath",
        str(work_dir / "spec"),
        "--add-data",
        f"{REPO_ROOT / 'assets'}{os.pathsep}assets",
        "--hidden-import",
        "tools.check_oracle_authorization_semantic_binding",
    ]
    if icon.is_file():
        command.extend(["--icon", str(icon)])
    command.append(str(CLI))
    subprocess.run(command, cwd=REPO_ROOT, check=True)
    executable = binary_dir / ("zenodex-oracle.exe" if sys.platform == "win32" else "zenodex-oracle")
    if not executable.is_file():
        raise RuntimeError(f"PyInstaller did not produce expected executable: {executable}")
    executable.chmod(executable.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return executable


def build_bundle(
    *,
    out_dir: Path,
    bundle_name: str | None = None,
    force: bool = False,
    zip_bundle: bool = False,
    native_binary: bool = False,
    pyinstaller_work_dir: Path | None = None,
) -> dict[str, Any]:
    version = _read_cli_version()
    target_name = "native" if native_binary else "python-local"
    name = bundle_name or f"zenodex-oracle-{version}-{target_name}"
    bundle_dir = out_dir / name
    if bundle_dir.exists():
        if not force:
            raise FileExistsError(f"{bundle_dir} already exists; pass --force to overwrite")
        shutil.rmtree(bundle_dir)
    bundle_dir.mkdir(parents=True)

    _write_root_launcher(bundle_dir)
    _copy_file(CLI, bundle_dir / "tools" / "zenodex_oracle.py", executable=True)
    _copy_file(WRAPPER, bundle_dir / "tools" / "zenodex-oracle", executable=True)
    _copy_file(REPO_ROOT / "tools" / "operator_report_output.py", bundle_dir / "tools" / "operator_report_output.py")
    _copy_tree(REPO_ROOT / "src", bundle_dir / "src")
    for filename in BRANDING_FILES:
        _copy_file(BRANDING_DIR / filename, bundle_dir / "assets" / "branding" / "zeno-oracle" / filename)
    native_path = None
    if native_binary:
        work_dir = pyinstaller_work_dir or (out_dir / ".pyinstaller-work" / name)
        native_path = _build_native_binary(bundle_dir=bundle_dir, work_dir=work_dir)
    _write_readme(bundle_dir, native_binary=native_binary)

    not_claimed = [
        "production_oracle_network",
        "production_oracle_authority",
    ]
    if not native_binary:
        not_claimed.insert(0, "native_binary")

    manifest = {
        "schema": "zenodex.oracle.release_bundle.v1",
        "name": "zenodex-oracle",
        "version": version,
        "git_commit": _git_commit(),
        "build_target": "native-binary-bundle" if native_binary else "python-local-bundle",
        "bundle_dir": str(bundle_dir),
        "entrypoint": "bin/zenodex-oracle" if native_binary else "zenodex-oracle",
        "python_entrypoint": "tools/zenodex_oracle.py",
        "native_binary": None if native_path is None else native_path.relative_to(bundle_dir).as_posix(),
        "official_icon": "assets/branding/zeno-oracle/zeno_oracle_icon_512.png",
        "official_favicon": "assets/branding/zeno-oracle/zeno_oracle_favicon.ico",
        "production_authority": False,
        "not_claimed": not_claimed,
        "files": [],
    }
    manifest["files"] = _manifest_files(bundle_dir)
    manifest_path = bundle_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8")

    archive_path = None
    archive_sha256 = None
    if zip_bundle:
        archive_base = out_dir / name
        archive_path = Path(shutil.make_archive(str(archive_base), "zip", root_dir=out_dir, base_dir=name))
        archive_sha256 = _sha256_file(archive_path)
        manifest["archive"] = str(archive_path)
        manifest["archive_sha256"] = archive_sha256
        manifest_path.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8")

    return {
        "schema": "zenodex.oracle.release_bundle.result.v1",
        "ok": True,
        "bundle_dir": str(bundle_dir),
        "manifest": str(manifest_path),
        "native_binary": None if native_path is None else str(native_path),
        "native_binary_sha256": None if native_path is None else _sha256_file(native_path),
        "archive": None if archive_path is None else str(archive_path),
        "archive_sha256": archive_sha256,
        "production_authority": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="build_zenodex_oracle_release.py")
    parser.add_argument("--out-dir", default=str(DEFAULT_OUT_DIR))
    parser.add_argument("--bundle-name")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--zip", action="store_true", dest="zip_bundle")
    parser.add_argument("--native-binary", action="store_true")
    parser.add_argument("--pyinstaller-work-dir")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    try:
        result = build_bundle(
            out_dir=Path(args.out_dir),
            bundle_name=args.bundle_name,
            force=bool(args.force),
            zip_bundle=bool(args.zip_bundle),
            native_binary=bool(args.native_binary),
            pyinstaller_work_dir=None if args.pyinstaller_work_dir is None else Path(args.pyinstaller_work_dir),
        )
    except Exception as exc:
        if args.json:
            print(
                json.dumps(
                    {
                        "schema": "zenodex.oracle.release_bundle.result.v1",
                        "ok": False,
                        "error": str(exc),
                        "production_authority": False,
                    },
                    sort_keys=True,
                )
            )
        else:
            print(str(exc), file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(result, sort_keys=True))
    else:
        print(f"bundle: {result['bundle_dir']}")
        print(f"manifest: {result['manifest']}")
        if result.get("archive"):
            print(f"archive: {result['archive']}")
            print(f"archive_sha256: {result['archive_sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
