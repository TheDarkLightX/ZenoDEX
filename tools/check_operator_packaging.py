#!/usr/bin/env python3
"""Check that common operator packaging entrypoints are present and safe."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_docker_hashlocked_install import evaluate_dockerfile  # noqa: E402


REPORT_SCHEMA = "zenodex.operator_packaging_readiness.v0"


REQUIRED_FILES = (
    "bin/zenoctl",
    "scripts/install_zenodex.sh",
    "scripts/install_zenodex.ps1",
    "tools/zenoctl.py",
    "tools/zeno_ledger_node.py",
    "tools/check_zeno_ledger_light_client_checkpoint.py",
    "tools/build_zeno_sdk_browser_bundle.py",
    "tools/dex-ui/src/sdk/zenoProofClient.js",
    "Dockerfile.hashlocked",
    "tools/build_operator_release_bundle.py",
    "Dockerfile.operator-tools",
    "docker-compose.two-node.yml",
    "docker-compose.multimachine.yml",
    ".github/workflows/release-integrity.yml",
    "docs/DEPLOYMENT_QUICKSTART.md",
    "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
)


def check_operator_packaging(root: Path = ROOT) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    errors: list[str] = []

    for relpath in REQUIRED_FILES:
        path = root / relpath
        ok = path.is_file()
        checks.append({"id": f"file:{relpath}", "ok": ok, "path": str(path)})
        if not ok:
            errors.append(f"missing required packaging file: {relpath}")

    _check_posix_wrapper(root, checks, errors)
    _check_install_script(root, checks, errors)
    _check_powershell_installer(root, checks, errors)
    _check_zenoctl_light_client(root, checks, errors)
    _check_browser_sdk(root, checks, errors)
    _check_release_bundle_builder(root, checks, errors)
    _check_release_integrity_publishes_operator_bundle(root, checks, errors)
    _check_hashlocked_dockerfile(root, "Dockerfile.hashlocked", checks, errors)
    _check_hashlocked_dockerfile(root, "Dockerfile.operator-tools", checks, errors)

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "checks": checks,
        "supported_operator_paths": [
            "docker-compose",
            "hashlocked-dockerfile",
            "posix-wrapper",
            "windows-cmd-wrapper-installer",
            "light-client-checkpoint-verifier",
            "proof-carrying-browser-bundle",
            "browser-wallet-sync-sdk",
            "github-release-assets",
        ],
    }


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _append_check(checks: list[dict[str, Any]], errors: list[str], *, check_id: str, ok: bool, error: str) -> None:
    checks.append({"id": check_id, "ok": ok})
    if not ok:
        errors.append(error)


def _check_posix_wrapper(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "bin" / "zenoctl"
    if not path.is_file():
        return
    text = _read(path)
    _append_check(
        checks,
        errors,
        check_id="bin_zenoctl_delegates_to_tools_zenoctl",
        ok="tools/zenoctl.py" in text and "python3" in text,
        error="bin/zenoctl must delegate to tools/zenoctl.py with python3",
    )
    _append_check(
        checks,
        errors,
        check_id="bin_zenoctl_executable",
        ok=bool(path.stat().st_mode & 0o111),
        error="bin/zenoctl must be executable",
    )


def _check_install_script(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "scripts" / "install_zenodex.sh"
    if not path.is_file():
        return
    text = _read(path)
    for token in ("zenoctl", "zenodex-node", "tools/zenoctl.py", "tools/zeno_ledger_node.py", "--dry-run"):
        _append_check(
            checks,
            errors,
            check_id=f"install_sh_contains:{token}",
            ok=token in text,
            error=f"scripts/install_zenodex.sh must contain {token}",
        )
    _append_check(
        checks,
        errors,
        check_id="install_sh_executable",
        ok=bool(path.stat().st_mode & 0o111),
        error="scripts/install_zenodex.sh must be executable",
    )


def _check_powershell_installer(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "scripts" / "install_zenodex.ps1"
    if not path.is_file():
        return
    text = _read(path)
    for token in ("zenoctl", "zenodex-node", ".cmd", "tools\\zenoctl.py", "tools\\zeno_ledger_node.py"):
        _append_check(
            checks,
            errors,
            check_id=f"install_ps1_contains:{token}",
            ok=token in text,
            error=f"scripts/install_zenodex.ps1 must contain {token}",
        )


def _check_zenoctl_light_client(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "tools" / "zenoctl.py"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "light-client",
        "verify-checkpoint",
        "build-browser-bundle",
        "check_zeno_ledger_light_client_checkpoint.py",
        "build_zeno_sdk_browser_bundle.py",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"zenoctl_light_client_contains:{token}",
            ok=token in text,
            error=f"tools/zenoctl.py must expose {token}",
        )


def _check_browser_sdk(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    builder = root / "tools" / "build_zeno_sdk_browser_bundle.py"
    if builder.is_file():
        text = _read(builder)
        for token in ("build_browser_bundle_from_files", "validate_light_client_checkpoint_v0", "bundle_hash"):
            _append_check(
                checks,
                errors,
                check_id=f"browser_bundle_builder_contains:{token}",
                ok=token in text,
                error=f"tools/build_zeno_sdk_browser_bundle.py must contain {token}",
            )
    sdk = root / "tools" / "dex-ui" / "src" / "sdk" / "zenoProofClient.js"
    if sdk.is_file():
        text = _read(sdk)
        for token in (
            "verifyBrowserCheckpointBundleV0",
            "advanceWalletSyncStateV0",
            "browser_bls_quorum_verified",
            "wallet sync rollback rejected",
        ):
            _append_check(
                checks,
                errors,
                check_id=f"browser_sdk_contains:{token}",
                ok=token in text,
                error=f"tools/dex-ui/src/sdk/zenoProofClient.js must contain {token}",
            )


def _check_release_bundle_builder(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "tools" / "build_operator_release_bundle.py"
    if not path.is_file():
        return
    text = _read(path)
    for token in ("build", "verify", "archive_sha256", "zenodex.operator_release_bundle.v0"):
        _append_check(
            checks,
            errors,
            check_id=f"release_bundle_builder_contains:{token}",
            ok=token in text,
            error=f"tools/build_operator_release_bundle.py must contain {token}",
        )


def _check_release_integrity_publishes_operator_bundle(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / ".github" / "workflows" / "release-integrity.yml"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "contents: write",
        "Build operator release bundle",
        "tools/build_operator_release_bundle.py build",
        "tools/build_operator_release_bundle.py verify",
        "Compute combined SHA256SUMS",
        "Attest operator bundle provenance",
        "Stage GitHub Release assets",
        "Create or update GitHub Release",
        "gh release upload",
        "--clobber",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_integrity_contains:{token}",
            ok=token in text,
            error=f".github/workflows/release-integrity.yml must contain {token}",
        )


def _check_hashlocked_dockerfile(
    root: Path,
    relpath: str,
    checks: list[dict[str, Any]],
    errors: list[str],
) -> None:
    path = root / relpath
    if not path.is_file():
        return
    report = evaluate_dockerfile(path, require_digest=False)
    checks.append({"id": f"docker_hashlocked:{relpath}", "ok": report["ok"], "warnings": report["warnings"]})
    if not report["ok"]:
        errors.append(f"{relpath} is not a hash-locked operator Dockerfile")


def main(argv: list[str] | None = None) -> int:
    root = ROOT
    pretty = False
    args = list(argv if argv is not None else sys.argv[1:])
    while args:
        arg = args.pop(0)
        if arg == "--repo-root":
            if not args:
                print("missing value for --repo-root", file=sys.stderr)
                return 2
            root = Path(args.pop(0))
        elif arg == "--pretty":
            pretty = True
        elif arg in {"-h", "--help"}:
            print("usage: tools/check_operator_packaging.py [--repo-root DIR] [--pretty]")
            return 0
        else:
            print(f"unknown argument: {arg}", file=sys.stderr)
            return 2

    report = check_operator_packaging(root.resolve())
    print(json.dumps(report, indent=2 if pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
