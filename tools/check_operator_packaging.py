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
    "bin/zenodex-local-testnet",
    "bin/zenodex-public-testnet",
    "bin/zenodex-public-testnet.command",
    "bin/zenodex-public-follower",
    "scripts/install_zenodex.sh",
    "scripts/install_zenodex.ps1",
    "tools/zenoctl.py",
    "tools/zeno_ledger_node.py",
    "tools/zenodex_public_follower.py",
    "tools/check_zeno_ledger_light_client_checkpoint.py",
    "tools/build_zeno_sdk_browser_bundle.py",
    "tools/dex-ui/src/sdk/zenoProofClient.js",
    "Dockerfile.hashlocked",
    "tools/build_operator_release_bundle.py",
    "Dockerfile.operator-tools",
    "config/tau_testnet.lock",
    ".github/workflows/native-launcher.yml",
    ".github/workflows/release-publish.yml",
    "docs/NATIVE_INSTALLER_PLAN.md",
    "rust-runtime/Cargo.toml",
    "rust-runtime/Cargo.lock",
    "rust-runtime/crates/zenodex-launcher/Cargo.toml",
    "rust-runtime/crates/zenodex-launcher/src/main.rs",
    ".docker/Dockerfile.tau-local",
    ".docker/nginx.local-testnet.conf.template",
    "docker-compose.local-testnet.yml",
    "docker-compose.two-node.yml",
    "docker-compose.multimachine.yml",
    ".github/workflows/release-integrity.yml",
    "docs/DEPLOYMENT_QUICKSTART.md",
    "docs/LOCAL_TESTNET_QUICKSTART.md",
    "docs/PUBLIC_TESTNET_V0_1_16.md",
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
    _check_tau_testnet_lock(root, checks, errors)
    _check_native_launcher(root, checks, errors)
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
            "native-launcher",
            "single-command-local-testnet",
            "single-click-public-testnet",
            "single-command-public-follower",
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
    local_path = root / "bin" / "zenodex-local-testnet"
    if local_path.is_file():
        local_text = _read(local_path)
        _append_check(
            checks,
            errors,
            check_id="bin_local_testnet_delegates_to_zenoctl_local",
            ok="tools/zenoctl.py" in local_text and "testnet local" in local_text,
            error="bin/zenodex-local-testnet must delegate to tools/zenoctl.py testnet local",
        )
        _append_check(
            checks,
            errors,
            check_id="bin_local_testnet_executable",
            ok=bool(local_path.stat().st_mode & 0o111),
            error="bin/zenodex-local-testnet must be executable",
        )
    public_path = root / "bin" / "zenodex-public-testnet"
    if public_path.is_file():
        public_text = _read(public_path)
        _append_check(
            checks,
            errors,
            check_id="bin_public_testnet_delegates_to_zenoctl_public",
            ok="tools/zenoctl.py" in public_text and "testnet local public" in public_text,
            error="bin/zenodex-public-testnet must delegate to tools/zenoctl.py testnet local public",
        )
        _append_check(
            checks,
            errors,
            check_id="bin_public_testnet_executable",
            ok=bool(public_path.stat().st_mode & 0o111),
            error="bin/zenodex-public-testnet must be executable",
        )
    click_path = root / "bin" / "zenodex-public-testnet.command"
    if click_path.is_file():
        click_text = _read(click_path)
        _append_check(
            checks,
            errors,
            check_id="bin_public_testnet_command_delegates_to_zenoctl_public",
            ok="tools/zenoctl.py" in click_text and "testnet local public" in click_text,
            error="bin/zenodex-public-testnet.command must delegate to tools/zenoctl.py testnet local public",
        )
        _append_check(
            checks,
            errors,
            check_id="bin_public_testnet_command_executable",
            ok=bool(click_path.stat().st_mode & 0o111),
            error="bin/zenodex-public-testnet.command must be executable",
        )
    follower_path = root / "bin" / "zenodex-public-follower"
    if follower_path.is_file():
        follower_text = _read(follower_path)
        _append_check(
            checks,
            errors,
            check_id="bin_public_follower_delegates_to_public_follower_tool",
            ok="tools/zenodex_public_follower.py" in follower_text,
            error="bin/zenodex-public-follower must delegate to tools/zenodex_public_follower.py",
        )
        _append_check(
            checks,
            errors,
            check_id="bin_public_follower_executable",
            ok=bool(follower_path.stat().st_mode & 0o111),
            error="bin/zenodex-public-follower must be executable",
        )


def _check_install_script(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "scripts" / "install_zenodex.sh"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "zenoctl",
        "zenodex-node",
        "zenodex-local-testnet",
        "zenodex-public-testnet",
        "zenodex-public-follower",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "tools/zenodex_public_follower.py",
        "testnet local public",
        "--dry-run",
    ):
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
    for token in (
        "zenoctl",
        "zenodex-node",
        "zenodex-local-testnet",
        "zenodex-public-testnet",
        "zenodex-public-follower",
        ".cmd",
        "tools\\zenoctl.py",
        "tools\\zeno_ledger_node.py",
        "tools\\zenodex_public_follower.py",
        "testnet local public",
    ):
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
    for token in ("zenoctl_testnet_local", "testnet local"):
        _append_check(
            checks,
            errors,
            check_id=f"zenoctl_local_testnet_contains:{token}",
            ok=token in text,
            error=f"tools/zenoctl.py must expose local-testnet command registration token {token}",
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


def _check_tau_testnet_lock(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "config" / "tau_testnet.lock"
    if not path.is_file():
        return

    fields: dict[str, str] = {}
    malformed = False
    for line in _read(path).splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if "=" not in stripped:
            malformed = True
            continue
        key, value = stripped.split("=", 1)
        fields[key.strip()] = value.strip()

    _append_check(
        checks,
        errors,
        check_id="tau_testnet_lock_schema",
        ok=fields.get("schema") == "zenodex.tau_testnet_dependency_lock.v0" and not malformed,
        error="config/tau_testnet.lock schema must be zenodex.tau_testnet_dependency_lock.v0",
    )
    _append_check(
        checks,
        errors,
        check_id="tau_testnet_lock_repo",
        ok=fields.get("repo") == "https://github.com/IDNI/tau-testnet.git",
        error="config/tau_testnet.lock repo must be https://github.com/IDNI/tau-testnet.git",
    )
    _append_check(
        checks,
        errors,
        check_id="tau_testnet_lock_ref",
        ok=fields.get("ref") == "refs/heads/main",
        error="config/tau_testnet.lock ref must be refs/heads/main",
    )
    commit = fields.get("commit", "")
    _append_check(
        checks,
        errors,
        check_id="tau_testnet_lock_commit_sha1",
        ok=len(commit) == 40 and all(ch in "0123456789abcdefABCDEF" for ch in commit),
        error="config/tau_testnet.lock commit must be a 40-character hex SHA-1",
    )
    _append_check(
        checks,
        errors,
        check_id="tau_testnet_lock_server_path",
        ok=fields.get("server_path") == "server.py",
        error="config/tau_testnet.lock server_path must be server.py",
    )


def _check_native_launcher(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    workflow = root / ".github" / "workflows" / "native-launcher.yml"
    if workflow.is_file():
        text = _read(workflow)
        for token in (
            "cargo test -p zenodex-launcher",
            "cargo build --release -p zenodex-launcher",
            "actions/upload-artifact@v4",
            "zenodex-launcher-${{ matrix.os }}",
            "rust-runtime/target/release/zenodex",
            "rust-runtime/target/release/zenodex.exe",
        ):
            _append_check(
                checks,
                errors,
                check_id=f"native_launcher_workflow_contains:{token}",
                ok=token in text,
                error=f".github/workflows/native-launcher.yml must contain {token}",
            )

    release_workflow = root / ".github" / "workflows" / "release-publish.yml"
    if release_workflow.is_file():
        text = _read(release_workflow)
        for token in (
            "build-native-launchers:",
            "cargo build --release -p zenodex-launcher",
            "linux-x86_64",
            "macos-x86_64",
            "windows-x86_64",
            "zenodex-native-launcher-",
        ):
            _append_check(
                checks,
                errors,
                check_id=f"release_publish_native_launcher_contains:{token}",
                ok=token in text,
                error=f".github/workflows/release-publish.yml must contain {token}",
            )

    launcher = root / "rust-runtime" / "crates" / "zenodex-launcher" / "src" / "main.rs"
    lock = root / "config" / "tau_testnet.lock"
    if launcher.is_file():
        text = _read(launcher)
        for token in ("TAU_TESTNET_COMMIT", "TAU_TESTNET_LOCK_REL", "ensure_tau_testnet", "testnet local"):
            _append_check(
                checks,
                errors,
                check_id=f"native_launcher_contains:{token}",
                ok=token in text,
                error=f"rust-runtime/crates/zenodex-launcher/src/main.rs must contain {token}",
            )
        if lock.is_file():
            lock_fields = {
                key.strip(): value.strip()
                for line in _read(lock).splitlines()
                if line.strip() and not line.strip().startswith("#") and "=" in line
                for key, value in [line.strip().split("=", 1)]
            }
            commit = lock_fields.get("commit", "")
            _append_check(
                checks,
                errors,
                check_id="native_launcher_tau_commit_matches_lock",
                ok=bool(commit) and commit in text,
                error="native launcher Tau commit must match config/tau_testnet.lock",
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
    for token in (
        "docker-compose.local-testnet.yml",
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        "packages/zeno-proof-client",
        "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_bundle_builder_includes:{token}",
            ok=token in text,
            error=f"tools/build_operator_release_bundle.py must include {token}",
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
