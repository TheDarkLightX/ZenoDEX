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
    "scripts/install_zenodex.sh",
    "scripts/install_zenodex.ps1",
    "scripts/zenodex_testnet_demo.sh",
    "scripts/zenodex_testnet_demo.ps1",
    "tools/zenoctl.py",
    "tools/zeno_ledger_node.py",
    "tools/check_zeno_ledger_light_client_checkpoint.py",
    "tools/build_zeno_sdk_browser_bundle.py",
    "tools/dex-ui/src/sdk/zenoProofClient.js",
    "Dockerfile.hashlocked",
    "tools/build_operator_release_bundle.py",
    "Dockerfile.operator-tools",
    ".dockerignore",
    ".docker/entrypoint.sh",
    ".docker/nginx.conf",
    ".docker/Dockerfile.tau-local",
    ".docker/nginx.local-testnet.conf.template",
    "docker-compose.local-testnet.yml",
    "docker-compose.two-node.yml",
    "docker-compose.multimachine.yml",
    "docker-compose.testnet-demo.yml",
    ".github/workflows/native-launcher.yml",
    ".github/workflows/release-integrity.yml",
    ".github/workflows/release-publish.yml",
    "tools/check_release_publication_workflow.py",
    "tools/build_release_sboms.py",
    "tools/dex-ui/src/lib/api.js",
    "tools/dex-ui/public/zenodex-config.json",
    "docs/DEPLOYMENT_QUICKSTART.md",
    "docs/LOCAL_TESTNET_QUICKSTART.md",
    "docs/NATIVE_INSTALLER_PLAN.md",
    "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
    "rust-runtime/Cargo.toml",
    "rust-runtime/crates/zenodex-launcher/Cargo.toml",
    "rust-runtime/crates/zenodex-launcher/src/main.rs",
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
    _check_testnet_demo_scripts(root, checks, errors)
    _check_testnet_demo_compose(root, checks, errors)
    _check_base_compose_loopback_ui(root, checks, errors)
    _check_testnet_demo_runtime_config(root, checks, errors)
    _check_zenoctl_light_client(root, checks, errors)
    _check_browser_sdk(root, checks, errors)
    _check_release_bundle_builder(root, checks, errors)
    _check_release_integrity_builds_operator_bundle(root, checks, errors)
    _check_release_publication_workflow(root, checks, errors)
    _check_hashlocked_dockerfile(root, "Dockerfile.hashlocked", checks, errors)
    _check_hashlocked_dockerfile(root, "Dockerfile.operator-tools", checks, errors)
    _check_operator_tools_image_inputs(root, checks, errors)
    _check_dockerignore_operator_inputs(root, checks, errors)

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
            "public-testnet-join-wrapper",
            "light-client-checkpoint-verifier",
            "proof-carrying-browser-bundle",
            "browser-wallet-sync-sdk",
            "single-command-local-testnet",
            "native-launcher",
            "github-release-assets",
            "github-release-publication",
            "ghcr-container-publication",
            "manual-npm-publication",
            "local-testnet-demo",
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


def _check_install_script(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "scripts" / "install_zenodex.sh"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "zenoctl",
        "zenodex-node",
        "zenodex-local-testnet",
        "tools/zenoctl.py",
        "tools/zeno_ledger_node.py",
        "testnet local",
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
        ".cmd",
        "tools\\zenoctl.py",
        "tools\\zeno_ledger_node.py",
        "testnet local",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"install_ps1_contains:{token}",
            ok=token in text,
            error=f"scripts/install_zenodex.ps1 must contain {token}",
        )


def _check_testnet_demo_scripts(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    shell_path = root / "scripts" / "zenodex_testnet_demo.sh"
    if shell_path.is_file():
        text = _read(shell_path)
        for token in (
            "docker-compose.testnet-demo.yml",
            "DEMO_API_TOKEN",
            "--dry-run",
            "smoke",
            "tools/zenoctl.py testnet up --profile docker-two-node",
        ):
            _append_check(
                checks,
                errors,
                check_id=f"testnet_demo_sh_contains:{token}",
                ok=token in text,
                error=f"scripts/zenodex_testnet_demo.sh must contain {token}",
            )
        _append_check(
            checks,
            errors,
            check_id="testnet_demo_sh_executable",
            ok=bool(shell_path.stat().st_mode & 0o111),
            error="scripts/zenodex_testnet_demo.sh must be executable",
        )
    ps_path = root / "scripts" / "zenodex_testnet_demo.ps1"
    if ps_path.is_file():
        text = _read(ps_path)
        for token in ("docker-compose.testnet-demo.yml", "zenodex-local-demo-token", "smoke", "tools/zenoctl.py"):
            _append_check(
                checks,
                errors,
                check_id=f"testnet_demo_ps1_contains:{token}",
                ok=token in text,
                error=f"scripts/zenodex_testnet_demo.ps1 must contain {token}",
            )


def _check_testnet_demo_compose(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "docker-compose.testnet-demo.yml"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "ZENODEX_TESTNET_DEMO=1",
        "API_HOST=127.0.0.1",
        "ALLOW_DEMO_TOKEN_AUTH=1",
        "DEX_API_ENABLED=true",
        "PERPS_API_ENABLED=true",
        "ZUSD_API_ENABLED=true",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"testnet_demo_compose_contains:{token}",
            ok=token in text,
            error=f"docker-compose.testnet-demo.yml must contain {token}",
        )


def _check_base_compose_loopback_ui(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "docker-compose.yml"
    if not path.is_file():
        return
    text = _read(path)
    _append_check(
        checks,
        errors,
        check_id="base_compose_ui_loopback_default",
        ok="${UI_HOST:-127.0.0.1}:${UI_PORT:-3000}:8080" in text,
        error="docker-compose.yml must bind the UI to 127.0.0.1 by default",
    )


def _check_testnet_demo_runtime_config(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    entrypoint = root / ".docker" / "entrypoint.sh"
    if entrypoint.is_file():
        text = _read(entrypoint)
        for token in (
            "ZENODEX_TESTNET_DEMO",
            "/tmp/zenodex-config.json",
            '"apiToken"',
            "DEMO_API_TOKEN",
        ):
            _append_check(
                checks,
                errors,
                check_id=f"testnet_demo_entrypoint_contains:{token}",
                ok=token in text,
                error=f".docker/entrypoint.sh must contain {token}",
            )
    nginx = root / ".docker" / "nginx.conf"
    if nginx.is_file():
        text = _read(nginx)
        for token in (
            "location = /zenodex-config.json",
            "alias /tmp/zenodex-config.json",
            "no-store",
            "proxy_pass http://127.0.0.1:8000;",
        ):
            _append_check(
                checks,
                errors,
                check_id=f"testnet_demo_nginx_contains:{token}",
                ok=token in text,
                error=f".docker/nginx.conf must contain {token}",
            )
    api_js = root / "tools" / "dex-ui" / "src" / "lib" / "api.js"
    if api_js.is_file():
        text = _read(api_js)
        _append_check(
            checks,
            errors,
            check_id="testnet_demo_ui_runtime_api_token",
            ok="getRuntimeConfig().apiToken" in text,
            error="tools/dex-ui/src/lib/api.js must read apiToken from runtime config",
        )


def _check_zenoctl_light_client(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "tools" / "zenoctl.py"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "light-client",
        "testnet",
        "demo",
        "join",
        "join-network",
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
        "rust-runtime",
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


def _check_release_integrity_builds_operator_bundle(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / ".github" / "workflows" / "release-integrity.yml"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "contents: read",
        "Build operator release bundle",
        "tools/build_operator_release_bundle.py build",
        "tools/build_operator_release_bundle.py verify",
        "Compute combined SHA256SUMS",
        "Generate SBOMs",
        "tools/build_release_sboms.py",
        "Attest operator bundle provenance",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_integrity_contains:{token}",
            ok=token in text,
            error=f".github/workflows/release-integrity.yml must contain {token}",
        )


def _check_release_publication_workflow(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / ".github" / "workflows" / "release-publish.yml"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "softprops/action-gh-release@v2",
        "docker/build-push-action@v6",
        "npm publish --access public --provenance",
        "tools/build_operator_release_bundle.py build",
        "cargo build --manifest-path rust-runtime/Cargo.toml --release -p zenodex-launcher",
        "tools/build_release_sboms.py",
        "SHA256SUMS",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_publish_contains:{token}",
            ok=token in text,
            error=f".github/workflows/release-publish.yml must contain {token}",
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


def _check_operator_tools_image_inputs(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "Dockerfile.operator-tools"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "COPY formal/property/production_key_management_v0.json",
        "COPY generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
        "USER zenodex",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"operator_tools_image_contains:{token}",
            ok=token in text,
            error=f"Dockerfile.operator-tools must contain {token}",
        )


def _check_dockerignore_operator_inputs(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / ".dockerignore"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "!formal/property/production_key_management_v0.json",
        "!generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
        "!tools/dex-ui/**",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"dockerignore_contains:{token}",
            ok=token in text,
            error=f".dockerignore must contain {token}",
        )


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
