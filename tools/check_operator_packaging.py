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

from src.integration.local_route_quarantine import (  # noqa: E402
    current_local_operator_release_admission_v1,
)
from tools.check_docker_hashlocked_install import evaluate_dockerfile  # noqa: E402

REPORT_SCHEMA = "zenodex/operator_packaging_readiness/v1"
HISTORICAL_RELEASE_REF_BLOCKER_V1 = (
    "historical workflow refs remain an external repository-control blocker until "
    "workflow disablement or equivalent tag and dispatch restrictions are independently verified"
)
SUPPORTED_OPERATOR_PATHS_V1 = (
    "docker-compose",
    "hashlocked-dockerfile",
    "posix-wrapper",
    "windows-cmd-wrapper-installer",
    "light-client-checkpoint-verifier",
    "proof-carrying-browser-bundle",
    "browser-wallet-sync-sdk",
    "single-command-local-testnet",
    "single-command-public-follower",
)
RETAINED_BLOCKED_OPERATOR_PATHS_V1 = (
    "single-click-public-testnet",
    "github-release-assets",
)


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

    path_overlap = sorted(
        set(SUPPORTED_OPERATOR_PATHS_V1) & set(RETAINED_BLOCKED_OPERATOR_PATHS_V1)
    )
    _append_check(
        checks,
        errors,
        check_id="supported_operator_paths_exclude_retained_blocked_paths",
        ok=not path_overlap,
        error=f"retained blocked operator paths advertised as supported: {path_overlap}",
    )

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
    _check_release_integrity_blocks_publication(root, checks, errors)
    _check_hashlocked_dockerfile(root, "Dockerfile.hashlocked", checks, errors)
    _check_hashlocked_dockerfile(root, "Dockerfile.operator-tools", checks, errors)

    admission = current_local_operator_release_admission_v1()
    packaging_integrity_ok = not errors
    checks.append(
        {
            "id": "current_operator_release_admission",
            "ok": admission.current_release_eligible,
            "profile_id": admission.profile_id,
            "authority": admission.authority,
            "vm_gates_closed": list(admission.vm_gates_closed),
        }
    )

    return {
        "schema": REPORT_SCHEMA,
        "ok": packaging_integrity_ok and admission.current_release_eligible,
        "status": "blocked_current_profile",
        "packaging_integrity_ok": packaging_integrity_ok,
        "current_profile_id": admission.profile_id,
        "current_release_eligible": admission.current_release_eligible,
        "authority": admission.authority,
        "vm_gates_closed": list(admission.vm_gates_closed),
        "release_blockers": [admission.blocker],
        "repository_controls_verified": False,
        "external_release_blockers": [HISTORICAL_RELEASE_REF_BLOCKER_V1],
        "errors": errors,
        "checks": checks,
        "supported_operator_paths": list(SUPPORTED_OPERATOR_PATHS_V1),
        "retained_blocked_operator_paths": list(RETAINED_BLOCKED_OPERATOR_PATHS_V1),
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


def _check_release_bundle_builder(root: Path, checks: list[dict[str, Any]], errors: list[str]) -> None:
    path = root / "tools" / "build_operator_release_bundle.py"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "OperatorReleaseAdmissionRejectV1",
        "build_operator_candidate_bundle",
        "verify_operator_candidate_manifest",
        "UNADMITTED_CANDIDATE_NO_RELEASE_AUTHORITY",
        "zenodex.operator_candidate_bundle.v1",
        "archive_sha256",
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_bundle_builder_contains:{token}",
            ok=token in text,
            error=f"tools/build_operator_release_bundle.py must contain {token}",
        )
    for forbidden in (
        'SCHEMA = "zenodex.operator_release_bundle.v0"',
        'archive_name = f"zenodex-operator-{_safe_version(version)}.tar.gz"',
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_bundle_builder_omits:{forbidden}",
            ok=forbidden not in text,
            error=f"tools/build_operator_release_bundle.py retains release-labelled output: {forbidden}",
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


def _check_release_integrity_blocks_publication(
    root: Path,
    checks: list[dict[str, Any]],
    errors: list[str],
) -> None:
    path = root / ".github" / "workflows" / "release-integrity.yml"
    if not path.is_file():
        return
    text = _read(path)
    for token in (
        "name: release-integrity-blocked",
        "contents: read",
        "Enforce current operator release admission",
        "python3 tools/check_operator_packaging.py --pretty",
        "Unreachable release guard",
        'test "${{ job.status }}" = "failure"',
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_integrity_contains:{token}",
            ok=token in text,
            error=f".github/workflows/release-integrity.yml must contain {token}",
        )
    for forbidden in (
        "contents: write",
        "id-token: write",
        "attestations: write",
        "tools/build_operator_release_bundle.py build",
        "gh release",
        "actions/attest-build-provenance",
        "actions/upload-artifact",
        'tags:\n      - "v*"',
    ):
        _append_check(
            checks,
            errors,
            check_id=f"release_integrity_omits:{forbidden}",
            ok=forbidden not in text,
            error=f"release-integrity retains blocked publication capability: {forbidden}",
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
