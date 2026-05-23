"""Packaging + drift checks for @zenodex/proof-client.

The package at ``packages/zeno-proof-client/`` is the publishable npm
artifact. Its source files are synced from ``tools/dex-ui/src/sdk/`` (the
authoritative copy) via ``tools/sync_zeno_proof_client_package.sh``. These
tests fail loudly if:

  - The package source drifts from the dex-ui source.
  - The package's declared ``@noble/curves`` version isn't an exact pin.
  - Required publish-time files are missing.
  - The tarball would include unwanted files (tests, node_modules).
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
PKG_DIR = ROOT / "packages" / "zeno-proof-client"
DEX_UI_SDK = ROOT / "tools" / "dex-ui" / "src" / "sdk"


def test_package_metadata_exists() -> None:
    for name in ("package.json", "README.md", "SECURITY.md", "CHANGELOG.md", "LICENSE"):
        assert (PKG_DIR / name).is_file(), f"missing {name}"


def test_package_json_has_exact_pin_for_noble_curves() -> None:
    meta = json.loads((PKG_DIR / "package.json").read_text(encoding="utf-8"))
    pin = meta["dependencies"]["@noble/curves"]
    assert pin == "1.2.0", (
        f"@noble/curves must be exact-pinned, got {pin!r}. "
        "Caret/tilde ranges are forbidden — see SECURITY.md."
    )


def test_package_json_declares_sideeffects_false() -> None:
    meta = json.loads((PKG_DIR / "package.json").read_text(encoding="utf-8"))
    assert meta.get("sideEffects") is False, (
        "sideEffects: false is required for tree-shaking in browser builds"
    )


def test_package_json_declares_engines_node_20_plus() -> None:
    meta = json.loads((PKG_DIR / "package.json").read_text(encoding="utf-8"))
    engines = meta.get("engines", {})
    node_spec = engines.get("node", "")
    assert ">=20" in node_spec or ">= 20" in node_spec, (
        f"engines.node must require ≥20 (got {node_spec!r}) — earlier versions "
        "lack stable WebCrypto SubtleCrypto / fs.promises semantics we rely on"
    )


def test_package_json_exports_map_complete() -> None:
    meta = json.loads((PKG_DIR / "package.json").read_text(encoding="utf-8"))
    exports = meta["exports"]
    # Three import paths: ".", "./bls", "./client". Plus package.json.
    expected_keys = {".", "./bls", "./client", "./package.json"}
    assert set(exports.keys()) >= expected_keys, (
        f"exports map missing keys: {expected_keys - set(exports.keys())}"
    )


def test_package_source_in_sync_with_dex_ui() -> None:
    """The package's JS source must match dex-ui's SDK byte-for-byte. The
    test scripts are byte-for-byte after path patching."""
    result = subprocess.run(
        ["bash", str(ROOT / "tools" / "sync_zeno_proof_client_package.sh"), "--check"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=30,
    )
    assert result.returncode == 0, (
        f"Package drift detected. Run `bash tools/sync_zeno_proof_client_package.sh` to sync.\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )


def test_package_dependencies_are_minimal() -> None:
    """The runtime dependency surface is exactly one direct package."""
    meta = json.loads((PKG_DIR / "package.json").read_text(encoding="utf-8"))
    deps = meta.get("dependencies", {})
    assert deps == {"@noble/curves": "1.2.0"}, (
        f"unexpected runtime dependencies: {deps!r}. "
        "The SDK's threat model promises @noble/curves is the only direct dep."
    )


def test_package_has_no_devdependencies_in_tarball() -> None:
    """`files:` array must exclude tests, lockfile, and any dev-only artifacts."""
    meta = json.loads((PKG_DIR / "package.json").read_text(encoding="utf-8"))
    files = set(meta.get("files", []))
    assert "test" not in files
    assert "node_modules" not in files


@pytest.mark.skipif(
    not (PKG_DIR / "node_modules").exists(),
    reason="packages/zeno-proof-client/node_modules not installed; run `npm install` there",
)
def test_installed_noble_curves_matches_pin() -> None:
    """The actual installed @noble/curves on disk matches the pinned version."""
    pkg = json.loads(
        (PKG_DIR / "node_modules" / "@noble" / "curves" / "package.json").read_text(encoding="utf-8")
    )
    assert pkg["version"] == "1.2.0"


def test_npm_pack_dry_run_succeeds() -> None:
    """The tarball builds without error and contains expected files."""
    result = subprocess.run(
        ["npm", "pack", "--dry-run", "--json"],
        cwd=PKG_DIR,
        text=True,
        capture_output=True,
        timeout=60,
    )
    assert result.returncode == 0, (
        f"npm pack --dry-run failed:\nstdout: {result.stdout}\nstderr: {result.stderr}"
    )
    payload = json.loads(result.stdout)
    assert isinstance(payload, list) and len(payload) == 1
    entry = payload[0]
    file_names = {f["path"] for f in entry["files"]}
    expected = {
        "package.json",
        "README.md",
        "SECURITY.md",
        "CHANGELOG.md",
        "LICENSE",
        "src/index.js",
        "src/index.d.ts",
        "src/zenoProofClient.js",
        "src/zenoProofClient.d.ts",
        "src/zenoBlsVerifier.js",
        "src/zenoBlsVerifier.d.ts",
    }
    assert expected <= file_names, (
        f"npm tarball missing expected files: {expected - file_names}"
    )
    # Forbidden inclusions.
    forbidden = {"test", "node_modules", "package-lock.json"}
    for name in file_names:
        assert not any(name.startswith(f + "/") or name == f for f in forbidden), (
            f"npm tarball includes forbidden file: {name}"
        )
