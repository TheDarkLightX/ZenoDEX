#!/usr/bin/env python3
"""Compile and kill two native coordinator semantic mutants using retained tests.

Run after the unchanged workspace tests pass. Builds are offline and use the
existing ABI target directory (or CARGO_TARGET_DIR). No guest is built.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = Path("zk/asset_lane_custody_coordinator_risc0")
LIB = WORKSPACE / "shared/src/lib.rs"
MEMBERS = (
    "Cargo.toml",
    "shared/Cargo.toml",
    "shared/src/lib.rs",
    "shared/tests/custody_coordinator_preflight.rs",
    "shared/tests/python_parity.rs",
)
FIXTURES = (
    "asset_transfer_lane_module_custody_v1_golden.json",
    "asset_lane_custody_coordinator_v1_golden.json",
)


def _run(
    args: list[str], cwd: Path, environment: dict[str, str]
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["cargo", "+1.90.0", *args],
        cwd=cwd,
        env=environment,
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )


def _require_success(result: subprocess.CompletedProcess[str]) -> None:
    if result.returncode != 0:
        raise RuntimeError(result.stdout + result.stderr)


def _replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"mutation anchor must occur exactly once: {old!r}")
    return text.replace(old, new, 1)


def _mutant(name: str, root: Path) -> tuple[Path, str, str]:
    workspace = root / WORKSPACE
    for relative in MEMBERS:
        destination = workspace / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / WORKSPACE / relative, destination)
    for name_in_fixture in FIXTURES:
        destination = root / "tests/data" / name_in_fixture
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "tests/data" / name_in_fixture, destination)
    manifest_path = workspace / "shared/Cargo.toml"
    manifest = manifest_path.read_text()
    source = (root / LIB).read_text()
    if name == "legacy_module_substitution":
        source = _replace_once(
            source,
            "use zenodex_asset_transfer_custody_module_risc0_shared::{",
            "use zenodex_asset_transfer_module_risc0_shared::{",
        )
        source = _replace_once(
            source,
            "prepare_asset_transfer_custody_module_v1, AssetTransferGuestErrorV1,",
            "prepare_asset_transfer_module_v1 as prepare_asset_transfer_custody_module_v1, "
            "AssetTransferGuestErrorV1,",
        )
        manifest = _replace_once(
            manifest,
            'zenodex-asset-transfer-custody-module-risc0-shared = { path = "../../asset_transfer_custody_module_risc0/shared" }',
            'zenodex-asset-transfer-module-risc0-shared = { path = "../../asset_transfer_module_risc0/shared" }',
        )
        test_binary = "python_parity"
        test_name = "complete_python_lane_values_and_canonical_journals_match"
    elif name == "omit_canonical_input_check":
        source = _replace_once(source, "if canonical != input_bytes {", "if false {")
        test_binary = "custody_coordinator_preflight"
        test_name = "raw_preflight_checks_bounds_and_canonicality_before_typed_validation"
    else:
        raise ValueError("unknown semantic mutant")
    for dependency in (
        "global_settlement_abi_v1",
        "asset_transfer_custody_module_risc0/shared",
        "asset_transfer_module_risc0/shared",
        "asset_lane_coordinator_risc0/shared",
    ):
        manifest = manifest.replace(
            json.dumps(f"../../{dependency}"), json.dumps(str(ROOT / "zk" / dependency))
        )
    manifest_path.write_text(manifest)
    (root / LIB).write_text(source)
    return workspace, test_binary, test_name


def main() -> None:
    environment = dict(os.environ)
    environment["CARGO_INCREMENTAL"] = "0"
    environment.setdefault("CARGO_TARGET_DIR", str(ROOT / "zk/global_settlement_abi_v1/target"))
    observations = []
    for name in ("legacy_module_substitution", "omit_canonical_input_check"):
        with tempfile.TemporaryDirectory(prefix="zenodex-custody-coordinator-mutant-") as scratch:
            workspace, test_binary, test_name = _mutant(name, Path(scratch))
            _require_success(_run(["generate-lockfile", "--offline"], workspace, environment))
            arguments = ["test", "--locked", "--offline", "-j", "2", "--test", test_binary]
            _require_success(_run([*arguments, "--no-run"], workspace, environment))
            result = _run([*arguments, test_name, "--", "--exact"], workspace, environment)
            if result.returncode != 101 or f"test {test_name} ... FAILED" not in result.stdout:
                raise RuntimeError(
                    f"{name}: expected semantic failure absent\n{result.stdout}{result.stderr}"
                )
            observations.append({"mutant": name, "compiled": True, "killed_by": test_name})
    print(
        json.dumps(
            {
                "authority": "NONE",
                "source_sha256": hashlib.sha256((ROOT / LIB).read_bytes()).hexdigest(),
                "observations": observations,
            },
            sort_keys=True,
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
