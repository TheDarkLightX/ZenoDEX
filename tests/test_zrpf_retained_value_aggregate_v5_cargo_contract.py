from __future__ import annotations

import json
import os
import subprocess
import tomllib
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
HARNESS_MANIFEST = REPOSITORY_ROOT / "zk/zrpf_risc0/harness/Cargo.toml"
HARNESS_PACKAGE = "zenodex-zrpf-risc0-harness"
RETAINED_BIN = "prove_retained_value_aggregate_v5"
RETAINED_FEATURE = "retained-value-aggregate-v5-harness"
METHOD_PACKAGES = {
    "zenodex-zrpf-risc0-methods",
    "zenodex-zrpf-risc0-spot-v6-methods",
}


def _cargo(*arguments: str) -> subprocess.CompletedProcess[str]:
    cargo = os.environ.get("CARGO", "cargo")
    environment = os.environ.copy()
    environment["CARGO_NET_OFFLINE"] = "true"
    return subprocess.run(
        [cargo, *arguments],
        cwd=REPOSITORY_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )


def test_manifest_requires_the_retained_only_feature_for_the_bin() -> None:
    manifest = tomllib.loads(HARNESS_MANIFEST.read_text(encoding="utf-8"))

    features = manifest["features"]
    assert RETAINED_FEATURE not in features["default"]
    assert features[RETAINED_FEATURE] == []
    assert features["legacy-methods"] == ["dep:zenodex-zrpf-risc0-methods"]
    assert features["spot-v6-methods"] == [
        "dep:zenodex-zrpf-risc0-spot-v6-methods"
    ]
    retained_targets = [
        target for target in manifest["bin"] if target["name"] == RETAINED_BIN
    ]
    assert retained_targets == [
        {
            "name": RETAINED_BIN,
            "path": f"src/bin/{RETAINED_BIN}.rs",
            "required-features": [RETAINED_FEATURE],
        }
    ]


def test_cargo_metadata_preserves_the_exact_required_feature() -> None:
    result = _cargo(
        "metadata",
        "--manifest-path",
        str(HARNESS_MANIFEST),
        "--locked",
        "--offline",
        "--no-deps",
        "--format-version",
        "1",
    )
    assert result.returncode == 0, result.stderr
    metadata = json.loads(result.stdout)
    harness = next(
        package
        for package in metadata["packages"]
        if package["name"] == HARNESS_PACKAGE
    )
    assert harness["features"][RETAINED_FEATURE] == []
    retained = next(
        target for target in harness["targets"] if target["name"] == RETAINED_BIN
    )
    assert retained["required-features"] == [RETAINED_FEATURE]


def test_retained_only_dependency_tree_excludes_method_build_packages() -> None:
    result = _cargo(
        "tree",
        "--manifest-path",
        str(HARNESS_MANIFEST),
        "--locked",
        "--offline",
        "-p",
        HARNESS_PACKAGE,
        "--no-default-features",
        "--features",
        RETAINED_FEATURE,
        "--edges",
        "normal,build,dev",
        "--prefix",
        "none",
        "--no-dedupe",
    )
    assert result.returncode == 0, result.stderr
    closure_packages = {
        line.split(" v", maxsplit=1)[0].strip() for line in result.stdout.splitlines()
    }
    assert METHOD_PACKAGES.isdisjoint(closure_packages)
