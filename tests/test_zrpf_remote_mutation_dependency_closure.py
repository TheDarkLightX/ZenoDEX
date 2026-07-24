from __future__ import annotations

import tomllib
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT / "zk/spot_settlement_v7_risc0"
MUTATION_PACKAGE = "zenodex-zrpf-risc0-spot-v7-remote-mutation-verifier"
V6_METHODS_PACKAGE = "zenodex-zrpf-risc0-spot-v6-methods"


def _manifest(path: Path) -> dict[str, Any]:
    return tomllib.loads(path.read_text(encoding="utf-8"))


def _local_dependency_manifests(manifest_path: Path) -> tuple[Path, ...]:
    document = _manifest(manifest_path)
    tables: list[dict[str, Any]] = [
        cast(dict[str, Any], document.get("dependencies", {})),
        cast(dict[str, Any], document.get("dev-dependencies", {})),
        cast(dict[str, Any], document.get("build-dependencies", {})),
    ]
    for target in cast(dict[str, Any], document.get("target", {})).values():
        target_table = cast(dict[str, Any], target)
        for key in ("dependencies", "dev-dependencies", "build-dependencies"):
            tables.append(cast(dict[str, Any], target_table.get(key, {})))

    dependencies: list[Path] = []
    for table in tables:
        for value in table.values():
            if not isinstance(value, dict) or not isinstance(value.get("path"), str):
                continue
            dependency = (manifest_path.parent / value["path"] / "Cargo.toml").resolve()
            assert dependency.is_file()
            dependencies.append(dependency)
    return tuple(dependencies)


def _local_package_closure(*roots: Path) -> frozenset[str]:
    pending = [path.resolve() for path in roots]
    seen: set[Path] = set()
    packages: set[str] = set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        document = _manifest(current)
        package = cast(dict[str, Any], document["package"])
        packages.add(cast(str, package["name"]))
        pending.extend(_local_dependency_manifests(current))
    return frozenset(packages)


def test_production_v7_verifier_and_firecracker_exclude_mutation_only_packages() -> None:
    closure = _local_package_closure(
        WORKSPACE / "verifier/Cargo.toml",
        WORKSPACE / "firecracker_runtime/Cargo.toml",
    )
    assert MUTATION_PACKAGE not in closure
    assert V6_METHODS_PACKAGE not in closure

    verifier_dependencies = cast(
        dict[str, Any], _manifest(WORKSPACE / "verifier/Cargo.toml")["dependencies"]
    )
    assert "libc" not in verifier_dependencies
    for dependency in (
        "zenodex-zrpf-risc0-spot-settlement-root-policy-v6",
        "zenodex-zrpf-risc0-spot-v6-methods",
        "zenodex-zrpf-risc0-spot-value-aggregate-l1-policy-v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l2-policy-v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-root-policy-v6",
        "zenodex-zrpf-risc0-spot-value-leaf-v6-shared",
        "zenodex-zrpf-risc0-value-aggregate-shared",
    ):
        assert dependency not in verifier_dependencies


def test_methods_export_one_stable_host_alias_for_real_and_skipped_builds() -> None:
    build = (WORKSPACE / "methods/build.rs").read_text(encoding="utf-8")
    library = (WORKSPACE / "methods/src/lib.rs").read_text(encoding="utf-8")
    for kind in ("ELF", "ID"):
        generated = f"ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_GUEST_{kind}"
        stable = f"ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_{kind}"
        assert f"pub const {generated}" in build
        assert f"pub use {generated} as {stable};" in library
        assert f"pub const {stable}" not in build
