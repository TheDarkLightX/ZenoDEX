"""Strict JSON and source-pin helpers for the ZRPF ShapeForge checker."""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_KEYS = {"name", "path"}
PIN_KEYS = {"path", "sha256"}
LOWER_HEX_64 = re.compile(r"[0-9a-f]{64}\Z")
EXPECTED_SOURCE_PATHS = [
    "docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json",
    "docs/zenodex/shapeforge_promoted/tactic_bank.seed.json",
    "docs/zenodex/shapeforge_promoted/scenario_corpus.seed.json",
    "docs/zenodex/shapeforge_promoted/development_import_bundle.json",
    "docs/zenodex/shapeforge_promoted/zenodex_negative_knowledge.seed.json",
    "src/core/epoch_effect_composition_v1.py",
    "src/core/global_economic_proof_v1.py",
    "src/integration/global_economic_commit_v1.py",
    "tests/core/test_global_settlement_abi_v1.py",
    "tests/core/test_asset_lane_coordinator_v1.py",
    "zk/global_settlement_abi_v1/README.md",
    "src/core/asset_transfer_lane_module_v1.py",
    "tests/core/test_asset_transfer_lane_module_v1.py",
    "zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs",
    "zk/global_settlement_abi_v1/tests/asset_transfer_lane_module.rs",
    "zk/global_settlement_abi_v1/src/lib.rs",
    "src/core/managed_asset_lifecycle_lane_module_v1.py",
    "tests/core/test_managed_asset_lifecycle_lane_module_v1.py",
    "zk/global_settlement_abi_v1/src/managed_asset_lifecycle_lane_module.rs",
    "zk/global_settlement_abi_v1/tests/managed_asset_lifecycle_lane_module.rs",
    "src/core/lane_module_release_route_binding_v1.py",
    "tests/core/test_lane_module_release_route_binding_v1.py",
    "zk/global_settlement_abi_v1/src/release.rs",
    "zk/global_settlement_abi_v1/src/lane_module_release_route_binding.rs",
    "zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs",
    "src/core/lane_module_receipt_verification_v1.py",
    "zk/global_settlement_abi_v1/src/lane_module_receipt_verification.rs",
    "src/core/receipt_backed_asset_lane_composition_v1.py",
    "zk/global_settlement_abi_v1/src/receipt_backed_asset_lane_composition.rs",
    "tests/core/test_receipt_backed_asset_lane_composition_boundaries_v1.py",
    "zk/global_settlement_abi_v1/src/asset_lane_projection.rs",
    "src/core/global_settlement_types_v1.py",
    "src/core/global_settlement_abi_v1.py",
    "src/core/route_composition_receipt_verification_v1.py",
    "zk/global_settlement_abi_v1/src/route_composition_receipt_verification.rs",
    "zk/global_settlement_abi_v1/src/epoch_effect_composition.rs",
    "zk/global_settlement_abi_v1/src/economic_epoch_receipt_verification.rs",
    "zk/global_settlement_abi_v1/tests/golden_vectors.rs",
    "tests/data/global_settlement_abi_v1_golden.json",
    "tools/render_global_settlement_abi_v1_golden.py",
    "tests/core/test_global_settlement_abi_v1_parity.py",
    "zk/global_economic_epoch_risc0/Cargo.toml",
    "zk/global_economic_epoch_risc0/Cargo.lock",
    "zk/global_economic_epoch_risc0/rust-toolchain.toml",
    "zk/global_economic_epoch_risc0/README.md",
    "zk/global_economic_epoch_risc0/shared/Cargo.toml",
    "zk/global_economic_epoch_risc0/shared/src/lib.rs",
    "zk/global_economic_epoch_risc0/shared/src/preflight.rs",
    "zk/global_economic_epoch_risc0/shared/src/aggregation.rs",
    "zk/global_economic_epoch_risc0/shared/tests/epoch_preflight.rs",
    "zk/global_economic_epoch_risc0/shared/tests/aggregation_preflight.rs",
    "zk/global_economic_epoch_risc0/methods/Cargo.toml",
    "zk/global_economic_epoch_risc0/methods/build.rs",
    "zk/global_economic_epoch_risc0/methods/src/lib.rs",
    "zk/global_economic_epoch_risc0/methods/epoch/Cargo.toml",
    "zk/global_economic_epoch_risc0/methods/epoch/src/main.rs",
    "zk/global_economic_epoch_risc0/host/Cargo.toml",
    "zk/global_economic_epoch_risc0/host/src/lib.rs",
    "zk/global_economic_epoch_risc0/host/tests/receipt_admission.rs",
    "zk/global_economic_epoch_risc0/host/tests/real_composition.rs",
    "zk/global_economic_epoch_risc0/host/tests/real_aggregation_nine.rs",
    "zk/global_economic_epoch_risc0/test_methods/Cargo.toml",
    "zk/global_economic_epoch_risc0/test_methods/build.rs",
    "zk/global_economic_epoch_risc0/test_methods/src/lib.rs",
    "zk/global_economic_epoch_risc0/test_methods/route_structural_test_leaf/Cargo.toml",
    "zk/global_economic_epoch_risc0/test_methods/route_structural_test_leaf/src/main.rs",
    "zk/asset_transfer_module_risc0/Cargo.toml",
    "zk/asset_transfer_module_risc0/Cargo.lock",
    "zk/asset_transfer_module_risc0/rust-toolchain.toml",
    "zk/asset_transfer_module_risc0/README.md",
    "zk/asset_transfer_module_risc0/shared/Cargo.toml",
    "zk/asset_transfer_module_risc0/shared/src/lib.rs",
    "zk/asset_transfer_module_risc0/shared/tests/transition_preflight.rs",
    "zk/asset_transfer_module_risc0/methods/Cargo.toml",
    "zk/asset_transfer_module_risc0/methods/build.rs",
    "zk/asset_transfer_module_risc0/methods/src/lib.rs",
    "zk/asset_transfer_module_risc0/methods/guest/Cargo.toml",
    "zk/asset_transfer_module_risc0/methods/guest/src/main.rs",
    "zk/asset_transfer_module_risc0/host/Cargo.toml",
    "zk/asset_transfer_module_risc0/host/src/lib.rs",
    "zk/asset_transfer_module_risc0/host/tests/receipt_admission.rs",
    "zk/asset_transfer_module_risc0/host/tests/real_proof.rs",
    "zk/asset_lane_coordinator_risc0/Cargo.toml",
    "zk/asset_lane_coordinator_risc0/Cargo.lock",
    "zk/asset_lane_coordinator_risc0/rust-toolchain.toml",
    "zk/asset_lane_coordinator_risc0/README.md",
    "zk/asset_lane_coordinator_risc0/shared/Cargo.toml",
    "zk/asset_lane_coordinator_risc0/shared/src/lib.rs",
    "zk/asset_lane_coordinator_risc0/shared/tests/coordinator_preflight.rs",
    "zk/asset_lane_coordinator_risc0/methods/Cargo.toml",
    "zk/asset_lane_coordinator_risc0/methods/build.rs",
    "zk/asset_lane_coordinator_risc0/methods/src/lib.rs",
    "zk/asset_lane_coordinator_risc0/methods/guest/Cargo.toml",
    "zk/asset_lane_coordinator_risc0/methods/guest/src/main.rs",
    "zk/asset_lane_coordinator_risc0/host/Cargo.toml",
    "zk/asset_lane_coordinator_risc0/host/src/lib.rs",
    "zk/asset_lane_coordinator_risc0/host/tests/receipt_admission.rs",
    "zk/asset_lane_coordinator_risc0/host/tests/real_composition.rs",
    "zk/asset_lane_coordinator_risc0/host/tests/support/mod.rs",
    "zk/asset_lane_coordinator_risc0/host/tests/support/governed_registries.rs",
    "zk/asset_lane_coordinator_risc0/host/tests/support/governed_scenario.rs",
]


class ContractError(ValueError):
    """Raised when a ShapeForge contract or artifact is ambiguous."""


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ContractError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> Mapping[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ContractError) as exc:
        raise ContractError(f"{path}: decode failed: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ContractError(f"{path}: root must be an object")
    return value


def load_artifacts(contract: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    rows = contract.get("required_artifacts")
    if not isinstance(rows, list):
        raise ContractError("required_artifacts must be a list")
    artifacts: dict[str, dict[str, Any]] = {}
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping) or set(row) != ARTIFACT_KEYS:
            raise ContractError(f"required_artifacts[{index}] is malformed")
        name = row["name"]
        raw_path = row["path"]
        if not isinstance(name, str) or not isinstance(raw_path, str):
            raise ContractError(f"required_artifacts[{index}] fields must be strings")
        if name in artifacts:
            raise ContractError(f"duplicate artifact name: {name}")
        artifacts[name] = dict(load_json(REPO_ROOT / raw_path))
    return artifacts


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def validate_source_pins(contract: Mapping[str, Any], errors: list[str]) -> int:
    pins = contract.get("source_pins")
    if not isinstance(pins, list) or not pins:
        errors.append("source_pins must be a nonempty list")
        return 0
    seen: set[str] = set()
    actual_paths: list[str] = []
    for index, pin in enumerate(pins):
        label = f"source_pins[{index}]"
        if not exact_keys(pin, PIN_KEYS, label, errors):
            continue
        assert isinstance(pin, Mapping)
        raw_path = pin.get("path")
        expected = pin.get("sha256")
        if not isinstance(raw_path, str) or not raw_path:
            errors.append(f"{label}.path must be a nonempty string")
            continue
        actual_paths.append(raw_path)
        path = Path(raw_path)
        if path.is_absolute() or ".." in path.parts:
            errors.append(f"{label}.path must be repository-relative without '..'")
            continue
        if raw_path in seen:
            errors.append(f"{label}.path is duplicated")
        seen.add(raw_path)
        if not isinstance(expected, str) or LOWER_HEX_64.fullmatch(expected) is None:
            errors.append(f"{label}.sha256 must be 64 lowercase hexadecimal characters")
            continue
        source = REPO_ROOT / path
        if not source.is_file():
            errors.append(f"{label} source is missing: {raw_path}")
            continue
        if sha256_file(source) != expected:
            errors.append(f"{label} sha256 mismatch for {raw_path}")
    if actual_paths != EXPECTED_SOURCE_PATHS:
        errors.append("source_pins paths must equal the closed ordered source list")
    return len(pins)


def exact_keys(value: Any, expected: set[str], label: str, errors: list[str]) -> bool:
    if not isinstance(value, Mapping):
        errors.append(f"{label} must be an object")
        return False
    if set(value) != expected:
        errors.append(
            f"{label} keys differ: missing={sorted(expected - set(value))}, "
            f"surplus={sorted(set(value) - expected)}"
        )
        return False
    return True


def nonempty_string(value: Any, label: str, errors: list[str]) -> bool:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{label} must be a nonempty string")
        return False
    return True


def nonempty_unique_strings(value: Any, label: str, errors: list[str]) -> list[str] | None:
    if not isinstance(value, list) or not value:
        errors.append(f"{label} must be a nonempty list")
        return None
    if any(not isinstance(item, str) or not item.strip() for item in value):
        errors.append(f"{label} must contain nonempty strings")
        return None
    if len(value) != len(set(value)):
        errors.append(f"{label} must not contain duplicates")
        return None
    return value


def objects_with(items: Any, key: str, expected: str) -> list[Mapping[str, Any]]:
    if not isinstance(items, list):
        return []
    return [item for item in items if isinstance(item, Mapping) and item.get(key) == expected]


def ids(items: Any) -> list[str]:
    if not isinstance(items, list):
        return []
    return [str(item.get("id")) for item in items if isinstance(item, Mapping)]


__all__ = [
    "ContractError",
    "exact_keys",
    "ids",
    "load_artifacts",
    "load_json",
    "nonempty_string",
    "nonempty_unique_strings",
    "objects_with",
    "sha256_file",
    "validate_source_pins",
]
