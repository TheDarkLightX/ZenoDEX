"""Feature-suite manifests for grouping ZenoLedger feature lanes."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_v0 import hash_v0


FEATURE_SUITE_SCHEMA_V0 = "zenodex/zeno_ledger/feature_suite/v0"
FEATURE_SUITE_LANE_SCHEMA_V0 = "zenodex.zeno_ledger.testnet_bundle.v0"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _is_relative_safe(path_text: str) -> bool:
    path = Path(path_text)
    return not path.is_absolute() and path_text != "" and ".." not in path.parts


def _relative_to_base(path: Path, base_dir: Path | None) -> str:
    if base_dir is None:
        return str(path)
    rel = path.resolve().relative_to(base_dir.resolve()).as_posix()
    if not _is_relative_safe(rel):
        raise ValueError(f"unsafe feature lane path: {rel}")
    return rel


def _resolve_lane_path(path_text: str, base_dir: Path | None) -> Path:
    path = Path(path_text)
    if path.is_absolute() or base_dir is None:
        return path
    if not _is_relative_safe(path_text):
        raise ValueError(f"unsafe feature lane path: {path_text}")
    return base_dir / path


def _optional_relative_to_base(value: object, base_dir: Path | None) -> object:
    if base_dir is None or not isinstance(value, str) or value == "":
        return value
    path = Path(value)
    if not path.is_absolute():
        return value
    rel = path.resolve().relative_to(base_dir.resolve()).as_posix()
    if not _is_relative_safe(rel):
        raise ValueError(f"unsafe feature metadata path: {rel}")
    return rel


def _validate_lane_manifest(path: Path) -> Mapping[str, Any]:
    if not path.is_file():
        raise ValueError(f"feature lane manifest missing: {path}")
    manifest = _load_json_object(path)
    if manifest.get("schema") != FEATURE_SUITE_LANE_SCHEMA_V0:
        raise ValueError(f"feature lane manifest schema mismatch: {path}")
    required = {
        "chain_id",
        "run_commands",
        "verify_command",
        "attest_command",
        "mirror_index_command",
    }
    missing = sorted(key for key in required if key not in manifest)
    if missing:
        raise ValueError(f"feature lane manifest missing keys: {missing}")
    return manifest


def build_feature_suite_manifest_v0(
    *,
    suite_name: str,
    lanes: Sequence[tuple[str, Path]],
    required_features: Sequence[str] = (),
    base_dir: Path | None = None,
) -> dict[str, Any]:
    name = _require_str(suite_name, name="suite_name")
    if not lanes:
        raise ValueError("feature suite requires at least one lane")
    lane_entries: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, (feature_id, path) in enumerate(lanes):
        fid = _require_str(feature_id, name=f"lanes[{index}].feature_id")
        if fid in seen:
            raise ValueError(f"duplicate feature_id: {fid}")
        seen.add(fid)
        manifest = _validate_lane_manifest(path)
        manifest_path = _relative_to_base(path, base_dir)
        lane_entries.append(
            {
                "feature_id": fid,
                "manifest_path": manifest_path,
                "chain_id": manifest["chain_id"],
                "from_height": manifest.get("from_height", 1),
                "to_height": manifest.get("to_height"),
                "bundle_kind": manifest.get("bundle_kind", "bootstrap"),
                "profile_path": _optional_relative_to_base(manifest.get("profile_path"), base_dir),
                "mirror_index_path": _optional_relative_to_base(manifest.get("mirror_index_path"), base_dir),
            }
        )

    required = sorted(_require_str(item, name="required_features[]") for item in required_features)
    missing_required = sorted(feature for feature in required if feature not in seen)
    if missing_required:
        raise ValueError(f"required feature lanes missing: {missing_required}")

    body = {
        "schema": FEATURE_SUITE_SCHEMA_V0,
        "suite_name": name,
        "required_features": required,
        "feature_count": len(lane_entries),
        "features": lane_entries,
    }
    return {**body, "feature_suite_hash": hash_v0("feature_suite_v0", body)}


def validate_feature_suite_manifest_v0(
    suite: Mapping[str, Any],
    *,
    base_dir: Path | None = None,
) -> None:
    obj = _require_mapping(suite, name="suite")
    if obj.get("schema") != FEATURE_SUITE_SCHEMA_V0:
        raise ValueError("feature suite schema mismatch")
    suite_name = _require_str(obj.get("suite_name"), name="suite_name")
    required_features = obj.get("required_features")
    if not isinstance(required_features, list):
        raise TypeError("required_features must be a list")
    feature_count = obj.get("feature_count")
    if not isinstance(feature_count, int) or isinstance(feature_count, bool) or feature_count <= 0:
        raise ValueError("feature_count must be a positive int")
    features = obj.get("features")
    if not isinstance(features, list):
        raise TypeError("features must be a list")
    if len(features) != feature_count:
        raise ValueError("feature_count mismatch")
    normalized_features: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, raw in enumerate(features):
        feature = dict(_require_mapping(raw, name=f"features[{index}]"))
        feature_id = _require_str(feature.get("feature_id"), name=f"features[{index}].feature_id")
        if feature_id in seen:
            raise ValueError(f"duplicate feature_id: {feature_id}")
        seen.add(feature_id)
        manifest_path = _require_str(feature.get("manifest_path"), name=f"features[{index}].manifest_path")
        resolved_path = _resolve_lane_path(manifest_path, base_dir)
        _validate_lane_manifest(resolved_path)
        normalized_features.append(feature)

    missing_required = sorted(feature for feature in required_features if feature not in seen)
    if missing_required:
        raise ValueError(f"required feature lanes missing: {missing_required}")

    body = {
        "schema": FEATURE_SUITE_SCHEMA_V0,
        "suite_name": suite_name,
        "required_features": required_features,
        "feature_count": feature_count,
        "features": normalized_features,
    }
    expected = {**body, "feature_suite_hash": hash_v0("feature_suite_v0", body)}
    if dict(obj) != expected:
        raise ValueError("feature suite binding mismatch")


def validate_feature_suite_manifest_digest_v0(suite: Mapping[str, Any]) -> None:
    """Validate a feature-suite manifest hash without dereferencing lane paths.

    This is the right check for portable public-status objects. Operators may
    unpack the same bundle under different local paths, while the public status
    only needs the suite's canonical content hash.
    """

    obj = _require_mapping(suite, name="suite")
    if obj.get("schema") != FEATURE_SUITE_SCHEMA_V0:
        raise ValueError("feature suite schema mismatch")
    suite_name = _require_str(obj.get("suite_name"), name="suite_name")
    required_features_raw = obj.get("required_features")
    if not isinstance(required_features_raw, list):
        raise TypeError("required_features must be a list")
    required_features = [_require_str(item, name="required_features[]") for item in required_features_raw]
    if required_features != sorted(required_features):
        raise ValueError("required_features must be sorted")
    feature_count = obj.get("feature_count")
    if not isinstance(feature_count, int) or isinstance(feature_count, bool) or feature_count <= 0:
        raise ValueError("feature_count must be a positive int")
    features = obj.get("features")
    if not isinstance(features, list):
        raise TypeError("features must be a list")
    if len(features) != feature_count:
        raise ValueError("feature_count mismatch")

    seen: set[str] = set()
    normalized_features: list[dict[str, Any]] = []
    for index, raw in enumerate(features):
        feature = dict(_require_mapping(raw, name=f"features[{index}]"))
        feature_id = _require_str(feature.get("feature_id"), name=f"features[{index}].feature_id")
        if feature_id in seen:
            raise ValueError(f"duplicate feature_id: {feature_id}")
        seen.add(feature_id)
        _require_str(feature.get("manifest_path"), name=f"features[{index}].manifest_path")
        _require_str(feature.get("chain_id"), name=f"features[{index}].chain_id")
        normalized_features.append(feature)

    missing_required = sorted(feature for feature in required_features if feature not in seen)
    if missing_required:
        raise ValueError(f"required feature lanes missing: {missing_required}")

    body = {
        "schema": FEATURE_SUITE_SCHEMA_V0,
        "suite_name": suite_name,
        "required_features": required_features,
        "feature_count": feature_count,
        "features": normalized_features,
    }
    expected = {**body, "feature_suite_hash": hash_v0("feature_suite_v0", body)}
    if dict(obj) != expected:
        raise ValueError("feature suite binding mismatch")
