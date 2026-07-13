#!/usr/bin/env python3
# ruff: noqa: E402
"""Replay a public ZenoLedger bundle as an independent operator."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
from src.integration.zeno_ledger_testnet_status import (
    build_testnet_status_v0,
    validate_testnet_status_v0,
)
from src.integration.zeno_ledger_v0 import ZERO_ROOT_V0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tools.zeno_ledger_run_feature_suite import run_feature_suite_v0
from tools.zeno_ledger_run_manifest import run_manifest_v0
from tools.zeno_ledger_verify import REPLAY_BOUND_MODE, verify_zeno_ledger_v0

REPORT_SCHEMA = "zenodex.zeno_ledger.operator_rehearsal_report.v0"
PUBLIC_MANIFEST_SCHEMA = "zenodex.zeno_ledger.public_testnet_bundle.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _is_safe_relative(path_text: str) -> bool:
    path = Path(path_text)
    return path_text != "" and not path.is_absolute() and ".." not in path.parts


def _known_bundle_path(bundle_root: Path, *parts: str) -> Path:
    return bundle_root.joinpath(*parts)


def _resolve_bundle_path(
    raw: object,
    *,
    bundle_root: Path,
    fallback: Path,
) -> Path:
    if isinstance(raw, str) and raw:
        path = Path(raw)
        if path.exists():
            return path
        if _is_safe_relative(raw):
            candidate = bundle_root / path
            if candidate.exists():
                return candidate
    if fallback.exists():
        return fallback
    raise ValueError(f"bundle path is missing: {fallback}")


def _rewrite_value(value: object, *, old_root: Path, new_root: Path) -> object:
    if isinstance(value, list):
        if value and isinstance(value[0], str) and Path(value[0]).is_absolute():
            first = Path(value[0])
            if first.name.startswith("python"):
                return [sys.executable, *[_rewrite_value(item, old_root=old_root, new_root=new_root) for item in value[1:]]]
        return [_rewrite_value(item, old_root=old_root, new_root=new_root) for item in value]
    if isinstance(value, dict):
        return {key: _rewrite_value(item, old_root=old_root, new_root=new_root) for key, item in value.items()}
    if isinstance(value, str):
        path = Path(value)
        if path.is_absolute():
            try:
                rel = path.resolve().relative_to(old_root.resolve())
            except ValueError:
                if path.name.startswith("python"):
                    return sys.executable
                return value
            return str(new_root / rel)
        return value
    return value


def _contains_absolute_path(value: object) -> bool:
    if isinstance(value, list):
        return any(_contains_absolute_path(item) for item in value)
    if isinstance(value, dict):
        return any(_contains_absolute_path(item) for item in value.values())
    if isinstance(value, str):
        return Path(value).is_absolute()
    return False


def _relocate_manifest(
    *,
    source_manifest_path: Path,
    old_root: Path,
    new_root: Path,
    out_path: Path,
) -> Path:
    manifest = _load_json_object(source_manifest_path)
    relocated = _rewrite_value(dict(manifest), old_root=old_root, new_root=new_root)
    _write_json(out_path, relocated)
    return out_path


def _bundle_old_root_from_manifest_path(raw_path: object, *, fallback_current_path: Path) -> Path:
    if isinstance(raw_path, str) and raw_path:
        path = Path(raw_path)
        if path.name == fallback_current_path.name:
            return path.parent
    return fallback_current_path.parent


def _resolve_feature_manifest_path(
    *,
    raw_path: str,
    new_suite_root: Path,
) -> Path:
    raw = Path(raw_path)
    if raw.is_absolute():
        raise ValueError("portable feature suite manifests must use relative feature paths")
    if not _is_safe_relative(raw_path):
        raise ValueError(f"unsafe feature manifest path: {raw_path}")
    return new_suite_root / raw


def _old_lane_root_from_manifest(manifest: Mapping[str, Any], *, current_manifest_path: Path) -> Path:
    for key in ("ledger_out_dir", "profile_path", "first_body_path"):
        raw = manifest.get(key)
        if isinstance(raw, str) and raw:
            path = Path(raw)
            if path.is_absolute():
                if key == "ledger_out_dir":
                    return path.parent
                if key == "profile_path":
                    return path.parent
                if key == "first_body_path":
                    return path.parent.parent
    return current_manifest_path.parent


def _feature_suite_needs_relocation(source_suite_path: Path) -> bool:
    suite = dict(_load_json_object(source_suite_path))
    if _contains_absolute_path(suite):
        return True
    features = suite.get("features")
    if not isinstance(features, list):
        raise ValueError("feature suite must contain features list")

    for raw_feature in features:
        feature = dict(raw_feature)
        raw_manifest_path = feature.get("manifest_path")
        if not isinstance(raw_manifest_path, str) or raw_manifest_path == "":
            raise ValueError("feature manifest_path must be a non-empty string")
        source_manifest_path = _resolve_feature_manifest_path(
            raw_path=raw_manifest_path,
            new_suite_root=source_suite_path.parent,
        )
        if _contains_absolute_path(_load_json_object(source_manifest_path)):
            return True
    return False


def _relocate_feature_suite(
    *,
    source_suite_path: Path,
    new_suite_root: Path,
    out_dir: Path,
) -> Path:
    suite = dict(_load_json_object(source_suite_path))
    features = suite.get("features")
    if not isinstance(features, list):
        raise ValueError("feature suite must contain features list")

    for raw_feature in features:
        feature = dict(raw_feature)
        raw_manifest_path = feature.get("manifest_path")
        if not isinstance(raw_manifest_path, str) or raw_manifest_path == "":
            raise ValueError("feature manifest_path must be a non-empty string")
        source_manifest_path = _resolve_feature_manifest_path(
            raw_path=raw_manifest_path,
            new_suite_root=new_suite_root,
        )
        source_manifest = _load_json_object(source_manifest_path)
        old_lane_root = _old_lane_root_from_manifest(source_manifest, current_manifest_path=source_manifest_path)
        relocated_manifest_path = out_dir / "core_features" / raw_manifest_path
        _relocate_manifest(
            source_manifest_path=source_manifest_path,
            old_root=old_lane_root,
            new_root=source_manifest_path.parent,
            out_path=relocated_manifest_path,
        )

    relocated_suite_path = out_dir / "core_features" / source_suite_path.name
    _write_json(relocated_suite_path, suite)
    return relocated_suite_path


def run_operator_rehearsal_v0(
    *,
    bundle_root: Path,
    operator_id: str,
    out_dir: Path,
    observed_time_ms: int | None,
    peer_watcher_attestation_paths: list[Path],
) -> dict[str, Any]:
    bundle = bundle_root.resolve()
    manifest_path = bundle / "public_testnet_manifest.json"
    public_manifest = dict(_load_json_object(manifest_path))
    if public_manifest.get("schema") != PUBLIC_MANIFEST_SCHEMA:
        raise ValueError("public testnet manifest schema mismatch")

    bootstrap_manifest_path = _resolve_bundle_path(
        public_manifest.get("bootstrap_manifest_path"),
        bundle_root=bundle,
        fallback=_known_bundle_path(bundle, "bootstrap", "manifest.json"),
    )
    bootstrap_manifest = dict(_load_json_object(bootstrap_manifest_path))
    bootstrap_root = bootstrap_manifest_path.parent
    old_bootstrap_root = _bundle_old_root_from_manifest_path(
        public_manifest.get("bootstrap_manifest_path"),
        fallback_current_path=bootstrap_manifest_path,
    )
    relocated_bootstrap_manifest_path = (
        _relocate_manifest(
            source_manifest_path=bootstrap_manifest_path,
            old_root=old_bootstrap_root,
            new_root=bootstrap_root,
            out_path=out_dir / "bootstrap_manifest.relocated.json",
        )
        if _contains_absolute_path(bootstrap_manifest)
        else bootstrap_manifest_path
    )

    bootstrap_run_report = run_manifest_v0(manifest_path=relocated_bootstrap_manifest_path, cwd=ROOT)
    if bootstrap_run_report.get("ok") is not True:
        raise ValueError("bootstrap replay rejected")

    core_suite_path = _resolve_bundle_path(
        public_manifest.get("core_suite_path"),
        bundle_root=bundle,
        fallback=_known_bundle_path(bundle, "core_features", "feature_suite.json"),
    )
    relocated_suite_path = (
        _relocate_feature_suite(
            source_suite_path=core_suite_path,
            new_suite_root=core_suite_path.parent,
            out_dir=out_dir,
        )
        if _feature_suite_needs_relocation(core_suite_path)
        else core_suite_path
    )
    core_suite_run_report = run_feature_suite_v0(suite_path=relocated_suite_path, cwd=ROOT)
    if core_suite_run_report.get("ok") is not True:
        raise ValueError("core feature replay rejected")

    headers_dir = bootstrap_root / "ledger" / "headers"
    bodies_dir = bootstrap_root / "ledger" / "bodies"
    checkpoints_dir = bootstrap_root / "ledger" / "checkpoints"
    profile_path = bootstrap_root / "profile.json"
    verify_report = verify_zeno_ledger_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        profile_path=profile_path,
        from_height=1,
        to_height=5,
        trusted_prev_header_hash=ZERO_ROOT_V0,
        mode=REPLAY_BOUND_MODE,
        pre_snapshots_dir=bootstrap_root / "ledger" / "pre_snapshots",
        engine_config_path=bootstrap_root / "engine_config.json",
        require_rejection_receipt_replay=True,
    )
    if verify_report.get("ok") is not True:
        raise ValueError("operator verify rejected")
    profile = _load_json_object(profile_path)
    observation_ms = (
        int(observed_time_ms)
        if observed_time_ms is not None
        else int(bootstrap_manifest.get("time_ms", 0)) + 10_000
    )
    operator_attestation = build_watcher_attestation_v0(
        verify_report=verify_report,
        watcher_id=operator_id,
        observed_time_ms=observation_ms,
        verifier_ref="tools/zeno_ledger_operator_rehearsal.py@v0",
        profile=profile,
    )
    operator_attestation_path = out_dir / f"{operator_id}.watcher_attestation.json"
    _write_json(operator_attestation_path, operator_attestation)

    mirror_index_path = _resolve_bundle_path(
        bootstrap_manifest.get("mirror_index_path"),
        bundle_root=bootstrap_root,
        fallback=bootstrap_root / "mirror_index.json",
    )
    mirror_index = _load_json_object(mirror_index_path)
    validate_mirror_index_v0(index=mirror_index, mirror_root=bootstrap_root)

    peer_attestations = [_load_json_object(path) for path in peer_watcher_attestation_paths]
    watcher_attestations = [*peer_attestations, operator_attestation]
    feature_suite = _load_json_object(core_suite_path)
    status = build_testnet_status_v0(
        network_id=str(public_manifest["network_id"]),
        mirror_index=mirror_index,
        mirror_root=bootstrap_root,
        watcher_attestations=watcher_attestations,
        feature_suite=feature_suite,
        feature_suite_run_report=core_suite_run_report,
    )
    status_path = out_dir / "combined_testnet_status.json"
    _write_json(status_path, status)
    validate_testnet_status_v0(
        status=status,
        mirror_index=mirror_index,
        mirror_root=bootstrap_root,
        watcher_attestations=watcher_attestations,
        feature_suite=feature_suite,
        feature_suite_run_report=core_suite_run_report,
    )

    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "bundle_root": str(bundle),
        "operator_id": operator_id,
        "operator_attestation_path": str(operator_attestation_path),
        "operator_attestation_hash": operator_attestation["attestation_hash"],
        "peer_watcher_count": len(peer_attestations),
        "combined_watcher_count": status["watcher_count"],
        "combined_testnet_status_path": str(status_path),
        "combined_testnet_status_hash": status["testnet_status_hash"],
        "mirror_index_hash": mirror_index["mirror_index_hash"],
        "feature_suite_hash": feature_suite["feature_suite_hash"],
        "covered_features": core_suite_run_report["covered_features"],
        "last_header_hash": verify_report["last_header_hash"],
        "last_app_hash": verify_report["last_app_hash"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Replay a public ZenoLedger bundle as an independent operator")
    parser.add_argument("--bundle-root", required=True, type=Path)
    parser.add_argument("--operator-id", required=True)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--observed-time-ms", type=int)
    parser.add_argument("--peer-watcher-attestation", action="append", default=[], type=Path)
    args = parser.parse_args(argv)

    try:
        report = run_operator_rehearsal_v0(
            bundle_root=args.bundle_root,
            operator_id=args.operator_id,
            out_dir=args.out_dir,
            observed_time_ms=args.observed_time_ms,
            peer_watcher_attestation_paths=list(args.peer_watcher_attestation),
        )
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
