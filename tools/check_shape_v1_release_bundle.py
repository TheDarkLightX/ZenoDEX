from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.cantor_shapeforge_bridge_report import SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA
from tools.build_shape_v1_release_bundle import (
    SHAPE_V1_RELEASE_BUNDLE_SCHEMA,
    build_shape_v1_release_bundle,
)
from tools.check_shape_v1_ratchet import SHAPE_V1_RATCHET_REPORT_SCHEMA


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_json(payload: dict[str, Any]) -> str:
    return _sha256_bytes((json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8"))


def _load_path(payload: dict[str, Any], key: str) -> Path:
    raw = payload.get(key)
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError(f"bundle field {key!r} must be a nonempty string path")
    path = Path(raw)
    if not path.exists():
        raise ValueError(f"bundle path {key!r} does not exist: {path}")
    return path.resolve()


def verify_shape_v1_release_bundle_payload(
    payload: dict[str, Any],
    *,
    require_current: bool = False,
) -> tuple[bool, str | None]:
    try:
        if payload.get("schema") != SHAPE_V1_RELEASE_BUNDLE_SCHEMA:
            return False, "unexpected SHAPE_V1 release bundle schema"

        artifact_sha256 = payload.get("artifact_sha256")
        if not isinstance(artifact_sha256, dict):
            return False, "bundle field 'artifact_sha256' must be an object"
        for key in (
            "manifest",
            "target_shapes",
            "world_model",
            "negative_knowledge",
            "ratchet_report",
            "cantor_bridge_report",
        ):
            value = artifact_sha256.get(key)
            if not isinstance(value, str) or len(value) != 64:
                return False, f"bundle digest {key!r} must be a 64-char sha256 hex string"

        ratchet_report = payload.get("ratchet_report")
        if not isinstance(ratchet_report, dict):
            return False, "bundle field 'ratchet_report' must be an object"
        if ratchet_report.get("schema") != SHAPE_V1_RATCHET_REPORT_SCHEMA:
            return False, "unexpected SHAPE_V1 ratchet report schema"
        if ratchet_report.get("ok") is not True:
            return False, "SHAPE_V1 ratchet report is not ok"

        bridge_report = payload.get("cantor_bridge_report")
        if not isinstance(bridge_report, dict):
            return False, "bundle field 'cantor_bridge_report' must be an object"
        if bridge_report.get("schema") != SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA:
            return False, "unexpected Cantor bridge report schema"
        if bridge_report.get("backend_invariance", {}).get("payload_equal") is not True:
            return False, "Cantor bridge report backend invariance is not satisfied"

        manifest_path = _load_path(payload, "manifest_path")
        target_shapes_path = _load_path(payload, "target_shapes_path")
        world_model_path = _load_path(payload, "world_model_path")
        negative_knowledge_path = _load_path(payload, "negative_knowledge_path")
        ratchet_report_path = _load_path(payload, "ratchet_report_path")
        cantor_bridge_report_path = _load_path(payload, "cantor_bridge_report_path")

        ratchet_manifest_path = Path(str(ratchet_report.get("manifest_path", ""))).resolve()
        ratchet_target_shapes_path = Path(str(ratchet_report.get("target_shapes_path", ""))).resolve()
        ratchet_world_model_path = Path(str(ratchet_report.get("world_model_path", ""))).resolve()
        bridge_world_model_path = Path(str(bridge_report.get("world_model_path", ""))).resolve()

        if manifest_path != ratchet_manifest_path:
            return False, "bundle manifest path does not match ratchet report"
        if target_shapes_path != ratchet_target_shapes_path:
            return False, "bundle target shapes path does not match ratchet report"
        if world_model_path != ratchet_world_model_path:
            return False, "bundle world model path does not match ratchet report"
        if world_model_path != bridge_world_model_path:
            return False, "bundle world model path does not match bridge report"

        if _sha256_bytes(manifest_path.read_bytes()) != artifact_sha256["manifest"]:
            return False, "bundle manifest sha256 does not match file content"
        if _sha256_bytes(target_shapes_path.read_bytes()) != artifact_sha256["target_shapes"]:
            return False, "bundle target_shapes sha256 does not match file content"
        if _sha256_bytes(world_model_path.read_bytes()) != artifact_sha256["world_model"]:
            return False, "bundle world_model sha256 does not match file content"
        if _sha256_bytes(negative_knowledge_path.read_bytes()) != artifact_sha256["negative_knowledge"]:
            return False, "bundle negative_knowledge sha256 does not match file content"
        if _sha256_json(ratchet_report) != artifact_sha256["ratchet_report"]:
            return False, "bundle ratchet_report sha256 does not match nested payload"
        if _sha256_json(bridge_report) != artifact_sha256["cantor_bridge_report"]:
            return False, "bundle cantor_bridge_report sha256 does not match nested payload"

        ratchet_report_file = json.loads(ratchet_report_path.read_text(encoding="utf-8"))
        bridge_report_file = json.loads(cantor_bridge_report_path.read_text(encoding="utf-8"))
        if ratchet_report_file != ratchet_report:
            return False, "bundle ratchet report payload does not match referenced file"
        if bridge_report_file != bridge_report:
            return False, "bundle Cantor bridge report payload does not match referenced file"

        if require_current:
            expected = build_shape_v1_release_bundle(
                ratchet_report_path=ratchet_report_path,
                cantor_bridge_report_path=cantor_bridge_report_path,
            )
            if expected != payload:
                return False, "bundle does not match current deterministic release bundle construction"
    except ValueError as exc:
        return False, str(exc)
    return True, None


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Fail-closed verifier for a SHAPE_V1 release bundle JSON.")
    parser.add_argument("bundle", type=Path, help="Path to the SHAPE_V1 release bundle JSON")
    parser.add_argument(
        "--require-current",
        action="store_true",
        help="Require the bundle to match the current deterministic release bundle construction exactly",
    )
    args = parser.parse_args(argv)

    payload = json.loads(args.bundle.read_text(encoding="utf-8"))
    ok, err = verify_shape_v1_release_bundle_payload(payload, require_current=bool(args.require_current))
    if not ok:
        print(err or "release bundle verification failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
