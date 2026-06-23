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
from tools.check_shape_v1_ratchet import SHAPE_V1_RATCHET_REPORT_SCHEMA
from tools.shapeforge_validate import _resolve_linked_path  # type: ignore

SHAPE_V1_RELEASE_BUNDLE_SCHEMA = "zenodex/shape-v1-release-bundle/v1"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_json(payload: dict[str, Any]) -> str:
    return _sha256_bytes((json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8"))


def _resolve(base: Path, raw: str) -> Path:
    resolved = _resolve_linked_path(base, raw)
    if resolved is None:
        raise ValueError(f"could not resolve linked path {raw!r} from {base}")
    return resolved


def build_shape_v1_release_bundle(
    *,
    ratchet_report_path: Path,
    cantor_bridge_report_path: Path,
) -> dict[str, Any]:
    ratchet_report = _load_json(ratchet_report_path)
    bridge_report = _load_json(cantor_bridge_report_path)

    if ratchet_report.get("schema") != SHAPE_V1_RATCHET_REPORT_SCHEMA:
        raise ValueError("unexpected SHAPE_V1 ratchet report schema")
    if ratchet_report.get("ok") is not True:
        raise ValueError("SHAPE_V1 ratchet report is not ok")
    if bridge_report.get("schema") != SHAPEFORGE_CANTOR_BRIDGE_REPORT_SCHEMA:
        raise ValueError("unexpected Cantor bridge report schema")
    if bridge_report.get("backend_invariance", {}).get("payload_equal") is not True:
        raise ValueError("Cantor bridge report backend invariance is not satisfied")

    ratchet_world_model = Path(str(ratchet_report["world_model_path"])).resolve()
    bridge_world_model = Path(str(bridge_report["world_model_path"])).resolve()
    if ratchet_world_model != bridge_world_model:
        raise ValueError("ratchet report world model path does not match bridge report world model path")

    ratchet_mapped = int(ratchet_report["cantor_shape_promotion"]["mapped_surface_count"])
    bridge_mapped = int(bridge_report["mapped_surface_count"])
    if ratchet_mapped != bridge_mapped:
        raise ValueError("ratchet mapped_surface_count does not match bridge report")

    ratchet_bundle_sha = str(ratchet_report["cantor_shape_promotion"]["shared_bundle_sha256"])
    bridge_bundle_sha = str(bridge_report["backend_invariance"]["shared_bundle_sha256"])
    if ratchet_bundle_sha != bridge_bundle_sha:
        raise ValueError("ratchet shared bundle sha256 does not match bridge report")

    target_shapes_path = Path(str(ratchet_report["target_shapes_path"]))
    target_shapes = _load_json(target_shapes_path)
    negative_knowledge_path = _resolve(target_shapes_path, str(target_shapes["negative_knowledge_path"]))
    manifest_path = Path(str(ratchet_report["manifest_path"]))

    return {
        "schema": SHAPE_V1_RELEASE_BUNDLE_SCHEMA,
        "manifest_path": str(manifest_path),
        "target_shapes_path": str(target_shapes_path),
        "world_model_path": str(ratchet_world_model),
        "negative_knowledge_path": str(negative_knowledge_path),
        "ratchet_report_path": str(ratchet_report_path),
        "cantor_bridge_report_path": str(cantor_bridge_report_path),
        "artifact_sha256": {
            "manifest": _sha256_bytes(manifest_path.read_bytes()),
            "target_shapes": _sha256_bytes(target_shapes_path.read_bytes()),
            "world_model": _sha256_bytes(ratchet_world_model.read_bytes()),
            "negative_knowledge": _sha256_bytes(negative_knowledge_path.read_bytes()),
            "ratchet_report": _sha256_json(ratchet_report),
            "cantor_bridge_report": _sha256_json(bridge_report),
        },
        "ratchet_report": ratchet_report,
        "cantor_bridge_report": bridge_report,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a replayable SHAPE_V1 release bundle JSON from ratchet outputs.")
    parser.add_argument("--ratchet-report", type=Path, required=True, help="Path to the SHAPE_V1 ratchet report JSON")
    parser.add_argument("--cantor-bridge-report", type=Path, required=True, help="Path to the Cantor-to-ShapeForge bridge report JSON")
    parser.add_argument("--output", type=Path, required=True, help="Path to write the SHAPE_V1 release bundle JSON")
    args = parser.parse_args(argv)

    try:
        bundle = build_shape_v1_release_bundle(
            ratchet_report_path=args.ratchet_report.resolve(),
            cantor_bridge_report_path=args.cantor_bridge_report.resolve(),
        )
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
