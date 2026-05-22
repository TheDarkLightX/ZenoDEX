from __future__ import annotations

import json
import tempfile
from functools import lru_cache
from pathlib import Path

from tools.build_shape_v1_release_bundle import (
    SHAPE_V1_RELEASE_BUNDLE_SCHEMA,
    build_shape_v1_release_bundle,
    main,
)
from tools.check_shape_v1_ratchet import check_shape_v1_ratchet


@lru_cache(maxsize=1)
def _artifact_paths() -> tuple[Path, Path, Path]:
    base = Path(tempfile.mkdtemp(prefix="shape-v1-release-bundle-"))
    ratchet_report = base / "shape-v1-ratchet.json"
    bridge_report = base / "cantor-bridge.json"
    check_shape_v1_ratchet(
        cantor_bridge_report_path=bridge_report,
        output_report_path=ratchet_report,
    )
    return base, ratchet_report, bridge_report


def test_build_shape_v1_release_bundle_json_ready(tmp_path: Path) -> None:
    _base, ratchet_report, bridge_report = _artifact_paths()

    bundle = build_shape_v1_release_bundle(
        ratchet_report_path=ratchet_report,
        cantor_bridge_report_path=bridge_report,
    )

    assert bundle["schema"] == SHAPE_V1_RELEASE_BUNDLE_SCHEMA
    assert bundle["ratchet_report"]["schema"] == "zenodex/shape-v1-ratchet-report/v1"
    assert bundle["cantor_bridge_report"]["backend_invariance"]["payload_equal"] is True
    assert bundle["artifact_sha256"]["ratchet_report"]
    assert bundle["artifact_sha256"]["cantor_bridge_report"]


def test_build_shape_v1_release_bundle_cli_rejects_mismatched_bridge(tmp_path: Path) -> None:
    _base, ratchet_report, bridge_report = _artifact_paths()
    bad_bridge = tmp_path / "bad-bridge.json"
    payload = json.loads(bridge_report.read_text(encoding="utf-8"))
    payload["mapped_surface_count"] = 999
    bad_bridge.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out_path = tmp_path / "bundle.json"

    assert main([
        "--ratchet-report", str(ratchet_report),
        "--cantor-bridge-report", str(bad_bridge),
        "--output", str(out_path),
    ]) == 1


def test_build_shape_v1_release_bundle_cli_writes_bundle(tmp_path: Path) -> None:
    _base, ratchet_report, bridge_report = _artifact_paths()
    out_path = tmp_path / "bundle.json"

    assert main([
        "--ratchet-report", str(ratchet_report),
        "--cantor-bridge-report", str(bridge_report),
        "--output", str(out_path),
    ]) == 0
    payload = json.loads(out_path.read_text(encoding="utf-8"))
    assert payload["schema"] == SHAPE_V1_RELEASE_BUNDLE_SCHEMA
