from __future__ import annotations

import json
from pathlib import Path

from tools.check_shape_v1_ratchet import (
    SHAPE_V1_RATCHET_REPORT_SCHEMA,
    DEFAULT_MANIFEST,
    DEFAULT_TARGET_SHAPES,
    DEFAULT_WORLD_MODEL,
    check_shape_v1_ratchet,
)


def test_shape_v1_ratchet_matches_current_baseline() -> None:
    report = check_shape_v1_ratchet()
    assert report["schema"] == SHAPE_V1_RATCHET_REPORT_SCHEMA
    assert report["ok"] is True
    by_id = {result["target_shape_id"]: result for result in report["results"]}
    assert by_id["shape_pp_candidate_v1"]["support_count"] == 10
    assert by_id["shape_pp_candidate_v1"]["blocked_count"] == 0
    assert by_id["dex_kernel_candidate_v1"]["support_count"] == 6
    assert by_id["runtime_boundary_candidate_v1"]["support_count"] == 5
    assert report["cantor_shape_promotion"]["mapped_surface_count"] == 4
    assert report["cantor_shape_promotion"]["unmapped_surface_count"] == 0


def test_shape_v1_ratchet_requires_manifest_entries(tmp_path: Path) -> None:
    broken_manifest = tmp_path / "SHAPE_V1.md"
    broken_manifest.write_text("# broken\n`cbc_validity`\n", encoding="utf-8")
    try:
        check_shape_v1_ratchet(
            target_shapes_path=DEFAULT_TARGET_SHAPES,
            world_model_path=DEFAULT_WORLD_MODEL,
            manifest_path=broken_manifest,
        )
    except ValueError as exc:
        assert "missing clause manifest entry" in str(exc)
    else:
        raise AssertionError("expected manifest check to fail")


def test_shape_v1_ratchet_writes_cantor_bridge_report(tmp_path: Path) -> None:
    report_path = tmp_path / 'cantor-bridge.json'
    report = check_shape_v1_ratchet(cantor_bridge_report_path=report_path)
    assert report['cantor_bridge_report_path'] == str(report_path)
    payload = json.loads(report_path.read_text(encoding='utf-8'))
    assert payload['mapped_surface_count'] == 4
    assert payload['backend_invariance']['payload_equal'] is True


def test_shape_v1_ratchet_writes_report_json(tmp_path: Path) -> None:
    report_path = tmp_path / 'shape-v1-ratchet.json'
    report = check_shape_v1_ratchet(output_report_path=report_path)
    assert report_path.exists()
    payload = json.loads(report_path.read_text(encoding='utf-8'))
    assert payload['ok'] is True
    assert payload['cantor_shape_promotion']['mapped_surface_count'] == 4
    assert payload['cantor_bridge_report_path'] is None


def test_shape_v1_manifest_exists() -> None:
    assert DEFAULT_MANIFEST.exists()
