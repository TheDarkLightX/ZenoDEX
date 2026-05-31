from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_zenodex_critical_value_surface_inventory import (
    DEFAULT_MANIFEST,
    main,
    validate_critical_value_surface_inventory_v0,
)


def _manifest() -> dict[str, object]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def _surface(manifest: dict[str, object], surface_id: str) -> dict[str, object]:
    surfaces = manifest["critical_source_surfaces"]
    assert isinstance(surfaces, list)
    for surface in surfaces:
        assert isinstance(surface, dict)
        if surface.get("id") == surface_id:
            return surface
    raise AssertionError(f"missing surface {surface_id}")


def _unsupported(manifest: dict[str, object], surface_id: str) -> dict[str, object]:
    surfaces = manifest["unsupported_source_surfaces"]
    assert isinstance(surfaces, list)
    for surface in surfaces:
        assert isinstance(surface, dict)
        if surface.get("id") == surface_id:
            return surface
    raise AssertionError(f"missing unsupported surface {surface_id}")


def _scan(manifest: dict[str, object], query_id: str) -> dict[str, object]:
    queries = manifest["source_scan_queries"]
    assert isinstance(queries, list)
    for query in queries:
        assert isinstance(query, dict)
        if query.get("id") == query_id:
            return query
    raise AssertionError(f"missing query {query_id}")


def _replace_surface(manifest: dict[str, object], surface: dict[str, object]) -> None:
    surfaces = list(manifest["critical_source_surfaces"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(surfaces) if item["id"] == surface["id"])  # type: ignore[index]
    surfaces[index] = surface
    manifest["critical_source_surfaces"] = surfaces


def test_critical_value_surface_inventory_accepts_default_manifest() -> None:
    report = validate_critical_value_surface_inventory_v0(_manifest())

    assert report["ok"] is True
    assert report["critical_source_surface_count"] == 7
    assert report["unsupported_source_surface_count"] == 1
    assert report["closure_group_count"] == 7
    assert report["mapped_closure_group_count"] == 7
    assert report["unsupported_closure_entry_count"] == 5
    assert report["mapped_unsupported_closure_entry_count"] == 5
    assert report["source_scan_query_count"] >= 6


def test_critical_value_surface_inventory_rejects_missing_closure_group_mapping() -> None:
    manifest = _manifest()
    surfaces = [
        surface
        for surface in manifest["critical_source_surfaces"]  # type: ignore[index]
        if surface["id"] != "proof_mining_reward_replay"  # type: ignore[index]
    ]
    manifest["critical_source_surfaces"] = surfaces

    report = validate_critical_value_surface_inventory_v0(manifest)

    assert report["ok"] is False
    assert any("proof_mining_reward_full_node_replay_v1" in error for error in report["errors"])


def test_critical_value_surface_inventory_rejects_missing_source_symbol() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "spot_runtime_settlement_replay"))
    surface["required_symbols"] = ["definitely_missing_apply_ops_symbol"]
    _replace_surface(manifest, surface)

    report = validate_critical_value_surface_inventory_v0(manifest)

    assert report["ok"] is False
    assert any("required symbol not found in paths: definitely_missing_apply_ops_symbol" in err for err in report["errors"])


def test_critical_value_surface_inventory_rejects_metadata_public_data() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "spot_runtime_settlement_replay"))
    surface["public_data_availability"] = "metadata_only_non_transition"
    _replace_surface(manifest, surface)

    report = validate_critical_value_surface_inventory_v0(manifest)

    assert report["ok"] is False
    assert any("deterministic_replay requires public_inputs_and_replay_artifacts" in err for err in report["errors"])
    assert any("value-moving source inventory cannot use metadata_only_non_transition" in err for err in report["errors"])


def test_critical_value_surface_inventory_rejects_missing_unsupported_entry() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_unsupported(manifest, "spot_v1_proof_required_fail_closed_inventory"))
    surface["unsupported_closure_entry_ids"] = [
        entry
        for entry in surface["unsupported_closure_entry_ids"]  # type: ignore[index]
        if entry != "spot_v1_swap_exact_out_proof_rejected"
    ]
    unsupported = list(manifest["unsupported_source_surfaces"])  # type: ignore[arg-type]
    unsupported[0] = surface
    manifest["unsupported_source_surfaces"] = unsupported

    report = validate_critical_value_surface_inventory_v0(manifest)

    assert report["ok"] is False
    assert any("spot_v1_swap_exact_out_proof_rejected" in error for error in report["errors"])


def test_critical_value_surface_inventory_rejects_scan_token_missing() -> None:
    manifest = _manifest()
    query = copy.deepcopy(_scan(manifest, "perps_value_moving_runtime"))
    query["required_tokens"] = ["missing_perps_scan_token"]
    queries = list(manifest["source_scan_queries"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(queries) if item["id"] == query["id"])  # type: ignore[index]
    queries[index] = query
    manifest["source_scan_queries"] = queries

    report = validate_critical_value_surface_inventory_v0(manifest)

    assert report["ok"] is False
    assert any("required token not found in paths: missing_perps_scan_token" in err for err in report["errors"])


def test_critical_value_surface_inventory_rejects_path_escape() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "zusd_lifecycle_replay"))
    surface["paths"] = ["../outside.py"]
    _replace_surface(manifest, surface)

    report = validate_critical_value_surface_inventory_v0(manifest)

    assert report["ok"] is False
    assert any("paths path escapes repo: ../outside.py" in err for err in report["errors"])


def test_critical_value_surface_inventory_cli_outputs_report(tmp_path: Path, capsys) -> None:
    manifest_path = tmp_path / "critical_value_surface_inventory.json"
    manifest_path.write_text(json.dumps(_manifest(), indent=2, sort_keys=True), encoding="utf-8")

    code = main(["--manifest", str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.critical_value_surface_inventory_report.v0"
