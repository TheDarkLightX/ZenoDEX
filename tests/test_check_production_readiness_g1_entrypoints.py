from __future__ import annotations

import json
from pathlib import Path

from tools.check_production_readiness_g1_entrypoints import (
    DEFAULT_OUTPUT,
    build_document,
    check_artifact,
)


def test_exact_subject_entrypoint_audit_is_research_only() -> None:
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["command_route_count"] == 33
    assert report["declared_production_writer_count"] == 0
    assert report["writer_inventory_unmounted_entrypoint_count"] == 18
    assert report["surface_count"] == 12


def test_every_command_has_frozen_handler_and_no_production_writer() -> None:
    document = build_document()
    routes = document["command_routes"]

    assert len(routes) == 33
    assert all(route["core_transition"].startswith("src/core/m6_safe_mount_transition_v1.py:") for route in routes)
    assert all(route["candidate_surface"].endswith(":run_m6_transition_v1") for route in routes)
    assert all(route["mounted_entrypoint"] == "UNMOUNTED_RESEARCH_ONLY" for route in routes)
    assert all(route["production_writer_declared"] is False for route in routes)
    assert document["g1_exit_gate"]["command_routes_with_declared_production_writer"] == 0


def test_writer_inventory_reconciles_25_entries_and_18_unmounted() -> None:
    inventory = build_document()["writer_inventory"]

    assert inventory["entrypoint_count"] == 25
    assert inventory["unmounted_entrypoint_count"] == 18
    assert inventory["coverage_row_count"] == 25
    assert inventory["open_coverage_count"] == 25
    assert inventory["release_ready"] is False
    assert inventory["m6_production_mounted"] is False
    assert inventory["production_authority"] is False
    assert inventory["mount_status_counts"] == {
        "M6_RESEARCH_ONLY": 6,
        "SEPARATE_RESEARCH_NOT_M6": 1,
        "UNMOUNTED_LEGACY": 18,
    }
    assert inventory["declared_production_entrypoint_ids"] == []


def test_research_publication_and_effect_surfaces_are_classified() -> None:
    surfaces = {surface["id"]: surface for surface in build_document()["surface_inventory"]}

    assert surfaces["m6_reference_commit_direct"]["status"] == "M6_RESEARCH_ONLY"
    assert surfaces["m6_research_durable_direct"]["status"] == "M6_RESEARCH_ONLY"
    assert surfaces["m6_finality_verifier_port"]["status"] == "PORT_ONLY_NO_IMPLEMENTATION"
    assert surfaces["m6_outbox_delivery"]["status"] == "M6_RESEARCH_ONLY_NO_STATE_WRITER"
    assert (
        build_document()["production_publication_capability"]["dynamic_runtime_reachability"]
        == "UNKNOWN_NOT_CHECKED"
    )


def test_falsely_declaring_a_production_writer_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["production_publication_capability"]["declared_production_entrypoint_count"] = 1
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["production_ready"] is False


def test_falsely_mounting_a_command_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["command_routes"][0]["mounted_entrypoint"] = "MOUNTED_PRODUCTION"
    candidate = tmp_path / "candidate.json"
    candidate.write_text(json.dumps(artifact), encoding="utf-8")

    report = check_artifact(candidate)

    assert report["ok"] is False
    assert report["declared_production_writer_count"] == 0
