from __future__ import annotations

import copy
import json

from tools.check_zenodex_host_independent_coverage import (
    DEFAULT_MANIFEST,
    main,
    validate_host_independent_coverage_v0,
)


def _manifest() -> dict[str, object]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def _surface(manifest: dict[str, object], surface_id: str) -> dict[str, object]:
    surfaces = manifest["critical_surfaces"]
    assert isinstance(surfaces, list)
    for surface in surfaces:
        assert isinstance(surface, dict)
        if surface.get("id") == surface_id:
            return surface
    raise AssertionError(f"missing surface {surface_id}")


def test_host_independent_coverage_accepts_default_manifest() -> None:
    report = validate_host_independent_coverage_v0(_manifest())

    assert report["ok"] is True
    assert report["surface_count"] == 10
    assert report["full_node_open_surfaces"] == []
    assert report["succinct_open_surfaces"] == ["full_zk_execution_for_all_value_moving_surfaces"]
    spot = next(item for item in report["surfaces"] if item["id"] == "spot_intent_admission_and_settlement")
    assert spot["public_data_availability"] == "public_inputs_and_replay_artifacts"


def test_host_independent_coverage_rejects_docker_correctness_boundary() -> None:
    manifest = _manifest()
    boundary = copy.deepcopy(manifest["claim_boundary"])
    assert isinstance(boundary, dict)
    boundary["docker_is_correctness_boundary"] = True
    manifest["claim_boundary"] = boundary

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert "docker_is_correctness_boundary must be false" in report["errors"]


def test_host_independent_coverage_rejects_metadata_as_transition_coverage() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "proof_required_profile_metadata_and_report_replay"))
    surface["counts_as_transition_coverage"] = True
    surfaces = list(manifest["critical_surfaces"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(surfaces) if item["id"] == surface["id"])  # type: ignore[index]
    surfaces[index] = surface
    manifest["critical_surfaces"] = surfaces

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("metadata/report/checkpoint replay must not count" in err for err in report["errors"])


def test_host_independent_coverage_rejects_transition_without_public_data() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "spot_intent_admission_and_settlement"))
    surface["public_data_availability"] = "metadata_only_non_transition"
    surfaces = list(manifest["critical_surfaces"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(surfaces) if item["id"] == surface["id"])  # type: ignore[index]
    surfaces[index] = surface
    manifest["critical_surfaces"] = surfaces

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert any(
        "deterministic transition coverage requires public_inputs_and_replay_artifacts" in err
        for err in report["errors"]
    )


def test_host_independent_coverage_rejects_open_full_node_surface() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "upba_bounded_grid_and_exact_out_certificates"))
    surface["coverage_status"] = "open"
    surface["verifier_mode"] = "fail_closed_blocked"
    surface["counts_as_transition_coverage"] = False
    surfaces = list(manifest["critical_surfaces"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(surfaces) if item["id"] == surface["id"])  # type: ignore[index]
    surfaces[index] = surface
    manifest["critical_surfaces"] = surfaces

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert "upba_bounded_grid_and_exact_out_certificates" in report["full_node_open_surfaces"]
    assert any("full_node_host_independence cannot be supported" in err for err in report["errors"])


def test_host_independent_coverage_rejects_missing_claim_binding() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "spot_intent_admission_and_settlement"))
    surface["claim_ids"] = ["py:missing:claim"]
    surfaces = list(manifest["critical_surfaces"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(surfaces) if item["id"] == surface["id"])  # type: ignore[index]
    surfaces[index] = surface
    manifest["critical_surfaces"] = surfaces

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("claim_ids missing or unsupported: py:missing:claim" in err for err in report["errors"])


def test_host_independent_coverage_rejects_unknown_proof_surface() -> None:
    manifest = _manifest()
    surface = copy.deepcopy(_surface(manifest, "spot_v1_risc0_supported_transition_kernel"))
    proof_ids = list(surface["proof_surface_ids"])  # type: ignore[arg-type]
    proof_ids.append("risc0_missing_surface")
    surface["proof_surface_ids"] = proof_ids
    surfaces = list(manifest["critical_surfaces"])  # type: ignore[arg-type]
    index = next(i for i, item in enumerate(surfaces) if item["id"] == surface["id"])  # type: ignore[index]
    surfaces[index] = surface
    manifest["critical_surfaces"] = surfaces

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("proof_surface_ids missing from proof coverage matrix: risc0_missing_surface" in err for err in report["errors"])


def test_host_independent_coverage_rejects_succinct_everything_overclaim() -> None:
    manifest = _manifest()
    boundary = copy.deepcopy(manifest["claim_boundary"])
    assert isinstance(boundary, dict)
    boundary["succinct_everything_host_independence"] = "supported"
    manifest["claim_boundary"] = boundary

    report = validate_host_independent_coverage_v0(manifest)

    assert report["ok"] is False
    assert any("succinct_everything_host_independence cannot be supported" in err for err in report["errors"])


def test_host_independent_coverage_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "host_independent_coverage.json"
    manifest_path.write_text(json.dumps(_manifest(), indent=2, sort_keys=True), encoding="utf-8")

    code = main(["--manifest", str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.host_independent_coverage_report.v0"
