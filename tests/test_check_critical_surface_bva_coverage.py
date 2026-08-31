from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from tools.bva.check_critical_surface_coverage import (
    DEFAULT_MANIFEST,
    REQUIRED_BOUNDARY_CLASSES,
    CoverageManifestError,
    check_manifest,
)


def _manifest() -> dict[str, Any]:
    value = json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _write_manifest(tmp_path: Path, manifest: dict[str, Any]) -> Path:
    path = tmp_path / "coverage.json"
    path.write_text(json.dumps(manifest), encoding="utf-8")
    return path


def _first_surface(manifest: dict[str, Any]) -> dict[str, Any]:
    surfaces = manifest["surfaces"]
    assert isinstance(surfaces, list)
    first = surfaces[0]
    assert isinstance(first, dict)
    return first


def _materialize_declared_evidence(root: Path, manifest: dict[str, Any]) -> None:
    for raw_surface in manifest["surfaces"]:
        assert isinstance(raw_surface, dict)
        for raw_path in raw_surface["evidence"]:
            path = root / raw_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch()


def _source_bound_first_surface(root: Path, manifest: dict[str, Any]) -> None:
    source_relative = Path("src/kernels/example.yaml")
    source_path = root / source_relative
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(
        """schema: example/v1
state_vars:
  - id: x
    type: {kind: int, min: 0, max: 1}
actions:
  - id: run
    params:
      - id: amount
        type: {kind: int, min: 0, max: 1}
""",
        encoding="utf-8",
    )
    source_sha = hashlib.sha256(source_path.read_bytes()).hexdigest()
    evidence_relative = Path("tests/data/example-boundaries.json")
    evidence_path = root / evidence_relative
    evidence_path.parent.mkdir(parents=True, exist_ok=True)
    witnesses = []
    for value, labels in ((0, ["min", "max-1"]), (1, ["min+1", "max"])):
        pre_state = {"x": value}
        witnesses.append(
            {
                "field": "x",
                "value": value,
                "labels": labels,
                "pre_state": pre_state,
                "witness_sha256": hashlib.sha256(
                    json.dumps(
                        pre_state,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest(),
            }
        )
    evidence_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/ml-boundary-bva/v1",
                "model_path": source_relative.as_posix(),
                "model_sha256": source_sha,
                "state_boundary_witnesses": {
                    "enabled": True,
                    "method": "esso_z3_exact_state_edge_obligations_v3",
                    "witnesses": witnesses,
                    "infeasible": [],
                    "unresolved": [],
                    "target_count": 4,
                    "unique_target_count": 2,
                },
            }
        ),
        encoding="utf-8",
    )
    first = _first_surface(manifest)
    first.update(
        {
            "status": "complete",
            "inventory_complete": True,
            "commands": ["run"],
            "authoritative_fields": ["x"],
            "action_parameters": ["run.amount"],
            "covered_boundary_classes": list(REQUIRED_BOUNDARY_CLASSES),
            "missing_boundary_classes": [],
            "not_applicable_boundary_classes": [],
            "not_applicable_reasons": {},
            "source_model": {
                "path": source_relative.as_posix(),
                "sha256": source_sha,
                "require_bounded_scalars": True,
                "state_boundary_evidence": {
                    "path": evidence_relative.as_posix(),
                    "require_no_unresolved": True,
                },
            },
        }
    )


def test_default_inventory_is_valid_and_honestly_incomplete() -> None:
    report = check_manifest()
    assert report == {
        "ok": True,
        "schema": "zenodex/critical-bva-coverage/v1",
        "production_complete": False,
        "surface_count": 8,
        "incomplete_surfaces": [
            "spot_swap_and_fees",
            "liquidity",
            "perpetuals",
            "zusd",
            "oracle",
            "zeno_ledger_and_proof",
            "keys",
            "fire_and_zenocover",
        ],
    }


def test_checker_executes_directly_from_the_repository_gate() -> None:
    completed = subprocess.run(
        [sys.executable, "tools/bva/check_critical_surface_coverage.py"],
        cwd=DEFAULT_MANIFEST.parents[2],
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0
    assert json.loads(completed.stdout)["production_complete"] is False


def test_release_mode_fails_closed_while_any_surface_is_partial() -> None:
    with pytest.raises(CoverageManifestError, match="critical BVA coverage incomplete"):
        check_manifest(require_complete=True)


def test_missing_or_reordered_mandatory_surface_rejects(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest["surfaces"] = list(reversed(manifest["surfaces"]))
    with pytest.raises(CoverageManifestError, match="surface order or identity drift"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_required_boundary_class_cannot_be_deleted_from_the_universe(
    tmp_path: Path,
) -> None:
    manifest = _manifest()
    manifest["required_boundary_classes"].remove("resource_bounds")
    for surface in manifest["surfaces"]:
        surface["missing_boundary_classes"] = [
            value for value in surface["missing_boundary_classes"] if value != "resource_bounds"
        ]
        surface["covered_boundary_classes"] = [
            value for value in surface["covered_boundary_classes"] if value != "resource_bounds"
        ]
    with pytest.raises(CoverageManifestError, match="required boundary class inventory drift"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_boundary_partition_overlap_rejects(tmp_path: Path) -> None:
    manifest = _manifest()
    first = _first_surface(manifest)
    first["missing_boundary_classes"].append("numeric_lower_triplet")
    with pytest.raises(CoverageManifestError, match="covered/missing overlap"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_not_applicable_class_requires_a_reason(tmp_path: Path) -> None:
    manifest = _manifest()
    first = _first_surface(manifest)
    first["missing_boundary_classes"].remove("resource_bounds")
    first["not_applicable_boundary_classes"] = ["resource_bounds"]
    with pytest.raises(CoverageManifestError, match="not-applicable reasons mismatch"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_unknown_manifest_field_rejects(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest["allow_partial_release"] = True
    with pytest.raises(CoverageManifestError, match="unknown fields"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_duplicate_json_key_rejects(tmp_path: Path) -> None:
    raw = DEFAULT_MANIFEST.read_text(encoding="utf-8")
    path = tmp_path / "duplicate.json"
    path.write_text(raw.replace('"schema":', '"schema": "wrong", "schema":', 1), encoding="utf-8")
    with pytest.raises(CoverageManifestError, match="duplicate JSON key: schema"):
        check_manifest(path)


def test_evidence_must_be_repo_relative_and_under_tests(tmp_path: Path) -> None:
    manifest = _manifest()
    _first_surface(manifest)["evidence"][0] = "tools/bva/README.md"
    with pytest.raises(CoverageManifestError, match="evidence must live under tests"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_evidence_symlink_rejects_even_when_target_stays_inside_repo(tmp_path: Path) -> None:
    manifest = _manifest()
    _materialize_declared_evidence(tmp_path, manifest)
    target = tmp_path / "tests/target.py"
    target.touch()
    link = tmp_path / "tests/linked.py"
    link.symlink_to("target.py")
    _first_surface(manifest)["evidence"][0] = "tests/linked.py"
    with pytest.raises(CoverageManifestError, match="symbolic links are forbidden"):
        check_manifest(_write_manifest(tmp_path, manifest), repo_root=tmp_path)


def test_complete_claim_requires_source_bound_finite_model(tmp_path: Path) -> None:
    manifest = _manifest()
    first = _first_surface(manifest)
    first["status"] = "complete"
    first["inventory_complete"] = True
    first["covered_boundary_classes"] += first["missing_boundary_classes"]
    first["missing_boundary_classes"] = []
    with pytest.raises(CoverageManifestError, match="source-bound finite model evidence"):
        check_manifest(_write_manifest(tmp_path, manifest))


def test_source_bound_complete_surface_accepts_exact_finite_evidence(
    tmp_path: Path,
) -> None:
    manifest = _manifest()
    _materialize_declared_evidence(tmp_path, manifest)
    _source_bound_first_surface(tmp_path, manifest)
    report = check_manifest(_write_manifest(tmp_path, manifest), repo_root=tmp_path)
    assert report["production_complete"] is False
    assert "spot_swap_and_fees" not in report["incomplete_surfaces"]


def test_source_hash_mutation_rejects_before_coverage_promotion(
    tmp_path: Path,
) -> None:
    manifest = _manifest()
    _materialize_declared_evidence(tmp_path, manifest)
    _source_bound_first_surface(tmp_path, manifest)
    _first_surface(manifest)["source_model"]["sha256"] = "0" * 64
    with pytest.raises(CoverageManifestError, match="source model SHA-256 drift"):
        check_manifest(_write_manifest(tmp_path, manifest), repo_root=tmp_path)


def test_unresolved_state_boundary_rejects_complete_surface(
    tmp_path: Path,
) -> None:
    manifest = _manifest()
    _materialize_declared_evidence(tmp_path, manifest)
    _source_bound_first_surface(tmp_path, manifest)
    evidence_path = tmp_path / "tests/data/example-boundaries.json"
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    evidence["state_boundary_witnesses"]["unresolved"] = [{"field": "x", "value": 1}]
    evidence_path.write_text(json.dumps(evidence), encoding="utf-8")
    with pytest.raises(CoverageManifestError, match="unresolved state boundary obligations"):
        check_manifest(_write_manifest(tmp_path, manifest), repo_root=tmp_path)


def test_duplicate_yaml_key_rejects_even_when_the_new_hash_is_pinned(
    tmp_path: Path,
) -> None:
    manifest = _manifest()
    _materialize_declared_evidence(tmp_path, manifest)
    _source_bound_first_surface(tmp_path, manifest)
    source_path = tmp_path / "src/kernels/example.yaml"
    source_path.write_text(
        source_path.read_text(encoding="utf-8") + "actions: []\n", encoding="utf-8"
    )
    source_sha = hashlib.sha256(source_path.read_bytes()).hexdigest()
    _first_surface(manifest)["source_model"]["sha256"] = source_sha
    evidence_path = tmp_path / "tests/data/example-boundaries.json"
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    evidence["model_sha256"] = source_sha
    evidence_path.write_text(json.dumps(evidence), encoding="utf-8")
    with pytest.raises(CoverageManifestError, match="duplicate YAML key: actions"):
        check_manifest(_write_manifest(tmp_path, manifest), repo_root=tmp_path)


def test_production_complete_flag_cannot_be_asserted_independently(
    tmp_path: Path,
) -> None:
    manifest = _manifest()
    manifest["production_complete"] = True
    with pytest.raises(CoverageManifestError, match="does not match derived status"):
        check_manifest(_write_manifest(tmp_path, manifest))
