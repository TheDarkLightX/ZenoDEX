from __future__ import annotations

import json
from pathlib import Path

from tools.check_disaster_obligation_certificate import (
    CertificateError,
    check_result_against_manifest,
    evaluate_manifest,
)

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tools" / "zeno_oracle_disaster_obligation_certificate_manifest.json"


def _load_manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def test_zeno_oracle_obligation_certificate_passes() -> None:
    manifest = _load_manifest()
    result = evaluate_manifest(manifest)
    check_result_against_manifest(result, manifest)

    assert result["axis_count"] == 24
    assert "proof_independence" in result["required_obligations"]
    assert "proof_independence_gate" in result["selected_guard_set"]
    assert result["selected_guard_set_covers_required_obligations"] is True
    assert result["private_certificate_proves_cardinality_optimality"] is True


def test_zeno_oracle_new_atom_probe_is_not_silently_covered() -> None:
    manifest = _load_manifest()
    manifest["candidate_probes"].append(
        {
            "name": "external_data_availability_oracle_variant",
            "obligations": ["critical_action_bound", "external_data_availability", "receipt_dag_closed"],
            "expected_classification": "new_atom_required",
        }
    )
    result = evaluate_manifest(manifest)
    probes = {probe["name"]: probe for probe in result["candidate_probes"]}

    availability = probes["external_data_availability_oracle_variant"]
    assert availability["classification"] == "new_atom_required"
    assert availability["missing_obligations"] == ["external_data_availability"]


def test_zeno_oracle_certificate_detects_uncovered_new_obligation() -> None:
    manifest = _load_manifest()
    manifest["axes"].append(
        {
            "name": "external_finality_reorg_feeds_oracle_read",
            "obligations": ["critical_action_bound", "external_data_availability", "receipt_dag_closed"],
        }
    )

    result = evaluate_manifest(manifest)
    assert "external_data_availability" in result["required_obligations"]
    assert result["selected_guard_set_covers_required_obligations"] is False

    try:
        check_result_against_manifest(result, manifest)
    except CertificateError as exc:
        assert "axis_count mismatch" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("certificate accepted a new uncovered obligation")
