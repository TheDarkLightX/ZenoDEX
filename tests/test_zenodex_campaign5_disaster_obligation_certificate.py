from __future__ import annotations

import json
from pathlib import Path

from tools.check_disaster_obligation_certificate import (
    CertificateError,
    check_result_against_manifest,
    evaluate_manifest,
)

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tools" / "zenodex_campaign5_disaster_obligation_certificate_manifest.json"


def _load_manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def test_campaign5_obligation_certificate_passes() -> None:
    manifest = _load_manifest()
    result = evaluate_manifest(manifest)
    check_result_against_manifest(result, manifest)

    assert result["schema"] == "zenodex.campaign5.disaster_obligation_certificate_result.v1"
    assert result["status"] == "accepted"
    assert result["axis_count"] == 7
    assert result["quotient_class_count"] == 3
    assert result["antichain_class_count"] == 3
    assert result["compression_ratio_axis_to_antichain"] == "7:3"
    assert result["selected_guard_set_covers_required_obligations"] is True
    assert result["private_certificate_proves_cardinality_optimality"] is True


def test_campaign5_candidate_probes_preserve_negative_knowledge() -> None:
    manifest = _load_manifest()
    result = evaluate_manifest(manifest)
    probes = {probe["name"]: probe for probe in result["candidate_probes"]}

    cubic_root = probes["cubic_root_generosity_variant"]
    assert cubic_root["classification"] == "new_atom_required"
    assert cubic_root["missing_obligations"] == ["post_calculation_k_assertion"]

    uniform_batch = probes["uniform_batch_lvr_variant"]
    assert uniform_batch["classification"] == "new_atom_required"
    assert uniform_batch["missing_obligations"] == [
        "order_permutation_invariance",
        "uniform_batch_clearing",
    ]


def test_campaign5_certificate_detects_uncovered_new_obligation() -> None:
    manifest = _load_manifest()
    manifest["axes"].append(
        {
            "name": "exotic_cubic_root_generosity_drain",
            "obligations": ["kernel_invariant_step", "post_calculation_k_assertion", "schema_total"],
        }
    )

    result = evaluate_manifest(manifest)
    assert "post_calculation_k_assertion" in result["required_obligations"]
    assert result["selected_guard_set_covers_required_obligations"] is False

    try:
        check_result_against_manifest(result, manifest)
    except CertificateError as exc:
        assert "axis_count mismatch" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("certificate accepted a new uncovered obligation")
