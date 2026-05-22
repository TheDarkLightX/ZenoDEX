from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_zenocover_regulatory_boundary import (
    REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS,
    REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS,
    REQUIRED_REVIEWS,
    REQUIRED_SOURCE_CITATIONS,
    REQUIRED_USER_DISCLOSURES,
    main,
    validate_zenocover_regulatory_boundary_v0,
)

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = ROOT / "internal" / "zenocover" / "REGULATORY_BOUNDARY_MANIFEST_V0.json"


def _manifest() -> dict[str, object]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def test_zenocover_regulatory_boundary_accepts_internal_research_manifest() -> None:
    report = validate_zenocover_regulatory_boundary_v0(_manifest())

    assert report["ok"] is True
    assert report["launch_allowed"] is False
    assert report["review_count"] == len(REQUIRED_REVIEWS)
    assert report["software_only_true_count"] == len(REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS)
    assert report["software_only_false_count"] == len(REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS)
    assert report["user_disclosure_count"] == len(REQUIRED_USER_DISCLOSURES)
    assert report["missing_user_disclosures"] == []
    assert report["source_citation_count"] == len(REQUIRED_SOURCE_CITATIONS)
    assert all(report["required_boundary_fields"].values())


def test_zenocover_regulatory_boundary_rejects_internal_premium_collection() -> None:
    manifest = _manifest()
    manifest["premium_collection_enabled"] = True

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "internal research manifest must set premium_collection_enabled=false" in report["errors"]


def test_zenocover_regulatory_boundary_rejects_launch_without_approved_reviews() -> None:
    manifest = _manifest()
    manifest["status"] = "counsel_gated_launch_candidate"
    manifest["launch_allowed"] = True
    manifest["jurisdictions"] = ["US-CA"]
    manifest["operating_model"] = "licensed_carrier_partnership"

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert any("launch candidate missing approved reviews" in err for err in report["errors"])


def test_zenocover_regulatory_boundary_rejects_launch_with_unapproved_terms() -> None:
    manifest = _manifest()
    manifest["status"] = "counsel_gated_launch_candidate"
    manifest["launch_allowed"] = True
    manifest["public_marketing_allowed"] = True
    manifest["jurisdictions"] = ["US-CA"]
    manifest["operating_model"] = "licensed_carrier_partnership"
    reviews = copy.deepcopy(manifest["required_reviews"])
    for key in reviews:  # type: ignore[union-attr]
        reviews[key] = "approved"  # type: ignore[index]
    manifest["required_reviews"] = reviews

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert any("launch candidate has unapproved regulated terms" in err for err in report["errors"])


def test_zenocover_regulatory_boundary_rejects_project_custody() -> None:
    manifest = _manifest()
    manifest["software_only_boundary"]["project_takes_custody"] = True  # type: ignore[index]

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "software-only boundary must set project_takes_custody=false" in report["errors"]


def test_zenocover_regulatory_boundary_rejects_personalized_advice() -> None:
    manifest = _manifest()
    manifest["software_only_boundary"]["project_gives_personalized_financial_advice"] = True  # type: ignore[index]

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "software-only boundary must set project_gives_personalized_financial_advice=false" in report["errors"]


def test_zenocover_regulatory_boundary_rejects_broker_intermediary_role() -> None:
    manifest = _manifest()
    manifest["software_only_boundary"]["project_acts_as_broker_agent_or_intermediary"] = True  # type: ignore[index]

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "software-only boundary must set project_acts_as_broker_agent_or_intermediary=false" in report["errors"]


def test_zenocover_regulatory_boundary_rejects_project_insurer_role() -> None:
    manifest = _manifest()
    manifest["software_only_boundary"]["project_is_insurer_or_risk_bearer"] = True  # type: ignore[index]

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "software-only boundary must set project_is_insurer_or_risk_bearer=false" in report["errors"]


def test_zenocover_regulatory_boundary_rejects_missing_user_disclosure() -> None:
    manifest = _manifest()
    disclosures = list(manifest["user_disclosures"])  # type: ignore[arg-type]
    disclosures.remove("project_never_tells_you_what_to_do_with_money")
    manifest["user_disclosures"] = disclosures

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "missing user disclosures: project_never_tells_you_what_to_do_with_money" in report["errors"]


def test_zenocover_regulatory_boundary_rejects_missing_research_source() -> None:
    manifest = _manifest()
    source_citations = copy.deepcopy(manifest["source_citations"])
    del source_citations["fincen_cvc_guidance_2019"]  # type: ignore[index]
    manifest["source_citations"] = source_citations

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is False
    assert "missing source citations: fincen_cvc_guidance_2019" in report["errors"]


def test_zenocover_regulatory_boundary_accepts_fully_approved_launch_candidate() -> None:
    manifest = _manifest()
    manifest["status"] = "counsel_gated_launch_candidate"
    manifest["launch_allowed"] = True
    manifest["public_marketing_allowed"] = True
    manifest["user_sales_enabled"] = True
    manifest["premium_collection_enabled"] = True
    manifest["external_policy_language_allowed"] = True
    manifest["jurisdictions"] = ["US-CA"]
    manifest["operating_model"] = "licensed_carrier_partnership"
    reviews = copy.deepcopy(manifest["required_reviews"])
    for key in reviews:  # type: ignore[union-attr]
        reviews[key] = "approved"  # type: ignore[index]
    manifest["required_reviews"] = reviews
    terms = copy.deepcopy(manifest["regulated_terms"])
    for key in terms:  # type: ignore[union-attr]
        terms[key] = "approved_for_counsel_cleared_jurisdiction"  # type: ignore[index]
    manifest["regulated_terms"] = terms

    report = validate_zenocover_regulatory_boundary_v0(manifest)

    assert report["ok"] is True
    assert report["launch_allowed"] is True
    assert report["jurisdiction_count"] == 1
    assert all(report["required_boundary_fields"].values())


def test_zenocover_regulatory_boundary_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "zenocover_regulatory_boundary.json"
    manifest_path.write_text(json.dumps(_manifest(), indent=2, sort_keys=True), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zenocover.regulatory_boundary_report.v0"
