#!/usr/bin/env python3
"""Validate the internal ZenoCover legal/regulatory release boundary."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

MANIFEST_SCHEMA = "zenodex.zenocover.regulatory_boundary_manifest.v0"
REPORT_SCHEMA = "zenodex.zenocover.regulatory_boundary_report.v0"

REQUIRED_REVIEWS = frozenset(
    {
        "insurance_regulatory_counsel",
        "jurisdiction_classification",
        "licensed_carrier_or_approved_model",
        "reserve_capital_accounting",
        "consumer_disclosure_market_conduct",
        "sanctions_aml_kyc",
        "tax_accounting",
        "oracle_basis_risk_disclosure",
    }
)

REQUIRED_REGULATED_TERMS = frozenset(
    {
        "insurance",
        "underwriting",
        "policy",
        "premium",
        "policyholder",
        "claims_adjustment",
    }
)

REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS = frozenset(
    {
        "user_runs_software_themselves",
        "user_compiles_or_interprets_themselves",
        "user_directly_signs_transactions",
    }
)

REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS = frozenset(
    {
        "project_accepts_or_transmits_value_for_users",
        "project_acts_as_broker_agent_or_intermediary",
        "project_hosts_managed_execution_or_wallet_service",
        "project_is_insurer_or_risk_bearer",
        "project_takes_custody",
        "project_controls_user_keys",
        "project_operates_or_controls_pool",
        "project_collects_or_sets_premiums",
        "project_issues_or_sells_cover_contracts",
        "project_pools_or_mutualizes_user_risk",
        "project_handles_claims_or_adjustment",
        "project_provides_claim_decision_or_discretion",
        "project_guarantees_or_promises_payout",
        "project_gives_personalized_financial_advice",
        "project_recommends_user_action",
        "project_selects_or_recommends_cover_terms",
        "project_sets_or_administers_coverage_terms",
        "project_markets_as_regulated_insurance",
        "project_routes_or_arranges_cover_purchase",
        "project_matches_or_routes_user_orders",
        "project_can_unilaterally_move_user_value",
    }
)

REQUIRED_USER_DISCLOSURES = frozenset(
    {
        "you_run_software_yourself",
        "you_compile_or_interpret_software_yourself",
        "you_directly_sign_transactions",
        "project_never_takes_custody",
        "project_never_controls_user_keys",
        "project_never_tells_you_what_to_do_with_money",
        "project_is_not_an_insurance_company",
        "no_policy_no_premium_no_claim_adjustment",
        "no_guaranteed_payout",
        "not_legal_tax_or_financial_advice",
    }
)

REQUIRED_SOURCE_CITATIONS = frozenset(
    {
        "bekemeier_defi_insurability_2023",
        "nadler_bekemeier_schar_defi_risk_transfer_2022",
        "zhou_zhang_defi_insurance_conundrums_2025",
        "mik_oracle_problem_insurtech_2023",
        "iais_fintech_developments_insurance_2022",
        "eiopa_blockchain_smart_contracts_insurance_2022",
        "naic_parametric_disaster_insurance",
        "naic_mccarran_ferguson_state_regulation",
        "fincen_cvc_guidance_2019",
        "opencover_onchain_cover_language",
    }
)

INTERNAL_RESEARCH_STATUS = "internal_research_only"
LAUNCH_CANDIDATE_STATUS = "counsel_gated_launch_candidate"
TERM_BLOCKED = "blocked_for_public_use_without_counsel"
TERM_APPROVED = "approved_for_counsel_cleared_jurisdiction"
ALLOWED_OPERATING_MODELS = frozenset(
    {
        "approved_cover_marketplace",
        "captive_or_sandbox",
        "licensed_carrier_partnership",
        "mutual_member_model",
        "regulated_entity_operated_pool",
    }
)
ALLOWED_TERM_STATUSES = frozenset({TERM_BLOCKED, TERM_APPROVED})


def validate_zenocover_regulatory_boundary_v0(manifest: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    status = _str(obj.get("status"), "status", errors)
    if status not in {INTERNAL_RESEARCH_STATUS, LAUNCH_CANDIDATE_STATUS}:
        errors.append("status must be internal_research_only or counsel_gated_launch_candidate")

    launch_allowed = _bool(obj.get("launch_allowed"), "launch_allowed", errors)
    public_marketing_allowed = _bool(obj.get("public_marketing_allowed"), "public_marketing_allowed", errors)
    user_sales_enabled = _bool(obj.get("user_sales_enabled"), "user_sales_enabled", errors)
    premium_collection_enabled = _bool(obj.get("premium_collection_enabled"), "premium_collection_enabled", errors)
    external_policy_language_allowed = _bool(
        obj.get("external_policy_language_allowed"), "external_policy_language_allowed", errors
    )
    jurisdictions = _list(obj.get("jurisdictions"), "jurisdictions", errors)
    operating_model = _str(obj.get("operating_model"), "operating_model", errors)
    software_only = _mapping(obj.get("software_only_boundary"), "software_only_boundary", errors)
    user_disclosures = _list(obj.get("user_disclosures"), "user_disclosures", errors)
    reviews = _mapping(obj.get("required_reviews"), "required_reviews", errors)
    regulated_terms = _mapping(obj.get("regulated_terms"), "regulated_terms", errors)
    source_citations = _mapping(obj.get("source_citations"), "source_citations", errors)

    missing_reviews = sorted(REQUIRED_REVIEWS - set(reviews))
    if missing_reviews:
        errors.append(f"missing required reviews: {','.join(missing_reviews)}")
    missing_terms = sorted(REQUIRED_REGULATED_TERMS - set(regulated_terms))
    if missing_terms:
        errors.append(f"missing regulated terms: {','.join(missing_terms)}")
    missing_true_flags = sorted(REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS - set(software_only))
    if missing_true_flags:
        errors.append(f"missing software-only true flags: {','.join(missing_true_flags)}")
    missing_false_flags = sorted(REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS - set(software_only))
    if missing_false_flags:
        errors.append(f"missing software-only false flags: {','.join(missing_false_flags)}")
    disclosure_ids: set[str] = set()
    for index, disclosure in enumerate(user_disclosures):
        if not isinstance(disclosure, str) or not disclosure:
            errors.append(f"user disclosure {index} must be a non-empty string")
            continue
        disclosure_ids.add(disclosure)
    missing_user_disclosures = sorted(REQUIRED_USER_DISCLOSURES - disclosure_ids)
    if missing_user_disclosures:
        errors.append(f"missing user disclosures: {','.join(missing_user_disclosures)}")
    missing_source_citations = sorted(REQUIRED_SOURCE_CITATIONS - set(source_citations))
    if missing_source_citations:
        errors.append(f"missing source citations: {','.join(missing_source_citations)}")
    for source_id, source in source_citations.items():
        if not isinstance(source, Mapping):
            errors.append(f"source citation {source_id} must be an object")
            continue
        if not isinstance(source.get("url"), str) or not source.get("url"):
            errors.append(f"source citation {source_id} must include a non-empty url")
        if not isinstance(source.get("relevance"), str) or not source.get("relevance"):
            errors.append(f"source citation {source_id} must include non-empty relevance")
    for term, value in regulated_terms.items():
        if value not in ALLOWED_TERM_STATUSES:
            errors.append(f"regulated term {term} has unsupported status")

    for name in sorted(REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS):
        if software_only.get(name) is not True:
            errors.append(f"software-only boundary must set {name}=true")
    for name in sorted(REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS):
        if software_only.get(name) is not False:
            errors.append(f"software-only boundary must set {name}=false")

    risky_flags = {
        "public_marketing_allowed": public_marketing_allowed,
        "user_sales_enabled": user_sales_enabled,
        "premium_collection_enabled": premium_collection_enabled,
        "external_policy_language_allowed": external_policy_language_allowed,
    }

    if status == INTERNAL_RESEARCH_STATUS:
        if launch_allowed is not False:
            errors.append("internal research manifest must set launch_allowed=false")
        for name, value in risky_flags.items():
            if value is not False:
                errors.append(f"internal research manifest must set {name}=false")
        if jurisdictions:
            errors.append("internal research manifest must not list launch jurisdictions")
        if operating_model not in {None, "unselected"}:
            errors.append("internal research manifest operating_model must be unselected")
        for term, value in regulated_terms.items():
            if value != TERM_BLOCKED:
                errors.append(f"regulated term {term} must stay blocked before counsel clearance")

    if launch_allowed is True or status == LAUNCH_CANDIDATE_STATUS:
        approved_reviews = {name for name, value in reviews.items() if value == "approved"}
        missing_approvals = sorted(REQUIRED_REVIEWS - approved_reviews)
        if missing_approvals:
            errors.append(f"launch candidate missing approved reviews: {','.join(missing_approvals)}")
        if not jurisdictions:
            errors.append("launch candidate must list approved jurisdictions")
        if operating_model not in ALLOWED_OPERATING_MODELS:
            errors.append("launch candidate must name an allowed counsel-approved operating model")
        if launch_allowed is not True:
            errors.append("launch candidate status must set launch_allowed=true")
        if any(value is True for value in risky_flags.values()):
            unapproved_terms = sorted(
                term for term, value in regulated_terms.items() if value != TERM_APPROVED
            )
            if unapproved_terms:
                errors.append(
                    f"launch candidate has unapproved regulated terms: {','.join(unapproved_terms)}"
                )

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "launch_allowed": launch_allowed,
        "public_marketing_allowed": public_marketing_allowed,
        "user_sales_enabled": user_sales_enabled,
        "premium_collection_enabled": premium_collection_enabled,
        "external_policy_language_allowed": external_policy_language_allowed,
        "review_count": len(reviews),
        "software_only_true_count": sum(1 for name in REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS if software_only.get(name) is True),
        "software_only_false_count": sum(1 for name in REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS if software_only.get(name) is False),
        "user_disclosure_count": len(disclosure_ids),
        "missing_user_disclosures": missing_user_disclosures,
        "source_citation_count": len(source_citations),
        "jurisdiction_count": len(jurisdictions),
        "required_boundary_fields": _required_boundary_fields(
            status=status,
            launch_allowed=launch_allowed,
            public_marketing_allowed=public_marketing_allowed,
            user_sales_enabled=user_sales_enabled,
            premium_collection_enabled=premium_collection_enabled,
            external_policy_language_allowed=external_policy_language_allowed,
            jurisdictions=jurisdictions,
            operating_model=operating_model,
            software_only=software_only,
            user_disclosures=disclosure_ids,
            reviews=reviews,
            regulated_terms=regulated_terms,
            source_citations=source_citations,
        ),
    }


def _required_boundary_fields(
    *,
    status: str | None,
    launch_allowed: bool | None,
    public_marketing_allowed: bool | None,
    user_sales_enabled: bool | None,
    premium_collection_enabled: bool | None,
    external_policy_language_allowed: bool | None,
    jurisdictions: list[Any],
    operating_model: str | None,
    software_only: Mapping[str, Any],
    user_disclosures: set[str],
    reviews: Mapping[str, Any],
    regulated_terms: Mapping[str, Any],
    source_citations: Mapping[str, Any],
) -> dict[str, bool]:
    risky_flags = {
        "public_marketing_allowed": public_marketing_allowed,
        "user_sales_enabled": user_sales_enabled,
        "premium_collection_enabled": premium_collection_enabled,
        "external_policy_language_allowed": external_policy_language_allowed,
    }
    fields: dict[str, bool] = {
        "status_supported": status in {INTERNAL_RESEARCH_STATUS, LAUNCH_CANDIDATE_STATUS},
        "internal_research_launch_blocked": status != INTERNAL_RESEARCH_STATUS or launch_allowed is False,
        "internal_research_risky_flags_blocked": status != INTERNAL_RESEARCH_STATUS
        or all(value is False for value in risky_flags.values()),
        "launch_candidate_has_jurisdiction_or_internal": status != LAUNCH_CANDIDATE_STATUS
        or bool(jurisdictions),
        "operating_model_allowed_or_unselected": (
            operating_model == "unselected"
            if status == INTERNAL_RESEARCH_STATUS
            else operating_model in ALLOWED_OPERATING_MODELS
        ),
    }
    for name in sorted(REQUIRED_SOFTWARE_ONLY_TRUE_FLAGS):
        fields[f"software_only_{name}"] = software_only.get(name) is True
    for name in sorted(REQUIRED_SOFTWARE_ONLY_FALSE_FLAGS):
        fields[f"software_only_{name}"] = software_only.get(name) is False
    for name in sorted(REQUIRED_USER_DISCLOSURES):
        fields[f"disclosure_{name}"] = name in user_disclosures
    for name in sorted(REQUIRED_REVIEWS):
        fields[f"review_{name}_declared"] = name in reviews
        fields[f"review_{name}_approved_or_internal"] = (
            status == INTERNAL_RESEARCH_STATUS or reviews.get(name) == "approved"
        )
    for term in sorted(REQUIRED_REGULATED_TERMS):
        value = regulated_terms.get(term)
        fields[f"regulated_term_{term}_declared"] = term in regulated_terms
        fields[f"regulated_term_{term}_status_supported"] = value in ALLOWED_TERM_STATUSES
        fields[f"regulated_term_{term}_blocked_or_approved"] = (
            value == TERM_BLOCKED
            if status == INTERNAL_RESEARCH_STATUS
            else value == TERM_APPROVED
        )
    for source_id in sorted(REQUIRED_SOURCE_CITATIONS):
        fields[f"source_{source_id}"] = source_id in source_citations
    return fields


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if isinstance(value, list):
        return value
    errors.append(f"{name} must be a list")
    return []


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if isinstance(value, bool):
        return value
    errors.append(f"{name} must be a boolean")
    return None


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_zenocover_regulatory_boundary_v0(_load_json(args.manifest))
    print(json.dumps(report, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
