from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path

import pytest

from tools.check_production_boundary import (
    CLAIM_PROMOTION_ALLOWED_TARGETS,
    CLAIM_PROMOTION_REQUIRED_NEGATIVES,
    CLAIM_PROMOTION_SCHEMA,
    RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
    RESEARCH_PROMOTION_OBLIGATION_MANIFESTS,
    RESEARCH_PROMOTION_REGISTRY_MANIFEST_PATH,
    RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256,
    THEOREMSEARCH_RETRIEVAL_ALLOWED_TARGETS,
    THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA,
    THEOREMSEARCH_RETRIEVAL_QUERIES,
    THEOREMSEARCH_RETRIEVAL_REQUIRED_NEGATIVES,
    ResearchPromotionBoundaryContract,
    audit_production_boundary,
    research_promotion_control_fixture_digest,
    research_promotion_obligation_manifest_digest,
    research_promotion_registry_manifest_digest,
    scan_apply_operations_exposure,
    scan_legacy_settlement_profile_literals,
    scan_unsafe_config_literals,
    theoremsearch_retrieval_promotion_checks,
    validate_claim_promotion_research_boundary,
    validate_research_promotion_obligation_manifest,
    validate_research_promotion_obligation_manifest_file,
    validate_research_promotion_registry_manifest,
    validate_research_promotion_registry_manifest_file,
    validate_research_promotion_boundary,
)

ROOT = Path(__file__).resolve().parents[1]


def test_current_production_boundary_audit_passes() -> None:
    payload = audit_production_boundary(ROOT)

    assert payload["ok"] is True
    check_ids = {check["check_id"] for check in payload["checks"]}
    assert {
        "dex_engine_defaults_fail_closed",
        "core_dex_defaults_use_strong_settlement_profile",
        "named_safe_profiles_force_production_closure",
        "nonce_free_value_moving_batch_rejected",
        "integration_validation_uses_strong_settlement_validator",
        "production_src_has_no_unsafe_dex_config_literals",
        "production_src_has_no_legacy_settlement_profile_literals",
        "direct_settlement_apply_helper_unexposed",
        "api_server_does_not_expose_direct_value_moving_core_ingress",
        "tau_testnet_dex_plugin_enters_through_dex_engine",
        "supported_runtime_doc_scopes_public_boundary",
        "public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        "research_promotion_schema_registry_research_only",
    } <= check_ids
    requirement_ids = {item["requirement_id"] for item in payload["requirements"]}
    assert {
        "value_moving_paths_use_safe_profile",
        "no_production_nonce_free_path",
        "no_legacy_settlement_validation_in_production",
        "no_require_settlement_match_false_in_production",
        "no_direct_pure_core_ingress_exposed",
        "research_promotion_has_no_production_authority",
    } == requirement_ids
    assert all(item["ok"] is True for item in payload["requirements"])
    safe_profile = next(
        check for check in payload["checks"]
        if check["check_id"] == "named_safe_profiles_force_production_closure"
    )
    assert '"require_uniform_batch_v3_exact_out_grid_optimality": true' in safe_profile["evidence"]
    promotion_check = next(
        check for check in payload["checks"]
        if check["check_id"] == "research_promotion_schema_registry_research_only"
    )
    promotion_evidence = json.loads(promotion_check["evidence"])
    assert promotion_evidence["registry_contract_count"] == 2
    assert promotion_evidence["registry_digest"] == RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256
    assert promotion_evidence["registry_manifest_path"] == "tools/research_promotion_boundary_registry_manifest.json"
    assert promotion_evidence["registry_manifest_schema"] == (
        "zenodex.research_promotion.boundary_registry_manifest.v1"
    )
    assert promotion_evidence["obligation_count"] == 2
    obligations = promotion_evidence["obligations"]
    assert obligations[CLAIM_PROMOTION_SCHEMA]["obligation_digest"] == (
        RESEARCH_PROMOTION_OBLIGATION_MANIFESTS[CLAIM_PROMOTION_SCHEMA]["sha256"]
    )
    assert obligations[THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA]["obligation_digest"] == (
        RESEARCH_PROMOTION_OBLIGATION_MANIFESTS[THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA]["sha256"]
    )
    assert promotion_evidence["registered_schemas"] == [
        THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA,
        CLAIM_PROMOTION_SCHEMA,
    ]
    assert promotion_evidence["reports"]["tight_argmax_claim_promotion"]["positive_count"] == 12
    assert promotion_evidence["reports"]["theoremsearch_retrieval_promotion"]["positive_count"] == 3


def test_unsafe_config_literal_scanner_rejects_production_overrides(tmp_path: Path) -> None:
    source = tmp_path / "unsafe.py"
    source.write_text(
        "\n".join(
            [
                "from src.integration.dex_engine import DexEngineConfig",
                "cfg = DexEngineConfig(require_settlement_match=False)",
                "cfg2 = DexEngineConfig(allow_missing_settlement=True)",
                "raw = {'require_settlement_match': False, \"allow_missing_settlement\": True}",
            ]
        ),
        encoding="utf-8",
    )

    findings = scan_unsafe_config_literals([source], root=tmp_path)
    assert [finding["rule_id"] for finding in findings] == [
        "require_settlement_match_false",
        "allow_missing_settlement_true",
        "require_settlement_match_false",
        "allow_missing_settlement_true",
    ]


def test_legacy_settlement_profile_scanner_rejects_legacy_config(tmp_path: Path) -> None:
    source = tmp_path / "legacy_profile.py"
    source.write_text(
        "\n".join(
            [
                "from src.core.dex import DexConfig",
                "cfg = DexConfig(settlement_validation='legacy')",
                "raw = {'settlement_validation': 'legacy'}",
            ]
        ),
        encoding="utf-8",
    )

    findings = scan_legacy_settlement_profile_literals([source], root=tmp_path)
    assert [finding["rule_id"] for finding in findings] == [
        "legacy_settlement_validation_profile",
        "legacy_settlement_validation_profile",
    ]


def test_apply_operations_exposure_scanner_rejects_import_and_call(tmp_path: Path) -> None:
    source = tmp_path / "unsafe_apply.py"
    source.write_text(
        "\n".join(
            [
                "from src.integration.validation import apply_operations",
                "def run():",
                "    return apply_operations(None, None, None)",
            ]
        ),
        encoding="utf-8",
    )

    findings = scan_apply_operations_exposure([source], root=tmp_path)
    assert [finding["rule_id"] for finding in findings] == [
        "legacy_apply_operations_import",
        "legacy_apply_operations_call",
    ]


def _valid_claim_promotion_payload() -> dict[str, object]:
    negative_cases = [
        {
            "mutation_id": mutation_id,
            "expected_reason": expected_reason,
            "reason": expected_reason,
            "ok": True,
        }
        for mutation_id, expected_reason in CLAIM_PROMOTION_REQUIRED_NEGATIVES.items()
    ]
    positive_cases = [
        {
            "case_id": f"case_{target}",
            "promotion_target": target,
            "ok": True,
            "bundle_sha256": "a" * 64,
            "manifest_sha256": "b" * 64,
        }
        for target in sorted(CLAIM_PROMOTION_ALLOWED_TARGETS)
    ]
    return {
        "schema": CLAIM_PROMOTION_SCHEMA,
        "ok": True,
        "positive_count": len(positive_cases),
        "negative_count": len(negative_cases),
        "positive_cases": positive_cases,
        "negative_cases": negative_cases,
    }


def _valid_theoremsearch_retrieval_payload() -> dict[str, object]:
    payload = theoremsearch_retrieval_promotion_checks()
    assert isinstance(payload, dict)
    return payload


def _actual_claim_promotion_payload() -> dict[str, object]:
    from tools.check_tight_argmax_m_source_certificate_20260630 import claim_promotion_checks

    payload = claim_promotion_checks()
    assert isinstance(payload, dict)
    return payload


def _finding_ids(payload: dict[str, object]) -> set[str]:
    return {finding["rule_id"] for finding in validate_claim_promotion_research_boundary(payload)}


def _default_registry_manifest() -> dict[str, object]:
    payload = json.loads(RESEARCH_PROMOTION_REGISTRY_MANIFEST_PATH.read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _default_obligation_manifest(schema: str) -> dict[str, object]:
    expected = RESEARCH_PROMOTION_OBLIGATION_MANIFESTS[schema]
    payload = json.loads((ROOT / str(expected["path"])).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def test_research_promotion_boundary_registry_exposes_contracts() -> None:
    tight_argmax = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS[CLAIM_PROMOTION_SCHEMA]
    theoremsearch = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS[THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA]

    assert tight_argmax.schema == CLAIM_PROMOTION_SCHEMA
    assert tight_argmax.allowed_targets == CLAIM_PROMOTION_ALLOWED_TARGETS
    assert tight_argmax.required_negative_map == CLAIM_PROMOTION_REQUIRED_NEGATIVES
    assert tight_argmax.required_hash_fields == ("bundle_sha256", "manifest_sha256")

    assert theoremsearch.schema == THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA
    assert theoremsearch.allowed_targets == THEOREMSEARCH_RETRIEVAL_ALLOWED_TARGETS
    assert theoremsearch.required_negative_map == THEOREMSEARCH_RETRIEVAL_REQUIRED_NEGATIVES
    assert theoremsearch.required_hash_fields == ("retrieval_sha256", "query_sha256")
    assert set(RESEARCH_PROMOTION_OBLIGATION_MANIFESTS) == {
        CLAIM_PROMOTION_SCHEMA,
        THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA,
    }


def test_research_promotion_registry_manifest_is_source_pinned() -> None:
    manifest = _default_registry_manifest()

    assert research_promotion_registry_manifest_digest(manifest) == RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256
    assert validate_research_promotion_registry_manifest(manifest) == []

    loaded, digest, findings = validate_research_promotion_registry_manifest_file()
    assert loaded == manifest
    assert digest == RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256
    assert findings == []


def test_research_promotion_obligation_manifests_are_source_pinned() -> None:
    reports = {
        CLAIM_PROMOTION_SCHEMA: ("tight_argmax_claim_promotion", _actual_claim_promotion_payload()),
        THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA: (
            "theoremsearch_retrieval_promotion",
            _valid_theoremsearch_retrieval_payload(),
        ),
    }

    for schema, (report_id, report) in reports.items():
        manifest = _default_obligation_manifest(schema)
        expected = RESEARCH_PROMOTION_OBLIGATION_MANIFESTS[schema]
        fixtures = manifest["control_fixtures"]
        assert isinstance(fixtures, dict)
        assert research_promotion_obligation_manifest_digest(manifest) == expected["sha256"]
        assert fixtures["positive_cases_sha256"] == research_promotion_control_fixture_digest(
            report,
            "positive_cases",
        )
        assert fixtures["negative_cases_sha256"] == research_promotion_control_fixture_digest(
            report,
            "negative_cases",
        )
        assert validate_research_promotion_obligation_manifest(
            manifest,
            report,
            report_id=report_id,
        ) == []
        loaded, digest, findings = validate_research_promotion_obligation_manifest_file(report_id, report)
        assert loaded == manifest
        assert digest == expected["sha256"]
        assert findings == []


def test_research_promotion_registry_manifest_rejects_missing_and_stale_files(tmp_path: Path) -> None:
    missing_path = tmp_path / "missing_registry_manifest.json"
    loaded, digest, findings = validate_research_promotion_registry_manifest_file(missing_path)

    assert loaded is None
    assert digest is None
    assert [finding["rule_id"] for finding in findings] == ["registry_manifest_missing"]

    manifest_path = tmp_path / "registry_manifest.json"
    manifest_path.write_text(json.dumps(_default_registry_manifest(), sort_keys=True), encoding="utf-8")
    _loaded, stale_digest, stale_findings = validate_research_promotion_registry_manifest_file(
        manifest_path,
        expected_sha256="0" * 64,
    )
    assert stale_digest == RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256
    assert "registry_manifest_digest_mismatch" in {finding["rule_id"] for finding in stale_findings}


def test_research_promotion_obligation_manifest_rejects_missing_and_stale_files(tmp_path: Path) -> None:
    report = _valid_theoremsearch_retrieval_payload()
    missing_path = tmp_path / "missing_obligation_manifest.json"
    loaded, digest, findings = validate_research_promotion_obligation_manifest_file(
        "theoremsearch_retrieval_promotion",
        report,
        path=missing_path,
    )
    assert loaded is None
    assert digest is None
    assert [finding["rule_id"] for finding in findings] == ["obligation_manifest_missing"]

    manifest_path = tmp_path / "obligation_manifest.json"
    manifest_path.write_text(
        json.dumps(_default_obligation_manifest(THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA), sort_keys=True),
        encoding="utf-8",
    )
    _loaded, stale_digest, stale_findings = validate_research_promotion_obligation_manifest_file(
        "theoremsearch_retrieval_promotion",
        report,
        path=manifest_path,
        expected_sha256="0" * 64,
    )
    assert stale_digest == RESEARCH_PROMOTION_OBLIGATION_MANIFESTS[
        THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA
    ]["sha256"]
    assert "obligation_manifest_digest_mismatch" in {finding["rule_id"] for finding in stale_findings}


def test_research_promotion_registry_manifest_rejects_schema_confusion() -> None:
    manifest = _default_registry_manifest()
    contracts = manifest["contracts"]
    assert isinstance(contracts, list)
    confused_contract = deepcopy(contracts[0])
    confused_contract["schema"] = "zenodex.unknown.promotion_bundle.v1"
    confused_contract["allowed_targets"] = ["production"]
    contracts.append(confused_contract)

    finding_ids = {finding["rule_id"] for finding in validate_research_promotion_registry_manifest(manifest)}
    assert "registry_manifest_schema_set_mismatch" in finding_ids
    assert "registry_manifest_unknown_contract_schema" in finding_ids


def test_research_promotion_obligation_manifest_rejects_cross_schema_fixture_reuse() -> None:
    theorem_report = _valid_theoremsearch_retrieval_payload()
    manifest = _default_obligation_manifest(THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA)
    tight_manifest = _default_obligation_manifest(CLAIM_PROMOTION_SCHEMA)
    manifest["control_fixtures"] = deepcopy(tight_manifest["control_fixtures"])

    finding_ids = {
        finding["rule_id"]
        for finding in validate_research_promotion_obligation_manifest(
            manifest,
            theorem_report,
            report_id="theoremsearch_retrieval_promotion",
        )
    }
    assert "obligation_manifest_positive_count_mismatch" in finding_ids
    assert "obligation_manifest_positive_cases_sha256_mismatch" in finding_ids
    assert "obligation_manifest_negative_cases_sha256_mismatch" in finding_ids


def test_theoremsearch_obligation_manifest_rejects_proof_role() -> None:
    report = _valid_theoremsearch_retrieval_payload()
    manifest = _default_obligation_manifest(THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA)
    manifest["evidence_roles"] = ["proof", "research_only"]

    finding_ids = {
        finding["rule_id"]
        for finding in validate_research_promotion_obligation_manifest(
            manifest,
            report,
            report_id="theoremsearch_retrieval_promotion",
        )
    }
    assert "obligation_manifest_evidence_roles_mismatch" in finding_ids


def test_research_promotion_boundary_contract_rejects_invalid_registry_entries() -> None:
    with pytest.raises(ValueError, match="schema"):
        ResearchPromotionBoundaryContract(
            schema="",
            allowed_targets=frozenset({"claims_registry"}),
            required_negative_reasons=(("missing_manifest", "promotion manifest required"),),
        )
    with pytest.raises(ValueError, match="allowed targets"):
        ResearchPromotionBoundaryContract(
            schema="example.schema.v1",
            allowed_targets=frozenset(),
            required_negative_reasons=(("missing_manifest", "promotion manifest required"),),
        )
    with pytest.raises(ValueError, match="duplicate promotion boundary negative id"):
        ResearchPromotionBoundaryContract(
            schema="example.schema.v1",
            allowed_targets=frozenset({"claims_registry"}),
            required_negative_reasons=(("x", "reason"), ("x", "reason")),
        )


def test_research_promotion_boundary_validator_rejects_unknown_schema() -> None:
    unknown = _valid_claim_promotion_payload()
    unknown["schema"] = "zenodex.unknown.promotion_bundle.v1"

    assert validate_claim_promotion_research_boundary(unknown) == [
        {
            "rule_id": "unknown_promotion_schema",
            "message": "zenodex.unknown.promotion_bundle.v1",
        }
    ]


def test_claim_promotion_boundary_validator_rejects_authority_escape_shapes() -> None:
    valid = _valid_claim_promotion_payload()
    assert validate_claim_promotion_research_boundary(valid) == []

    unsupported_target = deepcopy(valid)
    unsupported_target["positive_cases"][0]["promotion_target"] = "settlement_authority"
    assert "unsupported_promotion_target" in _finding_ids(unsupported_target)

    missing_negative = deepcopy(valid)
    missing_negative["negative_cases"] = [
        row for row in missing_negative["negative_cases"]
        if row["mutation_id"] != "production_security_overclaim"
    ]
    missing_negative["negative_count"] = len(missing_negative["negative_cases"])
    assert "required_negative_missing" in _finding_ids(missing_negative)

    failed_negative = deepcopy(valid)
    failed_negative["negative_cases"][0]["ok"] = False
    assert "required_negative_failed" in _finding_ids(failed_negative)

    bad_hash = deepcopy(valid)
    bad_hash["positive_cases"][0]["bundle_sha256"] = "A" * 64
    assert "bad_bundle_hash" in _finding_ids(bad_hash)


def test_theoremsearch_retrieval_boundary_validator_rejects_schema_confusion() -> None:
    valid = _valid_theoremsearch_retrieval_payload()
    assert validate_research_promotion_boundary(valid) == []
    assert valid["positive_count"] == len(THEOREMSEARCH_RETRIEVAL_QUERIES)

    unsupported_target = deepcopy(valid)
    unsupported_target["positive_cases"][0]["promotion_target"] = "claims_registry"
    findings = validate_research_promotion_boundary(unsupported_target)
    assert {finding["rule_id"] for finding in findings} == {"unsupported_promotion_target"}

    missing_negative = deepcopy(valid)
    missing_negative["negative_cases"] = [
        row for row in missing_negative["negative_cases"]
        if row["mutation_id"] != "retrieval_as_proof"
    ]
    missing_negative["negative_count"] = len(missing_negative["negative_cases"])
    assert "required_negative_missing" in {
        finding["rule_id"] for finding in validate_research_promotion_boundary(missing_negative)
    }

    bad_hash = deepcopy(valid)
    bad_hash["positive_cases"][0]["retrieval_sha256"] = "not-a-sha"
    assert "bad_retrieval_hash" in {
        finding["rule_id"] for finding in validate_research_promotion_boundary(bad_hash)
    }


def test_per_schema_negative_controls_cannot_cross_satisfy() -> None:
    confused = _valid_theoremsearch_retrieval_payload()
    confused["schema"] = CLAIM_PROMOTION_SCHEMA

    finding_ids = {finding["rule_id"] for finding in validate_research_promotion_boundary(confused)}
    assert "required_negative_missing" in finding_ids
    assert "bad_bundle_hash" in finding_ids
    assert "bad_manifest_hash" in finding_ids
