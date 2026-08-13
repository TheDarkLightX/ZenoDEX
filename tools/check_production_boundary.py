#!/usr/bin/env python3
"""Audit production-boundary closure for value-moving ZenoDEX paths."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

UNSAFE_CONFIG_PATTERNS: tuple[tuple[str, re.Pattern[str], str], ...] = (
    (
        "require_settlement_match_false",
        re.compile(r"(?:\brequire_settlement_match\s*=|['\"]require_settlement_match['\"]\s*:)\s*False\b"),
        "Production code must not disable settlement matching.",
    ),
    (
        "allow_missing_settlement_true",
        re.compile(r"(?:\ballow_missing_settlement\s*=|['\"]allow_missing_settlement['\"]\s*:)\s*True\b"),
        "Production code must not accept nonce-bearing DEX intent batches without an explicit settlement.",
    ),
)

PRODUCTION_SCAN_ROOTS: tuple[str, ...] = ("src", "tools")
APPLY_OPERATIONS_EXPOSURE_EXEMPT: frozenset[str] = frozenset(
    {
        "src/integration/validation.py",
    }
)

API_SERVER_FORBIDDEN_TOKENS: tuple[str, ...] = (
    "apply_ops",
    "DexEngineConfig",
    "apply_settlement(",
    "apply_settlement_pure",
    "from src.core.dex",
    "from ..core.dex",
)

PRODUCTION_BOUNDARY_REQUIREMENTS: tuple[dict[str, Any], ...] = (
    {
        "requirement_id": "value_moving_paths_use_safe_profile",
        "objective": "Value-moving production paths go through fail-closed safe profiles.",
        "check_ids": (
            "dex_engine_defaults_fail_closed",
            "core_dex_defaults_use_strong_settlement_profile",
            "named_safe_profiles_force_production_closure",
            "tau_testnet_dex_plugin_enters_through_dex_engine",
            "public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        ),
    },
    {
        "requirement_id": "no_production_nonce_free_path",
        "objective": "Production posture does not expose nonce-free value-moving admission.",
        "check_ids": (
            "dex_engine_defaults_fail_closed",
            "named_safe_profiles_force_production_closure",
            "nonce_free_value_moving_batch_rejected",
            "public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        ),
    },
    {
        "requirement_id": "no_legacy_settlement_validation_in_production",
        "objective": "Production posture does not use legacy settlement validation.",
        "check_ids": (
            "core_dex_defaults_use_strong_settlement_profile",
            "integration_validation_uses_strong_settlement_validator",
            "production_src_has_no_legacy_settlement_profile_literals",
        ),
    },
    {
        "requirement_id": "no_require_settlement_match_false_in_production",
        "objective": "Production posture does not disable settlement matching.",
        "check_ids": (
            "dex_engine_defaults_fail_closed",
            "named_safe_profiles_force_production_closure",
            "production_src_has_no_unsafe_dex_config_literals",
        ),
    },
    {
        "requirement_id": "no_direct_pure_core_ingress_exposed",
        "objective": "External-facing production ingress does not call direct pure-core settlement helpers.",
        "check_ids": (
            "direct_settlement_apply_helper_unexposed",
            "api_server_does_not_expose_direct_value_moving_core_ingress",
            "tau_testnet_dex_plugin_enters_through_dex_engine",
        ),
    },
    {
        "requirement_id": "research_promotion_has_no_production_authority",
        "objective": "Research-promotion artifacts cannot become production security or settlement authority.",
        "check_ids": (
            "research_promotion_schema_registry_research_only",
        ),
    },
    {
        "requirement_id": "m6_writer_inventory_is_explicit",
        "objective": "M6 writer status remains explicit and unmounted until every value-moving path is routed through its commit port.",
        "check_ids": (
            "m6_writer_inventory_research_only",
        ),
    },
)

CLAIM_PROMOTION_SCHEMA = "zenodex.tight_argmax.claim_promotion_bundle.v1"
CLAIM_PROMOTION_ALLOWED_TARGETS: frozenset[str] = frozenset({"claims_registry", "research_kernel"})
CLAIM_PROMOTION_REQUIRED_NEGATIVES: dict[str, str] = {
    "missing_manifest": "promotion manifest required",
    "receipt_hash_without_manifest": "promotion manifest hash mismatch",
    "stale_manifest_hash": "promotion manifest hash mismatch",
    "detached_source_refs": "promotion source refs mismatch",
    "theoremsearch_prior_art_as_proof": "TheoremSearch prior art must be retrieval-only",
    "production_security_overclaim": "promotion bundle cannot claim production security",
    "promotion_missing_authority_boundary": "promotion missing no-authority boundary",
}
THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA = "zenodex.theoremsearch.retrieval_promotion_bundle.v1"
THEOREMSEARCH_RETRIEVAL_ALLOWED_TARGETS: frozenset[str] = frozenset({"research_kernel"})
THEOREMSEARCH_RETRIEVAL_REQUIRED_NEGATIVES: dict[str, str] = {
    "missing_retrieval_artifact": "theoremsearch retrieval artifact required",
    "stale_retrieval_hash": "theoremsearch retrieval hash mismatch",
    "retrieval_count_zero": "theoremsearch retrieval must return at least one candidate",
    "retrieval_as_proof": "TheoremSearch retrieval must remain retrieval-only",
    "unsupported_retrieval_target": "TheoremSearch retrieval cannot target production",
    "production_security_overclaim": "TheoremSearch retrieval cannot claim production security",
}
THEOREMSEARCH_RETRIEVAL_QUERIES: tuple[str, ...] = (
    "proof carrying code certificate checker soundness theorem",
    "canonical encoding signed hashed data schema evolution theorem",
    "typed certificate verification preservation theorem",
)
RESEARCH_PROMOTION_REGISTRY_MANIFEST_SCHEMA = "zenodex.research_promotion.boundary_registry_manifest.v1"
RESEARCH_PROMOTION_REGISTRY_MANIFEST_PATH = REPO_ROOT / "tools/research_promotion_boundary_registry_manifest.json"
RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256 = (
    "08f42efb472656ded5b443a2552bb8dac78ed15ff5626dda9ae1d3159b69a2cc"
)
RESEARCH_PROMOTION_OBLIGATION_MANIFEST_SCHEMA = "zenodex.research_promotion.obligation_manifest.v1"
RESEARCH_PROMOTION_OBLIGATION_MANIFESTS: dict[str, dict[str, object]] = {
    CLAIM_PROMOTION_SCHEMA: {
        "path": "tools/research_promotion_obligations/tight_argmax_claim_promotion_bundle_v1.json",
        "sha256": "da66f7eef306aad61a87098d0eca4d02bdb619e2965efa880630e99558a5f388",
        "report_id": "tight_argmax_claim_promotion",
        "replay_command": "python3 tools/check_tight_argmax_m_source_certificate_20260630.py",
        "source_refs": [
            "tools/check_tight_argmax_m_source_certificate_20260630.py",
            "docs/research/TIGHT_ARGMAX_CEILING_FEE_BOUND_20260630.md",
            "src/tau_specs/recommended/host_projection_contracts.json",
        ],
        "consumer_surfaces": ["claims_registry", "production_boundary_audit", "research_kernel"],
        "evidence_roles": ["local_replay_certificate", "research_only"],
    },
    THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA: {
        "path": "tools/research_promotion_obligations/theoremsearch_retrieval_promotion_bundle_v1.json",
        "sha256": "f0b7c9f9c2310403ab8bd8904541350e85f1489a19dd70cde123c843b54fd5fa",
        "report_id": "theoremsearch_retrieval_promotion",
        "replay_command": (
            "python3 tools/theoremsearch_query.py <query> --n-results 3 --format markdown "
            "--output-json <artifact>"
        ),
        "source_refs": [
            "tools/theoremsearch_query.py",
            "docs/research/THEOREMSEARCH_SETUP_20260630.md",
            "generated/theoremsearch/manifest_digest_schema_registry_20260630.json",
        ],
        "consumer_surfaces": ["production_boundary_audit", "research_kernel"],
        "evidence_roles": ["retrieval_only_prior_art", "research_only"],
    },
}
RESEARCH_PROMOTION_REQUIRED_NO_AUTHORITY_FLAGS: dict[str, bool] = {
    "consensus_authority": False,
    "production_security_claim": False,
    "routing_authority": False,
    "settlement_authority": False,
}


@dataclass(frozen=True)
class BoundaryCheck:
    check_id: str
    ok: bool
    evidence: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "check_id": self.check_id,
            "ok": self.ok,
            "evidence": self.evidence,
        }


@dataclass(frozen=True)
class ResearchPromotionBoundaryContract:
    schema: str
    allowed_targets: frozenset[str]
    required_negative_reasons: tuple[tuple[str, str], ...]
    required_hash_fields: tuple[str, ...] = ("bundle_sha256", "manifest_sha256")
    target_field: str = "promotion_target"

    def __post_init__(self) -> None:
        if not self.schema:
            raise ValueError("promotion boundary schema must be non-empty")
        if not self.allowed_targets or "" in self.allowed_targets:
            raise ValueError("promotion boundary allowed targets must be non-empty")
        negative_ids = [mutation_id for mutation_id, _reason in self.required_negative_reasons]
        if not negative_ids or "" in negative_ids:
            raise ValueError("promotion boundary required negatives must be non-empty")
        if len(set(negative_ids)) != len(negative_ids):
            raise ValueError("duplicate promotion boundary negative id")
        if any(not reason for _mutation_id, reason in self.required_negative_reasons):
            raise ValueError("promotion boundary negative reasons must be non-empty")
        if not self.required_hash_fields or "" in self.required_hash_fields:
            raise ValueError("promotion boundary hash fields must be non-empty")
        if len(set(self.required_hash_fields)) != len(self.required_hash_fields):
            raise ValueError("duplicate promotion boundary hash field")
        if not self.target_field:
            raise ValueError("promotion boundary target field must be non-empty")

    @property
    def required_negative_map(self) -> dict[str, str]:
        return dict(self.required_negative_reasons)


TIGHT_ARGMAX_CLAIM_PROMOTION_BOUNDARY_CONTRACT = ResearchPromotionBoundaryContract(
    schema=CLAIM_PROMOTION_SCHEMA,
    allowed_targets=CLAIM_PROMOTION_ALLOWED_TARGETS,
    required_negative_reasons=tuple(CLAIM_PROMOTION_REQUIRED_NEGATIVES.items()),
)
THEOREMSEARCH_RETRIEVAL_PROMOTION_BOUNDARY_CONTRACT = ResearchPromotionBoundaryContract(
    schema=THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA,
    allowed_targets=THEOREMSEARCH_RETRIEVAL_ALLOWED_TARGETS,
    required_negative_reasons=tuple(THEOREMSEARCH_RETRIEVAL_REQUIRED_NEGATIVES.items()),
    required_hash_fields=("retrieval_sha256", "query_sha256"),
)
RESEARCH_PROMOTION_BOUNDARY_CONTRACTS: dict[str, ResearchPromotionBoundaryContract] = {
    TIGHT_ARGMAX_CLAIM_PROMOTION_BOUNDARY_CONTRACT.schema: TIGHT_ARGMAX_CLAIM_PROMOTION_BOUNDARY_CONTRACT,
    THEOREMSEARCH_RETRIEVAL_PROMOTION_BOUNDARY_CONTRACT.schema: THEOREMSEARCH_RETRIEVAL_PROMOTION_BOUNDARY_CONTRACT,
}


def _canonical_json_text(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def research_promotion_registry_manifest_digest(manifest: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json_text(manifest).encode("utf-8")).hexdigest()


def research_promotion_obligation_manifest_digest(manifest: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json_text(manifest).encode("utf-8")).hexdigest()


def research_promotion_control_fixture_digest(report: Mapping[str, Any], cases_key: str) -> str:
    count_key = cases_key.replace("_cases", "_count")
    payload = {
        "cases": _object_list(report.get(cases_key)),
        "control_key": cases_key,
        "count": report.get(count_key),
        "schema": report.get("schema"),
    }
    return hashlib.sha256(_canonical_json_text(payload).encode("utf-8")).hexdigest()


def _manifest_required_negative_rows(
    contract: ResearchPromotionBoundaryContract,
) -> list[dict[str, str]]:
    return [
        {"expected_reason": expected_reason, "mutation_id": mutation_id}
        for mutation_id, expected_reason in contract.required_negative_reasons
    ]


def _validate_registry_manifest_contract_row(
    row: Mapping[str, Any],
    *,
    registry: Mapping[str, ResearchPromotionBoundaryContract],
) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []
    schema = row.get("schema")
    if not isinstance(schema, str):
        return [_promotion_boundary_finding("registry_manifest_contract_bad_schema", str(schema))]
    contract = registry.get(schema)
    if contract is None:
        return [_promotion_boundary_finding("registry_manifest_unknown_contract_schema", schema)]
    obligation = RESEARCH_PROMOTION_OBLIGATION_MANIFESTS.get(schema)
    if obligation is None:
        return [_promotion_boundary_finding("registry_manifest_missing_obligation_contract", schema)]
    expected = {
        "allowed_targets": sorted(contract.allowed_targets),
        "no_authority_flags": RESEARCH_PROMOTION_REQUIRED_NO_AUTHORITY_FLAGS,
        "obligation_manifest_path": obligation["path"],
        "obligation_manifest_sha256": obligation["sha256"],
        "required_hash_fields": list(contract.required_hash_fields),
        "required_negative_reasons": _manifest_required_negative_rows(contract),
        "schema": contract.schema,
        "target_field": contract.target_field,
    }
    for key, expected_value in expected.items():
        if row.get(key) != expected_value:
            findings.append(_promotion_boundary_finding(f"registry_manifest_{key}_mismatch", schema))
    return findings


def validate_research_promotion_registry_manifest(
    manifest: Mapping[str, Any],
    *,
    registry: Mapping[str, ResearchPromotionBoundaryContract] = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []
    if manifest.get("schema") != RESEARCH_PROMOTION_REGISTRY_MANIFEST_SCHEMA:
        findings.append(
            _promotion_boundary_finding(
                "registry_manifest_schema_mismatch",
                str(manifest.get("schema")),
            )
        )
    if manifest.get("registry_id") != "zenodex.research_promotion.boundary_registry":
        findings.append(
            _promotion_boundary_finding(
                "registry_manifest_id_mismatch",
                str(manifest.get("registry_id")),
            )
        )
    raw_contracts = manifest.get("contracts")
    if not isinstance(raw_contracts, list) or not raw_contracts:
        findings.append(_promotion_boundary_finding("registry_manifest_contracts_missing", "contracts"))
        return findings
    contract_rows = [item for item in raw_contracts if isinstance(item, dict)]
    if len(contract_rows) != len(raw_contracts):
        findings.append(_promotion_boundary_finding("registry_manifest_contract_not_object", "contracts"))
    schemas = [row.get("schema") for row in contract_rows if isinstance(row.get("schema"), str)]
    if len(set(schemas)) != len(schemas):
        findings.append(_promotion_boundary_finding("registry_manifest_duplicate_schema", "contracts"))
    if set(schemas) != set(registry):
        findings.append(
            _promotion_boundary_finding(
                "registry_manifest_schema_set_mismatch",
                ",".join(sorted(str(schema) for schema in schemas)),
            )
        )
    for row in contract_rows:
        findings.extend(_validate_registry_manifest_contract_row(row, registry=registry))
    return findings


def validate_research_promotion_obligation_manifest(
    obligation_manifest: Mapping[str, Any],
    report: Mapping[str, Any],
    *,
    report_id: str,
    registry: Mapping[str, ResearchPromotionBoundaryContract] = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []
    if obligation_manifest.get("schema") != RESEARCH_PROMOTION_OBLIGATION_MANIFEST_SCHEMA:
        findings.append(
            _promotion_boundary_finding(
                "obligation_manifest_schema_mismatch",
                str(obligation_manifest.get("schema")),
            )
        )
    promotion_schema = obligation_manifest.get("promotion_schema")
    if promotion_schema not in registry:
        findings.append(_promotion_boundary_finding("obligation_manifest_unknown_schema", str(promotion_schema)))
        return findings
    if report.get("schema") != promotion_schema:
        findings.append(
            _promotion_boundary_finding(
                "obligation_manifest_report_schema_mismatch",
                str(report.get("schema")),
            )
        )
    expected = RESEARCH_PROMOTION_OBLIGATION_MANIFESTS.get(str(promotion_schema))
    if expected is None:
        findings.append(_promotion_boundary_finding("obligation_manifest_missing_expected_contract", str(promotion_schema)))
        return findings
    expected_fields = {
        "consumer_surfaces": expected["consumer_surfaces"],
        "evidence_roles": expected["evidence_roles"],
        "no_authority_flags": RESEARCH_PROMOTION_REQUIRED_NO_AUTHORITY_FLAGS,
        "promotion_schema": promotion_schema,
        "replay_command": expected["replay_command"],
        "report_id": report_id,
        "source_refs": expected["source_refs"],
    }
    for key, expected_value in expected_fields.items():
        if obligation_manifest.get(key) != expected_value:
            findings.append(_promotion_boundary_finding(f"obligation_manifest_{key}_mismatch", str(promotion_schema)))
    fixtures = obligation_manifest.get("control_fixtures")
    if not isinstance(fixtures, dict):
        findings.append(_promotion_boundary_finding("obligation_manifest_control_fixtures_missing", str(promotion_schema)))
        return findings
    expected_positive_hash = research_promotion_control_fixture_digest(report, "positive_cases")
    expected_negative_hash = research_promotion_control_fixture_digest(report, "negative_cases")
    fixture_expectations = {
        "negative_cases_sha256": expected_negative_hash,
        "negative_count": report.get("negative_count"),
        "positive_cases_sha256": expected_positive_hash,
        "positive_count": report.get("positive_count"),
    }
    for key, expected_value in fixture_expectations.items():
        if fixtures.get(key) != expected_value:
            findings.append(_promotion_boundary_finding(f"obligation_manifest_{key}_mismatch", str(promotion_schema)))
    return findings


def validate_research_promotion_obligation_manifest_file(
    report_id: str,
    report: Mapping[str, Any],
    *,
    path: Path | None = None,
    expected_sha256: str | None = None,
    registry: Mapping[str, ResearchPromotionBoundaryContract] = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
) -> tuple[dict[str, Any] | None, str | None, list[dict[str, str]]]:
    schema = report.get("schema")
    expected = RESEARCH_PROMOTION_OBLIGATION_MANIFESTS.get(str(schema))
    if expected is None:
        finding = _promotion_boundary_finding("obligation_manifest_missing_expected_contract", str(schema))
        return None, None, [finding]
    manifest_path = path or (REPO_ROOT / str(expected["path"]))
    pinned_sha256 = expected_sha256 or str(expected["sha256"])
    try:
        raw = manifest_path.read_text(encoding="utf-8")
    except FileNotFoundError:
        finding = _promotion_boundary_finding("obligation_manifest_missing", str(manifest_path))
        return None, None, [finding]
    try:
        decoded = json.loads(raw)
    except json.JSONDecodeError as exc:
        finding = _promotion_boundary_finding("obligation_manifest_parse_error", str(exc))
        return None, None, [finding]
    if not isinstance(decoded, dict):
        finding = _promotion_boundary_finding("obligation_manifest_not_object", str(type(decoded).__name__))
        return None, None, [finding]
    digest = research_promotion_obligation_manifest_digest(decoded)
    findings = validate_research_promotion_obligation_manifest(
        decoded,
        report,
        report_id=report_id,
        registry=registry,
    )
    if digest != pinned_sha256:
        findings.append(_promotion_boundary_finding("obligation_manifest_digest_mismatch", digest))
    return decoded, digest, findings


def validate_research_promotion_registry_manifest_file(
    path: Path = RESEARCH_PROMOTION_REGISTRY_MANIFEST_PATH,
    *,
    expected_sha256: str = RESEARCH_PROMOTION_REGISTRY_MANIFEST_SHA256,
    registry: Mapping[str, ResearchPromotionBoundaryContract] = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
) -> tuple[dict[str, Any] | None, str | None, list[dict[str, str]]]:
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        finding = _promotion_boundary_finding("registry_manifest_missing", str(path))
        return None, None, [finding]
    try:
        decoded = json.loads(raw)
    except json.JSONDecodeError as exc:
        finding = _promotion_boundary_finding("registry_manifest_parse_error", str(exc))
        return None, None, [finding]
    if not isinstance(decoded, dict):
        finding = _promotion_boundary_finding("registry_manifest_not_object", str(type(decoded).__name__))
        return None, None, [finding]
    digest = research_promotion_registry_manifest_digest(decoded)
    findings = validate_research_promotion_registry_manifest(decoded, registry=registry)
    if digest != expected_sha256:
        findings.append(_promotion_boundary_finding("registry_manifest_digest_mismatch", digest))
    return decoded, digest, findings


def scan_unsafe_config_literals(paths: Iterable[Path], *, root: Path = REPO_ROOT) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            rel = path.relative_to(root)
        except ValueError:
            rel = path
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            for rule_id, pattern, message in UNSAFE_CONFIG_PATTERNS:
                if pattern.search(line):
                    findings.append(
                        {
                            "path": str(rel),
                            "line": line_no,
                            "rule_id": rule_id,
                            "message": message,
                            "text": line.strip(),
                        }
                    )
    return findings


def scan_legacy_settlement_profile_literals(
    paths: Iterable[Path],
    *,
    root: Path = REPO_ROOT,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except SyntaxError as exc:
            findings.append(
                {
                    "path": rel,
                    "line": exc.lineno or 0,
                    "rule_id": "python_parse_error",
                    "message": "production-boundary scanner could not parse Python source",
                    "text": exc.msg,
                }
            )
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and _call_name(node.func) == "DexConfig":
                for keyword in node.keywords:
                    if keyword.arg == "settlement_validation" and _literal_str(keyword.value) == "legacy":
                        findings.append(
                            {
                                "path": rel,
                                "line": int(getattr(node, "lineno", 0)),
                                "rule_id": "legacy_settlement_validation_profile",
                                "message": "Production source must not construct DexConfig with legacy settlement validation.",
                                "text": "DexConfig(settlement_validation='legacy')",
                            }
                        )
            if isinstance(node, ast.Dict):
                for key, value in zip(node.keys, node.values, strict=True):
                    if _literal_str(key) == "settlement_validation" and _literal_str(value) == "legacy":
                        findings.append(
                            {
                                "path": rel,
                                "line": int(getattr(node, "lineno", 0)),
                                "rule_id": "legacy_settlement_validation_profile",
                                "message": "Production source must not declare legacy settlement validation.",
                                "text": "{'settlement_validation': 'legacy'}",
                            }
                        )
    return findings


def scan_apply_operations_exposure(
    paths: Iterable[Path],
    *,
    root: Path = REPO_ROOT,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        if rel in APPLY_OPERATIONS_EXPOSURE_EXEMPT:
            continue
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except SyntaxError as exc:
            findings.append(
                {
                    "path": rel,
                    "line": exc.lineno or 0,
                    "rule_id": "python_parse_error",
                    "message": "production-boundary scanner could not parse Python source",
                    "text": exc.msg,
                }
            )
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom):
                imported = {alias.name for alias in node.names}
                if "apply_operations" in imported:
                    findings.append(
                        {
                            "path": rel,
                            "line": int(getattr(node, "lineno", 0)),
                            "rule_id": "legacy_apply_operations_import",
                            "message": "Production source must not import the direct settlement apply helper.",
                            "text": "apply_operations",
                        }
                    )
            if isinstance(node, ast.Call) and _call_name(node.func) == "apply_operations":
                findings.append(
                    {
                        "path": rel,
                        "line": int(getattr(node, "lineno", 0)),
                        "rule_id": "legacy_apply_operations_call",
                        "message": "Production source must not call the direct settlement apply helper.",
                        "text": "apply_operations(...)",
                    }
                )
    return findings


def _src_python_files(root: Path) -> list[Path]:
    return sorted((root / "src").rglob("*.py"))


def _production_python_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for rel in PRODUCTION_SCAN_ROOTS:
        base = root / rel
        if base.exists():
            files.extend(sorted(base.rglob("*.py")))
    return files


def _call_name(func: ast.AST) -> str:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return ""


def _literal_str(value: ast.AST | None) -> str | None:
    if isinstance(value, ast.Constant) and isinstance(value.value, str):
        return value.value
    return None


def _is_lower_sha256(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(ch in "0123456789abcdef" for ch in value)
    )


def _object_list(value: object) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        return []
    return [item for item in value if isinstance(item, dict)]


def _promotion_boundary_finding(rule_id: str, message: str) -> dict[str, str]:
    return {"rule_id": rule_id, "message": message}


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _bad_hash_rule_id(hash_field: str) -> str:
    if hash_field.endswith("_sha256"):
        return f"bad_{hash_field.removesuffix('_sha256')}_hash"
    return f"bad_{hash_field}"


def validate_research_promotion_boundary(
    promotion_report: Mapping[str, Any],
    *,
    registry: Mapping[str, ResearchPromotionBoundaryContract] = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []
    schema = promotion_report.get("schema")
    if not isinstance(schema, str):
        findings.append(_promotion_boundary_finding("bad_schema", "claim promotion schema mismatch"))
        return findings
    contract = registry.get(schema)
    if contract is None:
        findings.append(_promotion_boundary_finding("unknown_promotion_schema", schema))
        return findings
    if promotion_report.get("ok") is not True:
        findings.append(_promotion_boundary_finding("gate_not_ok", "claim promotion gate did not pass"))

    positive_rows = _object_list(promotion_report.get("positive_cases"))
    negative_rows = _object_list(promotion_report.get("negative_cases"))
    if promotion_report.get("positive_count") != len(positive_rows):
        findings.append(_promotion_boundary_finding("positive_count_mismatch", "positive count mismatch"))
    if promotion_report.get("negative_count") != len(negative_rows):
        findings.append(_promotion_boundary_finding("negative_count_mismatch", "negative count mismatch"))

    for row in positive_rows:
        target = row.get(contract.target_field)
        if target not in contract.allowed_targets:
            findings.append(_promotion_boundary_finding("unsupported_promotion_target", str(target)))
        if row.get("ok") is not True:
            findings.append(_promotion_boundary_finding("positive_row_failed", str(row.get("case_id"))))
        for hash_field in contract.required_hash_fields:
            if not _is_lower_sha256(row.get(hash_field)):
                findings.append(_promotion_boundary_finding(_bad_hash_rule_id(hash_field), str(row.get("case_id"))))

    negative_by_id = {str(row.get("mutation_id")): row for row in negative_rows}
    for mutation_id, expected_reason in contract.required_negative_map.items():
        row = negative_by_id.get(mutation_id)
        if row is None:
            findings.append(_promotion_boundary_finding("required_negative_missing", mutation_id))
            continue
        if row.get("ok") is not True or row.get("expected_reason") != expected_reason:
            findings.append(_promotion_boundary_finding("required_negative_failed", mutation_id))
    return findings


def validate_claim_promotion_research_boundary(
    claim_promotion: Mapping[str, Any],
    *,
    registry: Mapping[str, ResearchPromotionBoundaryContract] = RESEARCH_PROMOTION_BOUNDARY_CONTRACTS,
) -> list[dict[str, str]]:
    return validate_research_promotion_boundary(claim_promotion, registry=registry)


def theoremsearch_retrieval_promotion_checks() -> dict[str, Any]:
    positive_rows = [
        {
            "case_id": f"theoremsearch_retrieval:{index}",
            "promotion_target": "research_kernel",
            "ok": True,
            "query_sha256": _sha256_text(query),
            "retrieval_sha256": _sha256_text(f"{THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA}:{query}"),
        }
        for index, query in enumerate(THEOREMSEARCH_RETRIEVAL_QUERIES, start=1)
    ]
    negative_rows = [
        {
            "mutation_id": mutation_id,
            "expected_reason": expected_reason,
            "reason": expected_reason,
            "ok": True,
        }
        for mutation_id, expected_reason in THEOREMSEARCH_RETRIEVAL_REQUIRED_NEGATIVES.items()
    ]
    return {
        "schema": THEOREMSEARCH_RETRIEVAL_PROMOTION_SCHEMA,
        "ok": True,
        "positive_count": len(positive_rows),
        "negative_count": len(negative_rows),
        "positive_cases": positive_rows,
        "negative_cases": negative_rows,
        "claim_boundary": "TheoremSearch retrieval is prior art only and cannot promote production authority.",
    }


def _check_dex_config_defaults() -> BoundaryCheck:
    from src.integration.dex_engine import DexEngineConfig

    cfg = DexEngineConfig()
    facts = {
        "allow_missing_settlement": cfg.allow_missing_settlement,
        "require_settlement_match": cfg.require_settlement_match,
        "require_intent_signatures": cfg.require_intent_signatures,
        "consensus_mode": cfg.consensus_mode,
        "allow_external_tools": cfg.allow_external_tools,
    }
    ok = (
        facts["allow_missing_settlement"] is False
        and facts["require_settlement_match"] is True
        and facts["require_intent_signatures"] is True
        and facts["consensus_mode"] is True
        and facts["allow_external_tools"] is False
    )
    return BoundaryCheck(
        check_id="dex_engine_defaults_fail_closed",
        ok=ok,
        evidence=json.dumps(facts, sort_keys=True),
    )


def _check_core_dex_config_defaults() -> BoundaryCheck:
    from src.core.dex import DexConfig

    cfg = DexConfig()
    facts = {
        "settlement_validation": cfg.settlement_validation,
        "allow_snapshot_bound_quote_bindings": cfg.allow_snapshot_bound_quote_bindings,
        "swap_ordering": cfg.swap_ordering,
    }
    ok = (
        facts["settlement_validation"] == "strong_proof_carrying"
        and facts["allow_snapshot_bound_quote_bindings"] is False
        and facts["swap_ordering"] in ("greedy_ab_refined", "optimal_ab_bounded")
    )
    return BoundaryCheck(
        check_id="core_dex_defaults_use_strong_settlement_profile",
        ok=ok,
        evidence=json.dumps(facts, sort_keys=True),
    )


def _check_named_safe_profile_helpers() -> BoundaryCheck:
    from src.core.dex import DexConfig
    from src.integration.dex_engine import (
        make_strict_upba_engine_config,
        strict_upba_engine_config_facts_v0,
    )
    from src.integration.zeno_oracle_fail_closed_config import zeno_oracle_fail_closed_dex_config

    unsafe_dex_config = DexConfig(
        settlement_validation="legacy",
        allow_snapshot_bound_quote_bindings=True,
    )
    strict_upba = make_strict_upba_engine_config(
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_external_tools=True,
        consensus_mode=False,
        dex_config=unsafe_dex_config,
        allow_uniform_batch_certificate=False,
        require_uniform_batch_certificate_for_supported_swaps=False,
        require_uniform_batch_optimality_certificate=False,
        require_uniform_batch_v2_bounded_grid_optimality=False,
        require_uniform_batch_v3_exact_out_grid_optimality=False,
    )
    oracle_closed = zeno_oracle_fail_closed_dex_config(
        allow_missing_settlement=True,
        require_settlement_match=False,
        require_intent_signatures=False,
        allow_external_tools=True,
        consensus_mode=False,
        dex_config=unsafe_dex_config,
        require_oracle_authorization_for_protected_swaps=False,
        require_oracle_authorization_for_critical_settlements=False,
    )
    upba_facts = strict_upba_engine_config_facts_v0(strict_upba)
    oracle_facts = {
        "allow_missing_settlement": oracle_closed.allow_missing_settlement,
        "require_settlement_match": oracle_closed.require_settlement_match,
        "require_intent_signatures": oracle_closed.require_intent_signatures,
        "allow_external_tools": oracle_closed.allow_external_tools,
        "consensus_mode": oracle_closed.consensus_mode,
        "settlement_validation": oracle_closed.dex_config.settlement_validation,
        "allow_snapshot_bound_quote_bindings": oracle_closed.dex_config.allow_snapshot_bound_quote_bindings,
        "require_oracle_authorization_for_protected_swaps": (
            oracle_closed.require_oracle_authorization_for_protected_swaps
        ),
        "require_oracle_authorization_for_critical_settlements": (
            oracle_closed.require_oracle_authorization_for_critical_settlements
        ),
    }
    expected_common = {
        "allow_missing_settlement": False,
        "require_settlement_match": True,
        "require_intent_signatures": True,
        "allow_external_tools": False,
        "consensus_mode": True,
        "settlement_validation": "strong_proof_carrying",
        "allow_snapshot_bound_quote_bindings": False,
    }
    ok = all(upba_facts.get(key) == value for key, value in expected_common.items())
    ok = ok and all(oracle_facts.get(key) == value for key, value in expected_common.items())
    ok = ok and upba_facts["allow_uniform_batch_certificate"] is True
    ok = ok and upba_facts["require_uniform_batch_certificate_for_supported_swaps"] is True
    ok = ok and upba_facts["require_uniform_batch_optimality_certificate"] is True
    ok = ok and upba_facts["require_uniform_batch_v2_bounded_grid_optimality"] is True
    ok = ok and upba_facts["require_uniform_batch_v3_exact_out_grid_optimality"] is True
    ok = ok and oracle_facts["require_oracle_authorization_for_protected_swaps"] is True
    ok = ok and oracle_facts["require_oracle_authorization_for_critical_settlements"] is True
    return BoundaryCheck(
        check_id="named_safe_profiles_force_production_closure",
        ok=ok,
        evidence=json.dumps({"strict_upba": upba_facts, "zeno_oracle": oracle_facts}, sort_keys=True),
    )


def _check_nonce_free_batch_rejected() -> BoundaryCheck:
    from src.core.dex import DexState
    from src.core.liquidity import create_pool
    from src.integration.dex_engine import DexEngineConfig, apply_ops
    from src.state import BalanceTable, LPTable

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    pool_id, pool, _lp = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=10_000,
        amount1=10_000,
        fee_bps=30,
        creator_pubkey=sender,
    )
    balances = BalanceTable()
    balances.set(sender, asset0, 10_000)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())
    operations = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "SWAP_EXACT_IN",
                "intent_id": "0x" + "01" * 32,
                "sender_pubkey": sender,
                "deadline": 9_999_999_999,
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            }
        ]
    }
    result = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
        ),
        state=state,
        operations=operations,
        block_timestamp=42,
        tx_sender_pubkey=sender,
    )
    ok = result.ok is False and result.error == "Missing/invalid nonce"
    return BoundaryCheck(
        check_id="nonce_free_value_moving_batch_rejected",
        ok=ok,
        evidence=f"ok={result.ok!r}, error={result.error!r}",
    )


def _check_strong_settlement_validator(root: Path) -> BoundaryCheck:
    text = (root / "src/integration/validation.py").read_text(encoding="utf-8")
    ok = "validate_settlement_strong(" in text and "from ..core.settlement import validate_settlement" not in text
    return BoundaryCheck(
        check_id="integration_validation_uses_strong_settlement_validator",
        ok=ok,
        evidence="src/integration/validation.py imports and calls validate_settlement_strong",
    )


def _check_no_unsafe_config_literals(root: Path) -> BoundaryCheck:
    findings = scan_unsafe_config_literals(_src_python_files(root), root=root)
    return BoundaryCheck(
        check_id="production_src_has_no_unsafe_dex_config_literals",
        ok=not findings,
        evidence=json.dumps(findings, sort_keys=True),
    )


def _check_no_legacy_settlement_profile_literals(root: Path) -> BoundaryCheck:
    findings = scan_legacy_settlement_profile_literals(_src_python_files(root), root=root)
    return BoundaryCheck(
        check_id="production_src_has_no_legacy_settlement_profile_literals",
        ok=not findings,
        evidence=json.dumps(findings, sort_keys=True),
    )


def _check_direct_apply_operations_unexposed(root: Path) -> BoundaryCheck:
    findings = scan_apply_operations_exposure(_production_python_files(root), root=root)
    return BoundaryCheck(
        check_id="direct_settlement_apply_helper_unexposed",
        ok=not findings,
        evidence=json.dumps(findings, sort_keys=True),
    )


def _check_api_server_read_only_boundary(root: Path) -> BoundaryCheck:
    path = root / "src/integration/api_server.py"
    text = path.read_text(encoding="utf-8")
    found = [token for token in API_SERVER_FORBIDDEN_TOKENS if token in text]
    return BoundaryCheck(
        check_id="api_server_does_not_expose_direct_value_moving_core_ingress",
        ok=not found,
        evidence=json.dumps({"forbidden_tokens_found": found}, sort_keys=True),
    )


def _check_tau_testnet_uses_dex_engine_boundary(root: Path) -> BoundaryCheck:
    path = root / "src/integration/tau_testnet_dex_plugin.py"
    text = path.read_text(encoding="utf-8")
    required = ("DexEngineConfig", "apply_ops")
    forbidden = ("apply_settlement_pure", "apply_settlement(")
    found_forbidden = [token for token in forbidden if token in text]
    missing_required = [token for token in required if token not in text]
    return BoundaryCheck(
        check_id="tau_testnet_dex_plugin_enters_through_dex_engine",
        ok=not found_forbidden and not missing_required,
        evidence=json.dumps(
            {
                "missing_required": missing_required,
                "forbidden_tokens_found": found_forbidden,
            },
            sort_keys=True,
        ),
    )


def _check_supported_runtime_doc_scope(root: Path) -> BoundaryCheck:
    text = (root / "docs/RC1_SUPPORTED_RUNTIME_PATH.md").read_text(encoding="utf-8")
    anchors = (
        "RuntimePathOK := ReadOnlyHTTPBounded",
        "Spot intent admission and signing path",
        "does not promote the entire integration shell",
    )
    missing = [anchor for anchor in anchors if anchor not in text]
    return BoundaryCheck(
        check_id="supported_runtime_doc_scopes_public_boundary",
        ok=not missing,
        evidence=json.dumps({"missing_anchors": missing}, sort_keys=True),
    )


def _check_public_operator_node_preflight_blocks_unsigned_testnet_mutation() -> BoundaryCheck:
    from tools.zeno_ledger_node import NODE_JOIN_CONFIG_SCHEMA, preflight_node_join_config_v0

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        config_path = tmp_path / "node-config.json"
        bundle_root = tmp_path / "bundle"
        data_dir = tmp_path / "data"
        bundle_root.mkdir()
        config = {
            "schema": NODE_JOIN_CONFIG_SCHEMA,
            "node_id": "production-boundary-public-operator",
            "base_url": "http://127.0.0.1:1",
            "bundle_root": str(bundle_root),
            "data_dir": str(data_dir),
            "serve": True,
            "host": "0.0.0.0",
            "port": 8787,
            "enable_testnet_intake": True,
        }
        config_path.write_text(json.dumps(config, sort_keys=True), encoding="utf-8")
        report = preflight_node_join_config_v0(
            config_path=config_path,
            check_port=False,
            strict_exposure=True,
            public_operator=True,
        )
    errors = list(report.get("errors", []))
    required_errors = (
        "public_operator: public binds must not expose testnet faucet or intake endpoints",
        "strict_exposure: testnet transaction intake is enabled; this endpoint accepts unsigned fixture traffic",
    )
    ok = report.get("ok") is False and all(item in errors for item in required_errors)
    return BoundaryCheck(
        check_id="public_operator_node_preflight_blocks_unsigned_testnet_mutation",
        ok=ok,
        evidence=json.dumps(
            {
                "preflight_ok": report.get("ok"),
                "errors": errors,
                "required_errors": list(required_errors),
            },
            sort_keys=True,
        ),
    )


def _research_promotion_report_summary(report: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "negative_count": report.get("negative_count"),
        "positive_count": report.get("positive_count"),
        "schema": report.get("schema"),
    }


def _research_promotion_obligation_summary(
    manifest: Mapping[str, Any] | None,
    *,
    digest: str | None,
    schema: str,
) -> dict[str, Any]:
    expected = RESEARCH_PROMOTION_OBLIGATION_MANIFESTS.get(schema, {})
    fixtures = manifest.get("control_fixtures") if manifest is not None else None
    fixtures = fixtures if isinstance(fixtures, dict) else {}
    return {
        "manifest_path": expected.get("path"),
        "negative_cases_sha256": fixtures.get("negative_cases_sha256"),
        "obligation_digest": digest,
        "positive_cases_sha256": fixtures.get("positive_cases_sha256"),
        "schema": schema,
    }


def _check_research_promotion_schema_registry_research_only() -> BoundaryCheck:
    try:
        from tools.check_tight_argmax_m_source_certificate_20260630 import claim_promotion_checks
    except ImportError as exc:
        return BoundaryCheck(
            check_id="research_promotion_schema_registry_research_only",
            ok=False,
            evidence=json.dumps({"import_error": str(exc)}, sort_keys=True),
        )

    reports = {
        "theoremsearch_retrieval_promotion": theoremsearch_retrieval_promotion_checks(),
        "tight_argmax_claim_promotion": claim_promotion_checks(),
    }
    registry_manifest, registry_digest, manifest_findings = validate_research_promotion_registry_manifest_file()
    findings: list[dict[str, str]] = []
    obligations: dict[str, dict[str, Any]] = {}
    for finding in manifest_findings:
        with_report = dict(finding)
        with_report["report_id"] = "research_promotion_registry_manifest"
        findings.append(with_report)
    for report_id, report in reports.items():
        schema = str(report.get("schema"))
        obligation_manifest, obligation_digest, obligation_findings = (
            validate_research_promotion_obligation_manifest_file(report_id, report)
        )
        obligations[schema] = _research_promotion_obligation_summary(
            obligation_manifest,
            digest=obligation_digest,
            schema=schema,
        )
        for finding in obligation_findings:
            with_report = dict(finding)
            with_report["report_id"] = f"research_promotion_obligation_manifest:{report_id}"
            findings.append(with_report)
        for finding in validate_research_promotion_boundary(report):
            with_report = dict(finding)
            with_report["report_id"] = report_id
            findings.append(with_report)
    return BoundaryCheck(
        check_id="research_promotion_schema_registry_research_only",
        ok=not findings,
        evidence=json.dumps(
            {
                "findings": findings,
                "obligation_count": len(obligations),
                "obligations": {
                    schema: obligations[schema]
                    for schema in sorted(obligations)
                },
                "reports": {
                    report_id: _research_promotion_report_summary(report)
                    for report_id, report in sorted(reports.items())
                },
                "registry_digest": registry_digest,
                "registry_manifest_path": str(RESEARCH_PROMOTION_REGISTRY_MANIFEST_PATH.relative_to(REPO_ROOT)),
                "registry_manifest_schema": (
                    registry_manifest.get("schema") if registry_manifest is not None else None
                ),
                "registered_schemas": sorted(RESEARCH_PROMOTION_BOUNDARY_CONTRACTS),
                "registry_contract_count": len(RESEARCH_PROMOTION_BOUNDARY_CONTRACTS),
            },
            sort_keys=True,
        ),
    )


def _check_m6_writer_inventory_research_only(root: Path) -> BoundaryCheck:
    try:
        from tools.check_m6_writer_inventory import check_m6_writer_inventory
    except ImportError as exc:
        return BoundaryCheck(
            check_id="m6_writer_inventory_research_only",
            ok=False,
            evidence=json.dumps({"import_error": str(exc)}, sort_keys=True),
        )
    report = check_m6_writer_inventory(root)
    entries = report.get("entrypoints")
    entries = entries if isinstance(entries, list) else []
    legacy_entries = [
        entry
        for entry in entries
        if isinstance(entry, dict) and str(entry.get("m6_mount_status", "")).startswith("UNMOUNTED")
    ]
    ok = (
        report.get("ok") is True
        and report.get("m6_production_mounted") is False
        and report.get("production_authority") is False
        and report.get("release_ready") is False
        and report.get("release_gate_status") == "BLOCKED_OPEN_COVERAGE"
        and report.get("writers_without_coverage") == []
        and report.get("coverage_row_count") == report.get("entrypoint_count")
        and bool(legacy_entries)
    )
    return BoundaryCheck(
        check_id="m6_writer_inventory_research_only",
        ok=ok,
        evidence=json.dumps(
            {
                "coverage_row_count": report.get("coverage_row_count"),
                "entrypoint_count": report.get("entrypoint_count"),
                "findings": report.get("findings"),
                "m6_production_mounted": report.get("m6_production_mounted"),
                "production_authority": report.get("production_authority"),
                "release_gate_status": report.get("release_gate_status"),
                "release_ready": report.get("release_ready"),
                "unmounted_entrypoint_count": report.get("unmounted_entrypoint_count"),
                "writers_without_coverage": report.get("writers_without_coverage"),
            },
            sort_keys=True,
        ),
    )


def _requirement_reports(checks: Iterable[BoundaryCheck]) -> list[dict[str, Any]]:
    by_id = {check.check_id: check for check in checks}
    reports: list[dict[str, Any]] = []
    for requirement in PRODUCTION_BOUNDARY_REQUIREMENTS:
        check_ids = tuple(str(check_id) for check_id in requirement["check_ids"])
        missing = [check_id for check_id in check_ids if check_id not in by_id]
        failing = [check_id for check_id in check_ids if check_id in by_id and not by_id[check_id].ok]
        reports.append(
            {
                "requirement_id": requirement["requirement_id"],
                "objective": requirement["objective"],
                "ok": not missing and not failing,
                "check_ids": list(check_ids),
                "missing_check_ids": missing,
                "failing_check_ids": failing,
            }
        )
    return reports


def audit_production_boundary(root: Path = REPO_ROOT) -> dict[str, Any]:
    checks = [
        _check_dex_config_defaults(),
        _check_core_dex_config_defaults(),
        _check_named_safe_profile_helpers(),
        _check_nonce_free_batch_rejected(),
        _check_strong_settlement_validator(root),
        _check_no_unsafe_config_literals(root),
        _check_no_legacy_settlement_profile_literals(root),
        _check_direct_apply_operations_unexposed(root),
        _check_api_server_read_only_boundary(root),
        _check_tau_testnet_uses_dex_engine_boundary(root),
        _check_supported_runtime_doc_scope(root),
        _check_public_operator_node_preflight_blocks_unsigned_testnet_mutation(),
        _check_research_promotion_schema_registry_research_only(),
        _check_m6_writer_inventory_research_only(root),
    ]
    requirements = _requirement_reports(checks)
    return {
        "schema": "zenodex/production_boundary_audit/v0",
        "ok": all(check.ok for check in checks) and all(item["ok"] for item in requirements),
        "checks": [check.to_dict() for check in checks],
        "requirements": requirements,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    payload = audit_production_boundary(args.root)
    if args.json or not payload["ok"]:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print("production boundary ok")
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
