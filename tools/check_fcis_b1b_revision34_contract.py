#!/usr/bin/env python3
"""Fail-closed structural checker for FCIS B1B Revision 3.4 and B1B-1."""

from __future__ import annotations

import argparse
import ast
import json
import re
from dataclasses import dataclass
from pathlib import Path

from tools.fcis_b1b_revision34_adversarial_model import build_report

REVISION_PATH = Path(
    "docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md"
)
CONTENT_VALIDATION_PATH = Path(
    "src/core/fcis_fee_distribution_configuration_content_validation.py"
)
PYTHON_PATHS = (
    Path("src/core/fcis_b1b_authority_values.py"),
    Path("src/core/fcis_b1b_authority_schema.py"),
    Path("src/core/fcis_b1b_authority_admission.py"),
    Path("src/core/fcis_b1b_authority_codec.py"),
)
RUST_PATH = Path("rust-runtime/crates/zenodex-runtime-core/src/fcis_b1b_authority.rs")
RUST_LIB_PATH = Path("rust-runtime/crates/zenodex-runtime-core/src/lib.rs")
FIXTURE_PATH = Path("tests/fixtures/fcis_b1b_authority_v2_golden.json")
BUILDER_PATH = Path("tools/build_fcis_b1b_authority_v2_golden.py")
MODEL_PATH = Path("tools/fcis_b1b_revision34_adversarial_model.py")
TEST_PATHS = (
    Path("tests/core/test_fcis_b1b_authority_values.py"),
    Path("tests/core/test_fcis_b1b_authority_admission.py"),
    Path("tests/core/test_fcis_b1b_authority_golden.py"),
    Path("tests/core/test_fcis_fee_distribution_configuration_content_validation.py"),
    Path("tests/tools/test_fcis_b1b_revision34_adversarial_model.py"),
    Path("tests/tools/test_check_fcis_b1b_revision34_contract.py"),
)

REQUIRED_PATHS = (
    REVISION_PATH,
    CONTENT_VALIDATION_PATH,
    *PYTHON_PATHS,
    RUST_PATH,
    RUST_LIB_PATH,
    FIXTURE_PATH,
    BUILDER_PATH,
    MODEL_PATH,
    *TEST_PATHS,
)

FORBIDDEN_AUTHORITY_SYMBOLS = (
    "PinnedDeploymentBootstrapVerifierV2",
    "VerifiedV1ToV2MigrationAuthorityV2",
    "V1ToV2MigrationCandidateV2",
    "FCISCommittedStateV2",
    "StateBoundFeeDistributionConfigurationV2",
    "TransitionCauseV2",
    "V2EvaluationCandidate",
    "ConfigurationUpdateCommandClaimV2",
    "AuthenticatedConfigurationUpdateCommandV2",
    "V2CommitBundle",
    "PublishedFCISV2Commit",
)
FORBIDDEN_IMPORT_PARTS = (
    "settlement",
    "state_transitions",
    "commit_bundle",
    "decision",
    "outbox",
    "integration",
    "proof",
    "shell",
    "runtime",
)
REQUIRED_VALUE_CLASSES = (
    "FCISAuthorityHeaderSourceV2",
    "DeploymentBootstrapAnchorClaimSourceV2",
    "V1ToV2MigrationManifestSourceV2",
    "FCISAuthorityHeaderV2",
    "DeploymentBootstrapAnchorClaimV2",
    "V1ToV2MigrationManifestV2",
    "B1BAuthorityAdmissionRejectV2",
)
REQUIRED_SCHEMA_IDS = (
    "zenodex/fcis/state/authority-header/v2",
    "zenodex/fcis/deployment/bootstrap-anchor-claim/v2",
    "zenodex/fcis/migration/v1-to-v2-manifest/v2",
)
REQUIRED_ROOT_DOMAINS = (
    "fcis_deployment_bootstrap_anchor_claim",
    "fcis_v1_to_v2_migration_manifest",
)


@dataclass(frozen=True, slots=True)
class Finding:
    code: str
    path: str
    detail: str


@dataclass(frozen=True, slots=True)
class Report:
    ok: bool
    findings: tuple[Finding, ...]
    model: dict[str, object]


def _read(root: Path, path: Path) -> str:
    return (root / path).read_text(encoding="utf-8")


def _decorator_name(node: ast.expr) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Call):
        return _decorator_name(node.func)
    return None


def _is_final_dataclass(node: ast.ClassDef) -> bool:
    names = {_decorator_name(decorator) for decorator in node.decorator_list}
    if "final" not in names or "dataclass" not in names:
        return False
    for decorator in node.decorator_list:
        if not isinstance(decorator, ast.Call) or _decorator_name(decorator) != "dataclass":
            continue
        keywords = {keyword.arg: keyword.value for keyword in decorator.keywords}
        frozen = keywords.get("frozen")
        slots = keywords.get("slots")
        return (
            isinstance(frozen, ast.Constant)
            and frozen.value is True
            and isinstance(slots, ast.Constant)
            and slots.value is True
        )
    return False


def _extract_call_block(text: str, prefix: str) -> str | None:
    start = text.find(prefix)
    if start < 0:
        return None
    depth = 0
    opened = False
    for index in range(start, len(text)):
        character = text[index]
        if character == "(":
            depth += 1
            opened = True
        elif character == ")" and opened:
            depth -= 1
            if depth == 0:
                return text[start : index + 1]
    return None


def _check_revision_document(root: Path, findings: list[Finding]) -> None:
    text = _read(root, REVISION_PATH)
    pipeline = (
        "closed structural admission",
        "call validate_fee_distribution_configuration_claim_v2",
        "call revalidate_fee_distribution_configuration_claim_v2",
        "recompute policy_root",
        "recompute configuration_root",
        "embedded claim.configuration_root = recomputed configuration_root",
    )
    positions = [text.find(token) for token in pipeline]
    if any(position < 0 for position in positions):
        missing = [
            token
            for token, position in zip(pipeline, positions, strict=True)
            if position < 0
        ]
        findings.append(Finding("REV34_PIPELINE_MISSING", str(REVISION_PATH), ", ".join(missing)))
    elif positions != sorted(positions):
        findings.append(
            Finding(
                "REV34_PIPELINE_ORDER",
                str(REVISION_PATH),
                "B1A validation must precede root authority",
            )
        )
    required_relations = (
        "validated_proposed.configuration_root",
        "reauthenticated_update_command",
        "proposed_fee_distribution_configuration_root",
        "validated_initial_configuration",
        "V2EvaluationCandidate(",
        "V2Decision(",
        "V2CommitBundle(",
        "Exactly one assignment accepts",
    )
    for token in required_relations:
        if token not in text:
            findings.append(Finding("REV34_RELATION_MISSING", str(REVISION_PATH), token))
    candidate = _extract_call_block(text, "V2EvaluationCandidate(")
    if candidate is None:
        findings.append(Finding("REV34_CANDIDATE_MISSING", str(REVISION_PATH), "candidate block"))
    elif re.search(r"\breceipt\b", candidate):
        findings.append(
            Finding(
                "REV34_RECEIPT_CYCLE",
                str(REVISION_PATH),
                "receipt appears inside V2EvaluationCandidate",
            )
        )
    cause = _extract_call_block(text, "TransitionCauseV2(")
    if cause is None:
        findings.append(Finding("REV34_CAUSE_MISSING", str(REVISION_PATH), "cause block"))
    elif "decision_hash" in cause or "candidate_hash" in cause or "receipt" in cause:
        findings.append(
            Finding(
                "REV34_CAUSE_DOWNSTREAM_HASH",
                str(REVISION_PATH),
                "transition cause contains downstream data",
            )
        )
    if "admission result is cast to ValidatedFeeDistributionConfigurationClaimV2" not in text:
        findings.append(
            Finding(
                "REV34_MUTANT_INVENTORY",
                str(REVISION_PATH),
                "missing admission-to-validated cast mutant",
            )
        )


def _check_python_carriers(root: Path, findings: list[Finding]) -> None:
    texts = {path: _read(root, path) for path in PYTHON_PATHS}
    combined = "\n".join(texts.values())
    for symbol in FORBIDDEN_AUTHORITY_SYMBOLS:
        if symbol in combined:
            findings.append(Finding("B1B1_PREMATURE_AUTHORITY", "python carriers", symbol))
    transition_pattern = r"def\s+([A-Za-z0-9_]*(?:advance|update)[A-Za-z0-9_]*)\s*\("
    for match in re.finditer(transition_pattern, combined):
        findings.append(
            Finding("B1B1_BARE_HEADER_TRANSITION", "python carriers", match.group(1))
        )
    for path, text in texts.items():
        tree = ast.parse(text, filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                names: list[str] = []
                if isinstance(node, ast.Import):
                    names = [alias.name for alias in node.names]
                elif node.module:
                    names = [node.module]
                for name in names:
                    if any(part in name for part in FORBIDDEN_IMPORT_PARTS):
                        findings.append(Finding("B1B1_FORBIDDEN_IMPORT", str(path), name))
    value_tree = ast.parse(texts[PYTHON_PATHS[0]], filename=str(PYTHON_PATHS[0]))
    classes = {node.name: node for node in value_tree.body if isinstance(node, ast.ClassDef)}
    for class_name in REQUIRED_VALUE_CLASSES:
        node = classes.get(class_name)
        if node is None:
            findings.append(Finding("B1B1_VALUE_MISSING", str(PYTHON_PATHS[0]), class_name))
        elif not _is_final_dataclass(node):
            findings.append(
                Finding("B1B1_VALUE_NOT_OWNED", str(PYTHON_PATHS[0]), class_name)
            )
    for schema_id in REQUIRED_SCHEMA_IDS:
        if schema_id not in combined:
            findings.append(Finding("B1B1_SCHEMA_ID_MISSING", "python carriers", schema_id))
    for domain in REQUIRED_ROOT_DOMAINS:
        if domain not in texts[PYTHON_PATHS[3]]:
            findings.append(Finding("B1B1_ROOT_DOMAIN_MISSING", str(PYTHON_PATHS[3]), domain))
    required_decoder_tokens = (
        "object_pairs_hook=_pairs_hook",
        "DUPLICATE_FIELD",
        "UNKNOWN_FIELD",
        "MISSING_FIELD",
        "NONCANONICAL_ENCODING",
        "canonical_json_bytes(envelope)",
    )
    for token in required_decoder_tokens:
        if token not in texts[PYTHON_PATHS[2]]:
            findings.append(Finding("B1B1_DECODER_GAP", str(PYTHON_PATHS[2]), token))


def _check_rust_carriers(root: Path, findings: list[Finding]) -> None:
    text = _read(root, RUST_PATH)
    for required in (
        "pub struct FCISAuthorityHeaderV2",
        "pub struct DeploymentBootstrapAnchorClaimV2",
        "pub struct V1ToV2MigrationManifestV2",
        "canonical_bootstrap_anchor_claim_root_v2",
        "canonical_v1_to_v2_migration_manifest_root_v2",
        "BigUint",
    ):
        if required not in text:
            findings.append(Finding("B1B1_RUST_GAP", str(RUST_PATH), required))
    for symbol in FORBIDDEN_AUTHORITY_SYMBOLS:
        if symbol in text:
            findings.append(Finding("B1B1_RUST_PREMATURE_AUTHORITY", str(RUST_PATH), symbol))
    if "pub struct FCISAuthorityHeaderV2 {\n    pub " in text:
        findings.append(
            Finding("B1B1_RUST_PUBLIC_FIELDS", str(RUST_PATH), "authority header fields")
        )
    for domain in REQUIRED_ROOT_DOMAINS:
        if domain not in text:
            findings.append(Finding("B1B1_RUST_ROOT_DOMAIN", str(RUST_PATH), domain))
    lib_text = _read(root, RUST_LIB_PATH)
    if "pub mod fcis_b1b_authority;" not in lib_text:
        findings.append(
            Finding("B1B1_RUST_MODULE_EXPORT", str(RUST_LIB_PATH), "fcis_b1b_authority")
        )


def _check_fixture_and_model(root: Path, findings: list[Finding]) -> dict[str, object]:
    document = json.loads(_read(root, FIXTURE_PATH))
    cases = document.get("cases")
    if not isinstance(cases, list) or len(cases) != 5:
        findings.append(Finding("B1B1_FIXTURE_CASES", str(FIXTURE_PATH), "expected five cases"))
    else:
        ids = {case.get("id") for case in cases if isinstance(case, dict)}
        expected = {
            "authority_header_initial",
            "authority_header_u256_maximum",
            "bootstrap_anchor_claim",
            "v1_to_v2_migration_manifest",
            "structurally_exact_wrong_fixed_constants",
        }
        if ids != expected:
            findings.append(Finding("B1B1_FIXTURE_IDS", str(FIXTURE_PATH), repr(ids)))
    model = build_report()
    if model.get("cases") != 1_024 or model.get("safe_accepts") != 1:
        findings.append(Finding("REV34_MODEL_TOTALITY", str(MODEL_PATH), repr(model)))
    if not model.get("receipt_cycle_mutant_rejected"):
        findings.append(Finding("REV34_MODEL_CYCLE", str(MODEL_PATH), repr(model)))
    if int(model.get("unsafe_semantically_invalid_accepts", 0)) <= 0:
        findings.append(Finding("REV34_NEGATIVE_CONTROL", str(MODEL_PATH), repr(model)))
    return model


def check_repository(root: Path) -> Report:
    root = root.resolve()
    findings: list[Finding] = []
    for path in REQUIRED_PATHS:
        if not (root / path).is_file():
            findings.append(Finding("MISSING_PATH", str(path), "required file is absent"))
    if findings:
        return Report(False, tuple(findings), {})
    _check_revision_document(root, findings)
    content_validation = _read(root, CONTENT_VALIDATION_PATH)
    for token in (
        "validate_fee_distribution_configuration_claim_v2",
        "revalidate_fee_distribution_configuration_claim_v2",
        "_fresh_owned_claim_v2",
        "type(first) is not ValidatedFeeDistributionConfigurationClaimV2",
        "type(second) is not ValidatedFeeDistributionConfigurationClaimV2",
    ):
        if token not in content_validation:
            findings.append(
                Finding("REV34_CONTENT_VALIDATION_GAP", str(CONTENT_VALIDATION_PATH), token)
            )
    _check_python_carriers(root, findings)
    _check_rust_carriers(root, findings)
    model = _check_fixture_and_model(root, findings)
    return Report(not findings, tuple(findings), model)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = check_repository(args.root)
    payload = {
        "schema": "zenodex/fcis/b1b-revision34-contract-check/v1",
        "ok": report.ok,
        "findings": [
            {"code": finding.code, "path": finding.path, "detail": finding.detail}
            for finding in report.findings
        ],
        "model": report.model,
    }
    if args.json:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(f"ok={report.ok}")
        for finding in report.findings:
            print(f"{finding.code}: {finding.path}: {finding.detail}")
    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
