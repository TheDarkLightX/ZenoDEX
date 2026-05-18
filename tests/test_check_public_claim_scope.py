from __future__ import annotations

from pathlib import Path

from tools.check_public_claim_scope import (
    check_claims_registry_public_artifact_paths,
    check_public_claim_scope,
    check_required_anchors,
    checked_public_claim_paths,
    scan_forbidden_claims,
)

ROOT = Path(__file__).resolve().parents[1]


def test_current_public_claim_docs_stay_scoped() -> None:
    assert check_public_claim_scope(root=ROOT) == []


def test_claims_registry_is_scanned_for_public_scope() -> None:
    from tools.check_public_claim_scope import checked_public_claim_paths

    assert "docs/claims_registry.yaml" in checked_public_claim_paths(root=ROOT)


def test_rejects_direct_upba_v2_optimal_overclaim() -> None:
    violations = scan_forbidden_claims(
        "README.md",
        "UPBA v2 is globally optimal across rational prices.",
    )

    assert [violation.rule_id for violation in violations] == [
        "upba_v2_direct_optimal_overclaim"
    ]


def test_rejects_upba_v2_optimality_proven_overclaim() -> None:
    violations = scan_forbidden_claims(
        "README.md",
        "UPBA v2 optimality is proven for all solver outputs.",
    )

    assert [violation.rule_id for violation in violations] == [
        "upba_v2_optimality_proven_overclaim"
    ]


def test_rejects_risc0_full_python_runtime_overclaim() -> None:
    violations = scan_forbidden_claims(
        "README.md",
        "Risc0 proves the full Python ZenoDEX runtime.",
    )

    assert [violation.rule_id for violation in violations] == [
        "risc0_full_python_overclaim"
    ]


def test_rejects_risc0_full_python_execution_proof_overclaim() -> None:
    violations = scan_forbidden_claims(
        "README.md",
        "Risc0 gives a full Python execution proof.",
    )

    assert [violation.rule_id for violation in violations] == [
        "risc0_full_python_execution_proof_overclaim"
    ]


def test_rejects_tee_complete_confidential_network_overclaim() -> None:
    violations = scan_forbidden_claims(
        "README.md",
        "TEE provides a complete confidential network for all trading.",
    )

    assert [violation.rule_id for violation in violations] == [
        "tee_complete_confidential_network_overclaim"
    ]


def test_allows_explicit_negative_tee_scope_line() -> None:
    violations = scan_forbidden_claims(
        "docs/claims_registry.yaml",
        "This does not prove TEE hardware soundness or a complete confidential network.",
    )

    assert violations == []


def test_rejects_zenocover_insurance_product_overclaim() -> None:
    violations = scan_forbidden_claims(
        "docs/ZENOCOVER_LP_LOSS_COVER_V1.md",
        "ZenoCover offers insurance policies for protocol users.",
    )

    assert [violation.rule_id for violation in violations] == [
        "zenocover_insurance_product_overclaim"
    ]


def test_rejects_zenocover_live_purchase_overclaim() -> None:
    violations = scan_forbidden_claims(
        "docs/ZENOCOVER_LP_LOSS_COVER_V1.md",
        "ZenoCover is live and open for purchase.",
    )

    assert [violation.rule_id for violation in violations] == [
        "zenocover_regulated_launch_overclaim"
    ]


def test_rejects_internal_registry_evidence_path() -> None:
    violations = check_claims_registry_public_artifact_paths(
        "docs/claims_registry.yaml",
        """
schema: zenodex/claims-registry/v1
meta: {}
claims:
  - id: py:test
    status: supported
    layer: assurance
    statement: scoped
    evidence:
      kind: pytest
      check:
        - cmd: python3 tools/check.py internal/private_manifest.json
      files:
        - runs/local_replay.json
""",
    )

    assert [violation.rule_id for violation in violations] == [
        "claims_registry_internal_or_runs_evidence_path",
        "claims_registry_internal_or_runs_command_path",
    ]


def test_required_readme_scope_anchor_is_enforced() -> None:
    violations = check_required_anchors(
        "README.md",
        "ZenoDEX is a public-testnet candidate.",
    )

    assert {violation.rule_id for violation in violations} == {"missing_scope_anchor"}


def test_missing_optional_claim_docs_are_not_required(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text("placeholder", encoding="utf-8")

    assert checked_public_claim_paths(
        root=tmp_path,
        paths=("README.md",),
        optional_paths=("docs/UPBA_V2_CERTIFICATE.md",),
    ) == ["README.md"]
