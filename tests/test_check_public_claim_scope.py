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


def test_release_bundle_claim_docs_are_scanned_for_public_scope() -> None:
    checked = set(checked_public_claim_paths(root=ROOT))

    # REVIEW [B -> A-]: these docs ship in the operator/release evidence bundle
    # but were absent from the public claim scanner. That let stale broad
    # product/testnet wording survive after the spot-DEX CBC matrix computed
    # production_security_claim=True.
    assert {
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        "docs/DEX_SURFACE_STATUS_2026_06_03.md",
        "docs/PERPS_NP_TESTNET_STATUS.md",
        "docs/RISC0_RELEASE_BINARY_ARTIFACTS_2026_06_02.md",
        "docs/zenodex_perps_np_state_proof_risc0_v1.md",
        "docs/zenodex_zusd_state_proof_risc0_v1.md",
    } <= checked


def test_perps_np_status_requires_scoped_false_claim_anchor() -> None:
    violations = check_required_anchors(
        "docs/PERPS_NP_TESTNET_STATUS.md",
        "Status: FAKE-VALUE PUBLIC TESTNET. production_security_claim = false on every surface.",
    )

    assert {violation.rule_id for violation in violations} == {"missing_scope_anchor"}


def test_release_gate_runs_rust_public_claim_scope_mirror() -> None:
    release_gate = (ROOT / "tools/run_release_gate.sh").read_text(encoding="utf-8")

    # REVIEW [B -> A-]: the public-claim gate was Python-only. The release gate
    # now requires the Rust mirror, so scoped-claim drift has two implementations
    # reviewing the shipped docs.
    assert "public claim scope (Rust mirror)" in release_gate
    assert "cargo run --quiet --bin zenodex-runtime -- public-claim-scope" in release_gate


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


def test_rejects_verifiably_confidential_overclaim() -> None:
    violations = scan_forbidden_claims(
        "tools/dex-ui/README.md",
        "The TEE lane is verifiably confidential for all private routing.",
    )

    assert [violation.rule_id for violation in violations] == [
        "confidential_verifiable_overclaim"
    ]


def test_rejects_tee_hardware_confidentiality_proof_overclaim() -> None:
    violations = scan_forbidden_claims(
        "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
        "The TEE receipt proves hardware confidentiality for private routing.",
    )

    assert [violation.rule_id for violation in violations] == [
        "tee_hardware_confidentiality_proof_overclaim"
    ]


def test_allows_explicit_negative_hardware_confidentiality_scope_line() -> None:
    violations = scan_forbidden_claims(
        "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
        "It does not prove TEE hardware confidentiality or hide on-chain execution.",
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
