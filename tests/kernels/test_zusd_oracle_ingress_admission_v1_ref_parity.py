from __future__ import annotations

import hashlib
import importlib.util
import sys
from itertools import product
from pathlib import Path
from types import ModuleType

from src.core.zusd_oracle_ingress_admission import (
    ZUSDOracleEvidenceProfile,
    ZUSDOracleIngressAction,
    ZUSDOracleIngressEvidence,
    ZUSDOracleIngressViolation,
    evaluate_zusd_oracle_ingress_admission,
)

PROFILE_CODE = {
    ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0: 0,
    ZUSDOracleEvidenceProfile.FINALIZED_O3_V1: 1,
}
ACTION_CODE = {
    ZUSDOracleIngressAction.ADVANCE_EPOCH: 0,
    ZUSDOracleIngressAction.BOOTSTRAP_ORACLE: 1,
    ZUSDOracleIngressAction.ORACLE_REPORT: 2,
    ZUSDOracleIngressAction.ORACLE_COMMIT: 3,
    ZUSDOracleIngressAction.LIQUIDATE: 4,
    ZUSDOracleIngressAction.MINT_ZUSD: 5,
}
VIOLATION_EFFECT = {
    ZUSDOracleIngressViolation.CONFIGURED_SENDER_REQUIRED: (
        "configured_sender_required"
    ),
    ZUSDOracleIngressViolation.FINALIZED_CONTEXT_REQUIRED: (
        "finalized_context_required"
    ),
    ZUSDOracleIngressViolation.AGGREGATE_PROPOSAL_REQUIRED: (
        "aggregate_proposal_required"
    ),
    ZUSDOracleIngressViolation.EXACT_PENDING_SNAPSHOT_REQUIRED: (
        "exact_pending_snapshot_required"
    ),
    ZUSDOracleIngressViolation.COMMITTED_ACTIVE_SNAPSHOT_REQUIRED: (
        "committed_active_snapshot_required"
    ),
    ZUSDOracleIngressViolation.CRITICAL_ACTION_AUTHORIZATION_REQUIRED: (
        "critical_action_authorization_required"
    ),
}


def _paths() -> tuple[Path, Path]:
    root = Path(__file__).resolve().parents[2]
    return (
        root / "src/kernels/dex/zusd_oracle_ingress_admission_v1.yaml",
        root
        / "generated/zusd_oracle_ingress_admission_v1/python_ref"
        / "zusd_oracle_ingress_admission_v1_ref.py",
    )


def _load_reference() -> ModuleType:
    _, reference = _paths()
    spec = importlib.util.spec_from_file_location(
        "zusd_oracle_ingress_admission_v1_ref",
        reference,
    )
    if spec is None or spec.loader is None:
        raise AssertionError("could not load generated ESSO Python reference")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_generated_reference_is_hash_bound_to_versioned_esso_ir() -> None:
    model, reference = _paths()
    ir_hash = "sha256:" + hashlib.sha256(model.read_bytes()).hexdigest()
    source = reference.read_text(encoding="utf-8")
    assert f"Source SHA256: {ir_hash}" in source
    assert ir_hash == (
        "sha256:fa2f230bbe2fc52dd96fba01162639db8e4d1886ada9356ab729a4679270ebca"
    )
    assert "IR hash: sha256:7bc00f4b2e8b25c8dc254790cec1a506ab4a97207a4f28469fd1ed7a040fd32b" in source


def test_pure_core_matches_generated_reference_for_all_768_control_cases() -> None:
    reference = _load_reference()
    count = 0
    for profile, action, bits in product(
        ZUSDOracleEvidenceProfile,
        ZUSDOracleIngressAction,
        product((False, True), repeat=6),
    ):
        evidence = ZUSDOracleIngressEvidence(*bits)
        core = evaluate_zusd_oracle_ingress_admission(
            profile=profile,
            action=action,
            evidence=evidence,
        )
        result = reference.step(
            reference.State(
                profile_code=PROFILE_CODE[profile],
                action_code=ACTION_CODE[action],
                configured_sender_bound=int(evidence.configured_sender_bound),
                finalized_context_bound=int(evidence.finalized_context_bound),
                aggregate_proposal_bound=int(evidence.aggregate_proposal_bound),
                pending_snapshot_bound=int(evidence.pending_snapshot_bound),
                committed_active_snapshot_bound=int(
                    evidence.committed_active_snapshot_bound
                ),
                critical_action_authorization_bound=int(
                    evidence.critical_action_authorization_bound
                ),
            ),
            reference.Command(tag="evaluate_oracle_ingress", args={}),
        )
        assert result.ok is True
        assert result.effects is not None
        expected = {name: False for name in VIOLATION_EFFECT.values()}
        for violation in core.violations:
            expected[VIOLATION_EFFECT[violation]] = True
        expected["admitted"] = core.admitted
        assert result.effects == expected
        count += 1
    assert count == 768
