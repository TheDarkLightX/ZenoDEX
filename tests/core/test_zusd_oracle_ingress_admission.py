from __future__ import annotations

from itertools import product

import pytest

from src.core.zusd_oracle_ingress_admission import (
    ZUSD_ORACLE_INGRESS_ADMISSION_NONCLAIMS,
    ZUSDOracleEvidenceProfile,
    ZUSDOracleIngressAction,
    ZUSDOracleIngressEvidence,
    ZUSDOracleIngressViolation,
    evaluate_zusd_oracle_ingress_admission,
)


def _evidence(bits: tuple[bool, ...]) -> ZUSDOracleIngressEvidence:
    return ZUSDOracleIngressEvidence(*bits)


def test_dev_profile_retains_only_the_explicit_legacy_sender_contract() -> None:
    for action in ZUSDOracleIngressAction:
        rejected = evaluate_zusd_oracle_ingress_admission(
            profile=ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0,
            action=action,
            evidence=ZUSDOracleIngressEvidence(),
        )
        if action in {
            ZUSDOracleIngressAction.LIQUIDATE,
            ZUSDOracleIngressAction.MINT_ZUSD,
        }:
            assert rejected.admitted is True
            assert rejected.violations == ()
        else:
            assert rejected.violations == (
                ZUSDOracleIngressViolation.CONFIGURED_SENDER_REQUIRED,
            )
        accepted = evaluate_zusd_oracle_ingress_admission(
            profile=ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0,
            action=action,
            evidence=ZUSDOracleIngressEvidence(configured_sender_bound=True),
        )
        assert accepted.admitted is True


def test_strict_commit_is_permissionless_after_exact_pending_and_finality_bind() -> None:
    decision = evaluate_zusd_oracle_ingress_admission(
        profile=ZUSDOracleEvidenceProfile.FINALIZED_O3_V1,
        action=ZUSDOracleIngressAction.ORACLE_COMMIT,
        evidence=ZUSDOracleIngressEvidence(
            configured_sender_bound=False,
            finalized_context_bound=True,
            pending_snapshot_bound=True,
        ),
    )

    assert decision.admitted is True
    assert decision.violations == ()


def test_strict_proposal_needs_f01_bound_aggregate_and_finality_not_consumer_o3() -> None:
    decision = evaluate_zusd_oracle_ingress_admission(
        profile=ZUSDOracleEvidenceProfile.FINALIZED_O3_V1,
        action=ZUSDOracleIngressAction.ORACLE_REPORT,
        evidence=ZUSDOracleIngressEvidence(
            finalized_context_bound=True,
            aggregate_proposal_bound=True,
            critical_action_authorization_bound=False,
        ),
    )

    assert decision.admitted is True
    assert decision.violations == ()


def test_strict_liquidation_requires_committed_active_context_and_action_o3() -> None:
    missing = evaluate_zusd_oracle_ingress_admission(
        profile=ZUSDOracleEvidenceProfile.FINALIZED_O3_V1,
        action=ZUSDOracleIngressAction.LIQUIDATE,
        evidence=ZUSDOracleIngressEvidence(),
    )
    accepted = evaluate_zusd_oracle_ingress_admission(
        profile=ZUSDOracleEvidenceProfile.FINALIZED_O3_V1,
        action=ZUSDOracleIngressAction.LIQUIDATE,
        evidence=ZUSDOracleIngressEvidence(
            finalized_context_bound=True,
            committed_active_snapshot_bound=True,
            critical_action_authorization_bound=True,
        ),
    )

    assert missing.violations == (
        ZUSDOracleIngressViolation.FINALIZED_CONTEXT_REQUIRED,
        ZUSDOracleIngressViolation.COMMITTED_ACTIVE_SNAPSHOT_REQUIRED,
        ZUSDOracleIngressViolation.CRITICAL_ACTION_AUTHORIZATION_REQUIRED,
    )
    assert accepted.admitted is True


def test_strict_mint_accepts_only_after_active_context_and_exact_action_o3() -> None:
    accepted = evaluate_zusd_oracle_ingress_admission(
        profile=ZUSDOracleEvidenceProfile.FINALIZED_O3_V1,
        action=ZUSDOracleIngressAction.MINT_ZUSD,
        evidence=ZUSDOracleIngressEvidence(
            finalized_context_bound=True,
            committed_active_snapshot_bound=True,
            critical_action_authorization_bound=True,
        ),
    )

    assert accepted.admitted is True
    assert accepted.violations == ()


def test_admission_is_total_and_acceptance_equals_empty_violations() -> None:
    cases = product(
        ZUSDOracleEvidenceProfile,
        ZUSDOracleIngressAction,
        product((False, True), repeat=6),
    )
    count = 0
    for profile, action, bits in cases:
        decision = evaluate_zusd_oracle_ingress_admission(
            profile=profile,
            action=action,
            evidence=_evidence(tuple(bits)),
        )
        assert decision.admitted is (not decision.violations)
        assert len(decision.violations) == len(set(decision.violations))
        count += 1
    assert count == 768


def test_port_kernel_explicitly_excludes_external_verifier_failure_detail() -> None:
    assert "external_verifier_failure_detail" in (
        ZUSD_ORACLE_INGRESS_ADMISSION_NONCLAIMS
    )
    assert "complete_f03_oracle_fsm" in ZUSD_ORACLE_INGRESS_ADMISSION_NONCLAIMS


@pytest.mark.parametrize("bad", (0, 1, "true", None))
def test_evidence_rejects_non_boolean_facts(bad: object) -> None:
    with pytest.raises(TypeError, match="configured_sender_bound"):
        ZUSDOracleIngressEvidence(configured_sender_bound=bad)  # type: ignore[arg-type]
