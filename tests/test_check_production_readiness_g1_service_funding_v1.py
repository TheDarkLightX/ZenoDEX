from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from tools import check_production_readiness_g1_service_funding_v1 as checker
from tools import production_readiness_g1_service_funding_contract_v1 as contract


def _root(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _policy(
    *,
    role_id: str = "proof_prover_and_proof_miner",
    funding_source: contract.FundingSourceV1 = (
        contract.FundingSourceV1.FINALIZED_PROTOCOL_REVENUE_PREFUND
    ),
    opening_reserve_atoms: int = 300,
    fixed_atoms_per_period: int = 10,
    maximum_jobs_per_period: int = 2,
    maximum_atoms_per_job: int = 20,
    period_cap_atoms: int = 50,
    target_prefund_periods: int = 6,
) -> contract.ServiceBudgetPolicyV1:
    return contract.ServiceBudgetPolicyV1(
        role_id=role_id,
        payment_asset_id="USDC",
        funding_source=funding_source,
        opening_reserve_atoms=opening_reserve_atoms,
        fixed_atoms_per_period=fixed_atoms_per_period,
        maximum_jobs_per_period=maximum_jobs_per_period,
        maximum_atoms_per_job=maximum_atoms_per_job,
        period_cap_atoms=period_cap_atoms,
        target_prefund_periods=target_prefund_periods,
        period_length_blocks=100,
        policy_root=_root(f"policy:{role_id}"),
    )


def _payment(
    *,
    kind: contract.ServicePaymentKindV1,
    amount_atoms: int,
    period_index: int = 0,
    job_label: str = "job:1",
) -> contract.ServicePaymentV1:
    return contract.ServicePaymentV1(
        role_id="proof_prover_and_proof_miner",
        payment_asset_id="USDC",
        payment_kind=kind,
        period_index=period_index,
        job_id=_root(job_label),
        claimant_id="PROVER_001",
        requested_atoms=amount_atoms,
        admitted_work_witness_root=_root(f"witness:{job_label}"),
    )


def _opened(
    policy: contract.ServiceBudgetPolicyV1,
) -> contract.ServiceBudgetStateV1:
    outcome = contract.open_service_budget_v1(policy, initial_period_index=0)
    assert isinstance(outcome, contract.ServiceBudgetOpenAcceptV1)
    return outcome.state


def test_artifact_is_exact_and_keeps_service_funding_unselected() -> None:
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["activation_allowed"] is False
    assert report["production_ready"] is False
    assert report["selected_budget_count"] == 0
    assert document["status"] == "RESEARCH_ONLY_UNSELECTED"
    assert document["production_promotion"] is False


def test_participant_registry_covers_exact_22_roles() -> None:
    registry = contract.participant_funding_registry_v1()

    assert set(registry) == contract.ALL_PARTICIPANT_IDS
    assert len(registry) == 22
    assert set(contract.SELECTED_ROLE_BUDGETS) == contract.BUDGET_ELIGIBLE_ROLE_IDS
    assert all(value is None for value in contract.SELECTED_ROLE_BUDGETS.values())


def test_property_and_distribution_roles_cannot_open_service_budgets() -> None:
    for role_id in (
        "liquidity_provider",
        "tau_depositor_and_withdrawer",
        "community_testnet_and_usage_award_recipient",
        "founder_team_partner_and_capital_recipient",
        "protocol_treasury_reserve_and_buyburn_executor",
    ):
        outcome = contract.assess_service_budget_v1(_policy(role_id=role_id))
        assert isinstance(outcome, contract.ServiceBudgetRejectV1)
        assert outcome.code is contract.ServiceBudgetRejectCodeV1.ROLE_NOT_BUDGET_ELIGIBLE


def test_funding_source_registry_is_role_specific() -> None:
    registry = contract.allowed_funding_sources_v1()

    assert (
        contract.FundingSourceV1.SIGNED_USER_INTERFACE_FEE
        in registry["interface_api_and_static_host"]
    )
    assert (
        contract.FundingSourceV1.SIGNED_USER_INTERFACE_FEE
        not in registry["validator_finality_operator"]
    )
    assert (
        contract.FundingSourceV1.USER_GRANTED_EXECUTION_IMPROVEMENT
        in registry["solver_batcher_and_sequencer"]
    )


def test_exact_target_runway_assessment() -> None:
    outcome = contract.assess_service_budget_v1(_policy())

    assert isinstance(outcome, contract.ServiceBudgetAssessmentV1)
    assert outcome.declared_maximum_period_liability_atoms == 50
    assert outcome.required_prefund_atoms == 300
    assert outcome.funded_full_periods == 6
    assert outcome.prefund_shortfall_atoms == 0
    assert outcome.target_met is True


def test_underfunded_target_reports_exact_shortfall_without_false_readiness() -> None:
    outcome = contract.assess_service_budget_v1(
        _policy(opening_reserve_atoms=299)
    )

    assert isinstance(outcome, contract.ServiceBudgetAssessmentV1)
    assert outcome.funded_full_periods == 5
    assert outcome.prefund_shortfall_atoms == 1
    assert outcome.target_met is False


def test_period_cap_must_cover_declared_fixed_and_variable_liability() -> None:
    outcome = contract.assess_service_budget_v1(_policy(period_cap_atoms=49))

    assert isinstance(outcome, contract.ServiceBudgetRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.PERIOD_CAP_TOO_SMALL


def test_budget_arithmetic_overflow_rejects() -> None:
    outcome = contract.assess_service_budget_v1(
        _policy(
            opening_reserve_atoms=contract.MAX_ATOMS,
            maximum_jobs_per_period=contract.MAX_ATOMS,
            maximum_atoms_per_job=2,
            period_cap_atoms=contract.MAX_ATOMS,
        )
    )

    assert isinstance(outcome, contract.ServiceBudgetRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.ARITHMETIC_OVERFLOW


def test_unsupported_funding_source_rejects() -> None:
    outcome = contract.assess_service_budget_v1(
        _policy(
            role_id="validator_finality_operator",
            funding_source=contract.FundingSourceV1.SIGNED_USER_INTERFACE_FEE,
        )
    )

    assert isinstance(outcome, contract.ServiceBudgetRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.FUNDING_SOURCE_NOT_ALLOWED


def test_open_budget_requires_one_fully_prefunded_period() -> None:
    outcome = contract.open_service_budget_v1(
        _policy(opening_reserve_atoms=49),
        initial_period_index=0,
    )

    assert isinstance(outcome, contract.ServiceBudgetOpenRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.CURRENT_PERIOD_NOT_PREFUNDED


def test_open_budget_requires_declared_target_runway() -> None:
    outcome = contract.open_service_budget_v1(
        _policy(opening_reserve_atoms=299),
        initial_period_index=0,
    )

    assert isinstance(outcome, contract.ServiceBudgetOpenRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.TARGET_PREFUND_NOT_MET


def test_fixed_and_variable_payments_preserve_caps_and_reserve() -> None:
    policy = _policy()
    state = _opened(policy)

    fixed = contract.run_service_budget_transition_v1(
        state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.FIXED_PERIOD,
            amount_atoms=10,
            job_label="fixed:0",
        ),
    )
    assert isinstance(fixed, contract.ServiceBudgetTransitionAcceptV1)
    assert fixed.state.remaining_reserve_atoms == 290
    assert fixed.state.fixed_payment_made is True

    variable = contract.run_service_budget_transition_v1(
        fixed.state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=20,
            job_label="proof:0",
        ),
    )
    assert isinstance(variable, contract.ServiceBudgetTransitionAcceptV1)
    assert variable.state.remaining_reserve_atoms == 270
    assert variable.state.period_spent_atoms == 30
    assert variable.state.variable_jobs_paid == 1


def test_fixed_payment_must_match_declared_liability() -> None:
    policy = _policy()
    state = _opened(policy)

    outcome = contract.run_service_budget_transition_v1(
        state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.FIXED_PERIOD,
            amount_atoms=9,
            job_label="fixed:underpay",
        ),
    )

    assert isinstance(outcome, contract.ServiceBudgetTransitionRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.FIXED_PAYMENT_MISMATCH
    assert outcome.state == state


def test_job_replay_rejects_without_spending_again() -> None:
    policy = _policy(fixed_atoms_per_period=0, period_cap_atoms=40)
    state = _opened(policy)
    command = _payment(
        kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
        amount_atoms=20,
        job_label="proof:replay",
    )
    first = contract.run_service_budget_transition_v1(state, policy, command)
    assert isinstance(first, contract.ServiceBudgetTransitionAcceptV1)

    replay = contract.run_service_budget_transition_v1(first.state, policy, command)

    assert isinstance(replay, contract.ServiceBudgetTransitionRejectV1)
    assert replay.code is contract.ServiceBudgetRejectCodeV1.JOB_ALREADY_PAID
    assert replay.state == first.state


def test_variable_job_and_period_caps_reject_no_op() -> None:
    policy = _policy(fixed_atoms_per_period=0, period_cap_atoms=40)
    state = _opened(policy)
    above_job_cap = contract.run_service_budget_transition_v1(
        state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=21,
            job_label="proof:large",
        ),
    )
    assert isinstance(above_job_cap, contract.ServiceBudgetTransitionRejectV1)
    assert above_job_cap.code is contract.ServiceBudgetRejectCodeV1.JOB_CAP_EXCEEDED
    assert above_job_cap.state == state

    first = contract.run_service_budget_transition_v1(
        state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=20,
            job_label="proof:first",
        ),
    )
    assert isinstance(first, contract.ServiceBudgetTransitionAcceptV1)
    second = contract.run_service_budget_transition_v1(
        first.state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=20,
            job_label="proof:second",
        ),
    )
    assert isinstance(second, contract.ServiceBudgetTransitionAcceptV1)
    third = contract.run_service_budget_transition_v1(
        second.state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=1,
            job_label="proof:third",
        ),
    )
    assert isinstance(third, contract.ServiceBudgetTransitionRejectV1)
    assert third.code is contract.ServiceBudgetRejectCodeV1.JOB_COUNT_EXCEEDED
    assert third.state == second.state


def test_reserve_exhaustion_rejects_no_op() -> None:
    policy = _policy(
        opening_reserve_atoms=50,
        fixed_atoms_per_period=0,
        maximum_jobs_per_period=2,
        maximum_atoms_per_job=20,
        period_cap_atoms=40,
        target_prefund_periods=1,
    )
    state = _opened(policy)
    malformed_state = replace(state, remaining_reserve_atoms=5)

    outcome = contract.run_service_budget_transition_v1(
        malformed_state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=6,
            job_label="proof:exhausted",
        ),
    )

    assert isinstance(outcome, contract.ServiceBudgetTransitionRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.RESERVE_EXHAUSTED
    assert outcome.state == malformed_state


def test_period_cannot_advance_with_unpaid_fixed_obligation() -> None:
    policy = _policy()
    state = _opened(policy)

    outcome = contract.run_service_budget_transition_v1(
        state,
        policy,
        contract.AdvanceServiceBudgetPeriodV1(
            next_period_index=1,
            authorization_root=_root("advance:unpaid"),
        ),
    )

    assert isinstance(outcome, contract.ServiceBudgetTransitionRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.UNPAID_FIXED_OBLIGATION
    assert outcome.state == state


def test_period_advance_resets_counters_and_retains_replay_nullifiers() -> None:
    policy = _policy()
    state = _opened(policy)
    fixed_command = _payment(
        kind=contract.ServicePaymentKindV1.FIXED_PERIOD,
        amount_atoms=10,
        job_label="fixed:advance",
    )
    paid = contract.run_service_budget_transition_v1(state, policy, fixed_command)
    assert isinstance(paid, contract.ServiceBudgetTransitionAcceptV1)

    advanced = contract.run_service_budget_transition_v1(
        paid.state,
        policy,
        contract.AdvanceServiceBudgetPeriodV1(
            next_period_index=1,
            authorization_root=_root("advance:paid"),
        ),
    )

    assert isinstance(advanced, contract.ServiceBudgetTransitionAcceptV1)
    assert advanced.state.period_index == 1
    assert advanced.state.period_spent_atoms == 0
    assert advanced.state.variable_jobs_paid == 0
    assert advanced.state.fixed_payment_made is False
    assert fixed_command.job_id in advanced.state.paid_job_ids


def test_period_index_overflow_rejects_no_op() -> None:
    policy = _policy(fixed_atoms_per_period=0, period_cap_atoms=40)
    state = replace(_opened(policy), period_index=contract.MAX_ATOMS)

    outcome = contract.run_service_budget_transition_v1(
        state,
        policy,
        contract.AdvanceServiceBudgetPeriodV1(
            next_period_index=contract.MAX_ATOMS + 1,
            authorization_root=_root("advance:overflow"),
        ),
    )

    assert isinstance(outcome, contract.ServiceBudgetTransitionRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.INVALID_PERIOD
    assert outcome.state == state


def test_unknown_payment_kind_rejects_instead_of_becoming_variable() -> None:
    policy = _policy(fixed_atoms_per_period=0, period_cap_atoms=40)
    state = _opened(policy)
    malformed = replace(
        _payment(
            kind=contract.ServicePaymentKindV1.VARIABLE_JOB,
            amount_atoms=1,
            job_label="proof:unknown-kind",
        ),
        payment_kind=cast(contract.ServicePaymentKindV1, "UNKNOWN"),
    )

    outcome = contract.run_service_budget_transition_v1(state, policy, malformed)

    assert isinstance(outcome, contract.ServiceBudgetTransitionRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.INVALID_PAYMENT_KIND
    assert outcome.state == state


def test_next_period_must_be_fully_prefunded() -> None:
    policy = _policy(
        opening_reserve_atoms=50,
        fixed_atoms_per_period=10,
        maximum_jobs_per_period=2,
        maximum_atoms_per_job=20,
        period_cap_atoms=50,
        target_prefund_periods=1,
    )
    state = _opened(policy)
    paid = contract.run_service_budget_transition_v1(
        state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.FIXED_PERIOD,
            amount_atoms=10,
            job_label="fixed:last-period",
        ),
    )
    assert isinstance(paid, contract.ServiceBudgetTransitionAcceptV1)

    outcome = contract.run_service_budget_transition_v1(
        paid.state,
        policy,
        contract.AdvanceServiceBudgetPeriodV1(
            next_period_index=1,
            authorization_root=_root("advance:unfunded"),
        ),
    )

    assert isinstance(outcome, contract.ServiceBudgetTransitionRejectV1)
    assert outcome.code is contract.ServiceBudgetRejectCodeV1.NEXT_PERIOD_NOT_PREFUNDED
    assert outcome.state == paid.state


def test_replay_protected_topup_enables_next_period() -> None:
    policy = _policy(
        opening_reserve_atoms=50,
        fixed_atoms_per_period=10,
        maximum_jobs_per_period=2,
        maximum_atoms_per_job=20,
        period_cap_atoms=50,
        target_prefund_periods=1,
    )
    state = _opened(policy)
    paid = contract.run_service_budget_transition_v1(
        state,
        policy,
        _payment(
            kind=contract.ServicePaymentKindV1.FIXED_PERIOD,
            amount_atoms=10,
            job_label="fixed:topup",
        ),
    )
    assert isinstance(paid, contract.ServiceBudgetTransitionAcceptV1)
    topup = contract.TopUpServiceBudgetV1(
        role_id=policy.role_id,
        payment_asset_id=policy.payment_asset_id,
        topup_id=_root("topup:revenue:1"),
        amount_atoms=10,
        admitted_source_witness_root=_root("topup:witness:1"),
    )
    funded = contract.run_service_budget_transition_v1(paid.state, policy, topup)
    assert isinstance(funded, contract.ServiceBudgetTransitionAcceptV1)
    assert funded.state.remaining_reserve_atoms == 50
    assert funded.reserve_increase_atoms == 10

    replay = contract.run_service_budget_transition_v1(funded.state, policy, topup)
    assert isinstance(replay, contract.ServiceBudgetTransitionRejectV1)
    assert replay.code is contract.ServiceBudgetRejectCodeV1.TOPUP_ALREADY_CONSUMED
    assert replay.state == funded.state

    advanced = contract.run_service_budget_transition_v1(
        funded.state,
        policy,
        contract.AdvanceServiceBudgetPeriodV1(
            next_period_index=1,
            authorization_root=_root("advance:after-topup"),
        ),
    )
    assert isinstance(advanced, contract.ServiceBudgetTransitionAcceptV1)
    assert topup.topup_id in advanced.state.consumed_topup_ids


def test_bounded_oracle_closes_direct_overspend_queries() -> None:
    evidence = checker.bounded_funding_evidence()

    assert evidence["accepted_payment_bound_search"]["counterexample"] is None
    assert evidence["runway_shortfall_search"]["counterexample"] is None
    assert all(
        witness["loss_atoms"] > 0
        for witness in evidence["named_mutant_witnesses"]
    )


def test_artifact_tampering_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["activation_gate"]["activation_allowed"] = True
    candidate = tmp_path / "activated.json"
    candidate.write_bytes(checker._encoded(artifact))

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert report["activation_allowed"] is False


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    candidate = tmp_path / "duplicate.json"
    candidate.write_text(
        '{"schema":"first","schema":"second"}\n',
        encoding="utf-8",
    )

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_selected_budget_mutation_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    role_id = "proof_prover_and_proof_miner"
    monkeypatch.setattr(
        contract,
        "SELECTED_ROLE_BUDGETS",
        {**contract.SELECTED_ROLE_BUDGETS, role_id: {"payment_asset_id": "USDC"}},
    )

    with pytest.raises(ValueError, match="role budgets must remain unselected"):
        checker.build_document()


def test_frozen_research_source_byte_drift_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    real_git_bytes = checker._git_bytes

    def altered_git_bytes(repo_root: Path, *args: str) -> bytes:
        observed = real_git_bytes(repo_root, *args)
        if args and args[0] == "show":
            return observed + b"tampered"
        return observed

    monkeypatch.setattr(checker, "_git_bytes", altered_git_bytes)

    with pytest.raises(ValueError, match="research source drift"):
        checker.build_document()
