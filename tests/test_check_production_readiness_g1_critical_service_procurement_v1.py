from __future__ import annotations

import json
from dataclasses import replace
from itertools import permutations
from pathlib import Path

import pytest

from tools import check_production_readiness_g1_critical_service_procurement_v1 as checker
from tools import production_readiness_g1_critical_service_cost_contract_v1 as costs
from tools import production_readiness_g1_critical_service_procurement_contract_v1 as contract

ROLE = "validator_finality_operator"
ASSET = "USD_E6"
SERVICE_ROOT = "1" * 64
BENCHMARK_ROOT = "2" * 64
EXECUTION_ROOT = "3" * 64
HARDWARE_ROOT = "4" * 64
IDENTITY_ROOT = "5" * 64
OWNER_ROOT = "6" * 64
SIGNED_QUOTE_ROOT = "7" * 64
EVIDENCE_ROOT = "8" * 64


def _quote(
    quote_id: str = "quote-a",
    *,
    provider_id: str | None = None,
    owner_id: str | None = None,
    cloud: str | None = None,
    jurisdiction: str | None = None,
    period_cap_atoms: int | None = None,
) -> contract.CompleteServiceQuoteV1:
    if period_cap_atoms is None:
        components = contract.QuotedCostComponentsV1(
            fixed_infrastructure_atoms=100,
            fixed_operator_on_call_atoms=200,
            fixed_security_monitoring_atoms=30,
            fixed_data_license_external_io_atoms=40,
            fixed_risk_capital_insurance_atoms=50,
            variable_compute_execution_per_job_atoms=10,
            variable_labor_external_per_job_atoms=5,
            one_time_onboarding_atoms=25,
        )
        maximum_jobs = 2
        contingency_bps = 1_000
    else:
        components = contract.QuotedCostComponentsV1(
            fixed_infrastructure_atoms=period_cap_atoms,
            fixed_operator_on_call_atoms=0,
            fixed_security_monitoring_atoms=0,
            fixed_data_license_external_io_atoms=0,
            fixed_risk_capital_insurance_atoms=0,
            variable_compute_execution_per_job_atoms=0,
            variable_labor_external_per_job_atoms=0,
            one_time_onboarding_atoms=0,
        )
        maximum_jobs = 0
        contingency_bps = 0
    return contract.CompleteServiceQuoteV1(
        quote_id=quote_id,
        role_id=ROLE,
        provider_id=provider_id or f"provider-{quote_id}",
        beneficial_owner_id=owner_id or f"owner-{quote_id}",
        payment_asset_id=ASSET,
        valid_from_epoch=10,
        valid_through_epoch=20,
        service_spec_root=SERVICE_ROOT,
        benchmark_profile_root=BENCHMARK_ROOT,
        execution_subject_root=EXECUTION_ROOT,
        hardware_profile_root=HARDWARE_ROOT,
        identity_evidence_root=IDENTITY_ROOT,
        beneficial_owner_evidence_root=OWNER_ROOT,
        signed_quote_evidence_root=SIGNED_QUOTE_ROOT,
        failure_domains=(
            contract.FailureDomainV1(
                kind="cloud_provider",
                value=cloud or f"cloud-{quote_id}",
            ),
            contract.FailureDomainV1(
                kind="jurisdiction",
                value=jurisdiction or f"jurisdiction-{quote_id}",
            ),
        ),
        cost_components=components,
        maximum_jobs_per_period=maximum_jobs,
        contingency_bps=contingency_bps,
        target_prefund_periods=18,
    )


def _qualification_policy() -> contract.QualificationPolicyV1:
    return contract.QualificationPolicyV1(
        role_id=ROLE,
        evaluation_epoch=15,
        service_spec_root=SERVICE_ROOT,
        benchmark_profile_root=BENCHMARK_ROOT,
        execution_subject_root=EXECUTION_ROOT,
        hardware_profile_root=HARDWARE_ROOT,
        minimum_successful_trials=10,
        maximum_failed_trials=1,
        maximum_p95_latency_ms=100,
        minimum_availability_bps=9_900,
        maximum_peak_memory_bytes=1_000,
    )


def _observation(quote_id: str = "quote-a") -> contract.QualificationObservationV1:
    return contract.QualificationObservationV1(
        quote_id=quote_id,
        role_id=ROLE,
        service_spec_root=SERVICE_ROOT,
        benchmark_profile_root=BENCHMARK_ROOT,
        execution_subject_root=EXECUTION_ROOT,
        hardware_profile_root=HARDWARE_ROOT,
        evidence_root=EVIDENCE_ROOT,
        successful_trials=10,
        failed_trials=0,
        invalid_work_accepts=0,
        replay_or_duplicate_accepts=0,
        safety_violation_events=0,
        recovery_failures=0,
        p95_latency_ms=90,
        availability_bps=9_999,
        peak_memory_bytes=900,
    )


def _bond(quote_id: str = "quote-a") -> contract.BondTermsV1:
    return contract.BondTermsV1(
        quote_id=quote_id,
        payment_asset_id=ASSET,
        bond_atoms=100,
        slash_atoms=100,
        maximum_defect_gain_atoms=100,
        future_value_lost_atoms=50,
        detection_probability_bps=5_000,
    )


def _qualified(quote: contract.CompleteServiceQuoteV1) -> contract.QualifiedServiceBidV1:
    outcome = contract.qualify_service_candidate_v1(
        quote,
        _observation(quote.quote_id),
        _bond(quote.quote_id),
        _qualification_policy(),
    )
    assert isinstance(outcome, contract.QualifiedServiceBidV1)
    return outcome


def _procurement_policy(
    *,
    required_winners: int = 2,
    period_budget_cap_atoms: int = 2_000,
    onboarding_budget_cap_atoms: int = 100,
    owner_cap: int = 1,
    domain_cap: int = 1,
) -> contract.ProcurementPolicyV1:
    return contract.ProcurementPolicyV1(
        role_id=ROLE,
        payment_asset_id=ASSET,
        selection_epoch=15,
        service_spec_root=SERVICE_ROOT,
        benchmark_profile_root=BENCHMARK_ROOT,
        execution_subject_root=EXECUTION_ROOT,
        hardware_profile_root=HARDWARE_ROOT,
        required_winners=required_winners,
        period_budget_cap_atoms=period_budget_cap_atoms,
        onboarding_budget_cap_atoms=onboarding_budget_cap_atoms,
        maximum_per_beneficial_owner=owner_cap,
        failure_domain_caps=(
            contract.FailureDomainCapV1(
                kind="cloud_provider",
                maximum_selected_per_value=domain_cap,
            ),
            contract.FailureDomainCapV1(
                kind="jurisdiction",
                maximum_selected_per_value=domain_cap,
            ),
        ),
        maximum_candidate_count=16,
    )


def test_complete_quote_uses_all_named_components_and_high_case_cap() -> None:
    outcome = contract.assess_complete_quote_v1(_quote(), evaluation_epoch=15)

    assert isinstance(outcome, contract.CompleteQuoteAssessmentV1)
    assert outcome.fixed_period_atoms == 420
    assert outcome.variable_period_atoms == 30
    assert outcome.raw_period_atoms == 450
    assert outcome.quoted_period_cap_atoms == 495
    assert outcome.one_time_onboarding_atoms == 25
    assert outcome.component_set_complete is True
    assert len(outcome.quote_commitment_root) == 64


@pytest.mark.parametrize(
    ("mutated", "epoch", "code"),
    (
        (
            replace(_quote(), valid_from_epoch=True),
            15,
            contract.ProcurementRejectCodeV1.INTEGER_REQUIRED,
        ),
        (
            replace(_quote(), service_spec_root="bad"),
            15,
            contract.ProcurementRejectCodeV1.ROOT_INVALID,
        ),
        (
            replace(_quote(), valid_through_epoch=14),
            15,
            contract.ProcurementRejectCodeV1.QUOTE_NOT_CURRENT,
        ),
        (
            replace(_quote(), payment_asset_id=" USD_E6"),
            15,
            contract.ProcurementRejectCodeV1.IDENTIFIER_INVALID,
        ),
        (
            replace(
                _quote(),
                failure_domains=(
                    contract.FailureDomainV1("cloud_provider", "one"),
                    contract.FailureDomainV1("cloud_provider", "two"),
                ),
            ),
            15,
            contract.ProcurementRejectCodeV1.DUPLICATE_FAILURE_DOMAIN_KIND,
        ),
    ),
)
def test_invalid_or_stale_complete_quote_rejects(
    mutated: contract.CompleteServiceQuoteV1,
    epoch: int,
    code: contract.ProcurementRejectCodeV1,
) -> None:
    outcome = contract.assess_complete_quote_v1(mutated, evaluation_epoch=epoch)

    assert isinstance(outcome, contract.ProcurementRejectV1)
    assert outcome.code is code


def test_complete_quote_overflow_rejects() -> None:
    quote = _quote(period_cap_atoms=contract.MAX_ATOMS)
    quote = replace(quote, contingency_bps=1)

    outcome = contract.assess_complete_quote_v1(quote, evaluation_epoch=15)

    assert isinstance(outcome, contract.ProcurementRejectV1)
    assert outcome.code is contract.ProcurementRejectCodeV1.ARITHMETIC_OVERFLOW


def test_wrong_runtime_types_reject_without_partial_selection() -> None:
    quote_outcome = contract.assess_complete_quote_v1(
        {},  # type: ignore[arg-type]
        evaluation_epoch=15,
    )
    selection_outcome = contract.select_service_bids_v1(
        ({"quote_id": "forged"},),  # type: ignore[arg-type]
        _procurement_policy(required_winners=1),
    )

    assert isinstance(quote_outcome, contract.ProcurementRejectV1)
    assert quote_outcome.code is contract.ProcurementRejectCodeV1.QUOTE_BINDING_MISMATCH
    assert isinstance(selection_outcome, contract.ProcurementRejectV1)
    assert selection_outcome.code is contract.ProcurementRejectCodeV1.POLICY_MISMATCH


def test_quote_refines_exactly_to_existing_cost_contract() -> None:
    quote = _quote()
    quote_assessment = contract.assess_complete_quote_v1(quote, evaluation_epoch=15)
    refined = contract.refine_quote_to_cost_envelope_v1(quote, evaluation_epoch=15)

    assert isinstance(quote_assessment, contract.CompleteQuoteAssessmentV1)
    assert isinstance(refined, costs.ServiceCostAssessmentV1)
    assert refined.recommended_period_cap_atoms == quote_assessment.quoted_period_cap_atoms
    assert refined.target_prefund_atoms == 18 * quote_assessment.quoted_period_cap_atoms
    assert refined.component_set_complete is True


def test_skin_in_game_boundary_is_exact_and_slash_is_bonded() -> None:
    exact = contract.assess_bond_adequacy_v1(
        _bond(), expected_quote_id="quote-a", expected_asset_id=ASSET
    )
    below = contract.assess_bond_adequacy_v1(
        replace(_bond(), future_value_lost_atoms=49),
        expected_quote_id="quote-a",
        expected_asset_id=ASSET,
    )
    unbonded = contract.assess_bond_adequacy_v1(
        replace(_bond(), bond_atoms=99),
        expected_quote_id="quote-a",
        expected_asset_id=ASSET,
    )

    assert isinstance(exact, contract.BondAdequacyAssessmentV1)
    assert exact.incentive_compatible is True
    assert exact.incentive_margin_scaled_atoms == 0
    assert isinstance(below, contract.ProcurementRejectV1)
    assert below.code is contract.ProcurementRejectCodeV1.BOND_INADEQUATE
    assert isinstance(unbonded, contract.ProcurementRejectV1)
    assert unbonded.code is contract.ProcurementRejectCodeV1.SLASH_EXCEEDS_BOND


@pytest.mark.parametrize(
    ("observation", "code"),
    (
        (
            replace(_observation(), invalid_work_accepts=1),
            contract.ProcurementRejectCodeV1.INVALID_WORK_ACCEPTED,
        ),
        (
            replace(_observation(), replay_or_duplicate_accepts=1),
            contract.ProcurementRejectCodeV1.REPLAY_ACCEPTED,
        ),
        (
            replace(_observation(), safety_violation_events=1),
            contract.ProcurementRejectCodeV1.SAFETY_VIOLATION,
        ),
        (
            replace(_observation(), recovery_failures=1),
            contract.ProcurementRejectCodeV1.RECOVERY_FAILURE,
        ),
        (
            replace(_observation(), p95_latency_ms=101),
            contract.ProcurementRejectCodeV1.QUALIFICATION_THRESHOLD_MISSED,
        ),
        (
            replace(_observation(), benchmark_profile_root="9" * 64),
            contract.ProcurementRejectCodeV1.PROFILE_BINDING_MISMATCH,
        ),
    ),
)
def test_qualification_fails_closed_on_safety_or_profile_drift(
    observation: contract.QualificationObservationV1,
    code: contract.ProcurementRejectCodeV1,
) -> None:
    outcome = contract.qualify_service_candidate_v1(
        _quote(), observation, _bond(), _qualification_policy()
    )

    assert isinstance(outcome, contract.ProcurementRejectV1)
    assert outcome.code is code


def test_qualified_bid_binds_quote_profile_bond_and_evidence() -> None:
    outcome = _qualified(_quote())

    assert outcome.quoted_period_cap_atoms == 495
    assert outcome.bond_atoms == 100
    assert outcome.qualification_evidence_root == EVIDENCE_ROOT
    assert outcome.service_spec_root == SERVICE_ROOT
    assert outcome.benchmark_profile_root == BENCHMARK_ROOT


def test_exact_selector_finds_feasible_set_that_greedy_cheapest_first_misses() -> None:
    # A blocks both remaining candidates: B shares its cloud and C shares its owner.
    # The globally feasible minimum is B+C.
    a = _qualified(_quote("a", period_cap_atoms=100, owner_id="owner-x", cloud="cloud-1"))
    b = _qualified(_quote("b", period_cap_atoms=101, owner_id="owner-y", cloud="cloud-1"))
    c = _qualified(_quote("c", period_cap_atoms=102, owner_id="owner-x", cloud="cloud-2"))

    outcome = contract.select_service_bids_v1((a, b, c), _procurement_policy())

    assert isinstance(outcome, contract.ProcurementSelectionV1)
    assert outcome.selected_quote_ids == ("b", "c")
    assert outcome.total_period_cap_atoms == 203
    assert outcome.exact_combinations_evaluated == 3


def test_selector_tie_break_is_canonical_under_input_permutation() -> None:
    bids = tuple(_qualified(_quote(qid, period_cap_atoms=100)) for qid in ("c", "a", "b"))
    observed = {
        contract.select_service_bids_v1(order, _procurement_policy()).selected_quote_ids  # type: ignore[union-attr]
        for order in permutations(bids)
    }

    assert observed == {("a", "b")}


@pytest.mark.parametrize(
    ("bids", "policy", "code"),
    (
        (
            lambda: (_qualified(_quote("a")), _qualified(_quote("a"))),
            lambda: _procurement_policy(),
            contract.ProcurementRejectCodeV1.DUPLICATE_QUOTE,
        ),
        (
            lambda: (_qualified(_quote("a", period_cap_atoms=100)),),
            lambda: _procurement_policy(required_winners=2),
            contract.ProcurementRejectCodeV1.INSUFFICIENT_QUALIFIED_BIDS,
        ),
        (
            lambda: (
                _qualified(_quote("a", period_cap_atoms=100)),
                _qualified(_quote("b", period_cap_atoms=101)),
            ),
            lambda: _procurement_policy(period_budget_cap_atoms=200),
            contract.ProcurementRejectCodeV1.NO_FEASIBLE_SELECTION,
        ),
    ),
)
def test_selector_rejects_replay_insufficiency_and_underfunding(
    bids: object,
    policy: object,
    code: contract.ProcurementRejectCodeV1,
) -> None:
    outcome = contract.select_service_bids_v1(bids(), policy())  # type: ignore[operator]

    assert isinstance(outcome, contract.ProcurementRejectV1)
    assert outcome.code is code


@pytest.mark.parametrize(
    "mutate",
    (
        lambda bid: replace(bid, payment_asset_id="USDC"),
        lambda bid: replace(bid, target_prefund_atoms=bid.target_prefund_atoms + 1),
        lambda bid: replace(
            bid,
            failure_domains=(
                contract.FailureDomainV1("cloud_provider", "cloud-a"),
                contract.FailureDomainV1("cloud_provider", "cloud-b"),
            ),
        ),
    ),
)
def test_selector_rejects_forged_qualified_bid_fields(mutate: object) -> None:
    bid = _qualified(_quote("a"))
    forged = mutate(bid)  # type: ignore[operator]

    outcome = contract.select_service_bids_v1(
        (forged,),
        _procurement_policy(required_winners=1),
    )

    assert isinstance(outcome, contract.ProcurementRejectV1)
    assert outcome.code is contract.ProcurementRejectCodeV1.POLICY_MISMATCH


def test_artifact_is_exact_and_every_selection_remains_null() -> None:
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["selected_procurement_policy_count"] == 0
    assert report["qualified_production_quote_count"] == 0
    assert report["activation_allowed"] is False
    assert report["payment_allowed"] is False
    assert report["production_ready"] is False
    assert document["status"] == "RESEARCH_ONLY_UNSELECTED"


def test_bounded_evidence_closes_only_declared_finite_queries() -> None:
    evidence = checker.bounded_procurement_evidence()

    assert evidence["bond_boundary_search"]["counterexample"] is None
    assert evidence["selector_permutation_search"]["counterexample"] is None
    assert {row["id"] for row in evidence["named_mutant_witnesses"]} == {
        "GREEDY_CHEAPEST_FIRST",
        "LOW_CASE_PRICE_SELECTION",
        "COMMON_OWNER_SYBIL",
        "COMMON_FAILURE_DOMAIN",
        "BENCHMARK_PROFILE_SUBSTITUTION",
        "QUOTE_REPLAY_AFTER_EXPIRY",
        "UNBONDED_SLASH",
        "PROOF_MARKET_CREATES_REWARD",
    }


def test_artifact_tampering_and_duplicate_json_fail_closed(tmp_path: Path) -> None:
    artifact = json.loads(checker.DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["activation_gate"]["activation_allowed"] = True
    tampered = tmp_path / "tampered.json"
    tampered.write_bytes(checker._encoded(artifact))
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    assert checker.check_artifact(tampered)["ok"] is False
    duplicate_report = checker.check_artifact(duplicate)
    assert duplicate_report["ok"] is False
    assert any("duplicate JSON keys" in error for error in duplicate_report["errors"])


def test_selected_policy_mutation_fails_generation(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        contract,
        "SELECTED_PROCUREMENT_POLICIES",
        {**contract.SELECTED_PROCUREMENT_POLICIES, ROLE: {"required_winners": 7}},
    )

    with pytest.raises(ValueError, match="procurement policies must remain unselected"):
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

    with pytest.raises(ValueError, match="critical-service procurement source drift"):
        checker.build_document()
