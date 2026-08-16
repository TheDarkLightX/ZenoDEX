from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from tools import check_production_readiness_g1_critical_service_costs_v1 as checker
from tools import production_readiness_g1_critical_service_cost_contract_v1 as contract
from tools import production_readiness_g1_service_funding_contract_v1 as funding


def _range(low: int, high: int) -> contract.AmountRangeV1:
    return contract.AmountRangeV1(low_atoms=low, high_atoms=high)


def _envelope(
    *,
    role_id: str = "validator_finality_operator",
    payment_asset_id: str = "USD_E6",
    scope: contract.CostEstimateScopeV1 = (
        contract.CostEstimateScopeV1.FULL_ROLE_COST_CANDIDATE
    ),
    role_count: int = 7,
    infrastructure: contract.AmountRangeV1 | None = None,
    operator: contract.AmountRangeV1 | None = None,
    maximum_jobs_per_period: int = 2,
    variable: contract.AmountRangeV1 | None = None,
    contingency_bps: int = 1_000,
    target_prefund_periods: int = 18,
) -> contract.ServiceCostEnvelopeV1:
    return contract.ServiceCostEnvelopeV1(
        role_id=role_id,
        payment_asset_id=payment_asset_id,
        estimate_scope=scope,
        cost_period=contract.CostPeriodV1.CALENDAR_MONTH_RESEARCH_ONLY,
        role_count=role_count,
        fixed_infrastructure_per_role=(
            infrastructure if infrastructure is not None else _range(50, 100)
        ),
        fixed_operator_per_role=(
            operator if operator is not None else _range(100, 200)
        ),
        maximum_jobs_per_period=maximum_jobs_per_period,
        variable_cost_per_job=(
            variable if variable is not None else _range(10, 20)
        ),
        contingency_bps=contingency_bps,
        target_prefund_periods=target_prefund_periods,
    )


def _assessed(**kwargs: Any) -> contract.ServiceCostAssessmentV1:
    outcome = contract.assess_service_cost_envelope_v1(_envelope(**kwargs))
    assert isinstance(outcome, contract.ServiceCostAssessmentV1)
    return outcome


def test_artifact_is_exact_and_keeps_all_costs_unselected() -> None:
    document = checker.build_document()
    report = checker.check_artifact(checker.DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["selected_cost_envelope_count"] == 0
    assert report["activation_allowed"] is False
    assert report["production_ready"] is False
    assert document["status"] == "RESEARCH_ONLY_UNSELECTED"
    assert document["production_promotion"] is False


def test_exact_five_critical_roles_remain_unselected() -> None:
    assert set(contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES) == {
        "validator_finality_operator",
        "oracle_reporter_aggregator_disputer_and_watcher",
        "liquidator_and_keeper",
        "tau_relayer_and_destination_operator",
        "proof_prover_and_proof_miner",
    }
    assert all(
        value is None
        for value in contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES.values()
    )
    assert all(
        value is None
        for value in contract.SELECTED_CRITICAL_SERVICE_REVENUE_INPUTS.values()
    )


def test_external_quotes_are_component_only_and_exactly_scaled() -> None:
    quotes = contract.external_benchmark_quotes_v1()

    assert set(quotes) == {
        "HETZNER_CCX13_US_MONTH_2026_06_15",
        "HETZNER_CCX33_US_MONTH_2026_06_15",
        "DIGITALOCEAN_GENERAL_PURPOSE_START_MONTH_2026_08_16",
        "DIGITALOCEAN_A4000_HOUR_2026_08_16",
        "DIGITALOCEAN_A100_HOUR_2026_08_16",
    }
    assert quotes["HETZNER_CCX13_US_MONTH_2026_06_15"].amount_atoms == 50_990_000
    assert quotes["HETZNER_CCX33_US_MONTH_2026_06_15"].amount_atoms == 165_990_000
    assert quotes["DIGITALOCEAN_GENERAL_PURPOSE_START_MONTH_2026_08_16"].amount_atoms == 63_000_000
    assert quotes["DIGITALOCEAN_A4000_HOUR_2026_08_16"].amount_atoms == 760_000
    assert quotes["DIGITALOCEAN_A100_HOUR_2026_08_16"].amount_atoms == 3_090_000
    assert all(
        quote.evidence_scope is contract.BenchmarkEvidenceScopeV1.COMPONENT_ONLY
        for quote in quotes.values()
    )


def test_cost_envelope_uses_ceil_contingency_and_high_case_cap() -> None:
    outcome = _assessed(
        role_count=1,
        infrastructure=_range(1, 1),
        operator=_range(0, 0),
        maximum_jobs_per_period=0,
        variable=_range(0, 0),
        contingency_bps=1,
        target_prefund_periods=3,
    )

    assert outcome.raw_period_cost_low_atoms == 1
    assert outcome.raw_period_cost_high_atoms == 1
    assert outcome.loaded_period_cost_low_atoms == 2
    assert outcome.loaded_period_cost_high_atoms == 2
    assert outcome.recommended_period_cap_atoms == 2
    assert outcome.target_prefund_atoms == 6


@pytest.mark.parametrize(
    ("mutated", "code"),
    (
        (
            _envelope(infrastructure=_range(2, 1)),
            contract.CostRejectCodeV1.RANGE_INVERTED,
        ),
        (
            _envelope(role_count=True),
            contract.CostRejectCodeV1.INTEGER_REQUIRED,
        ),
        (
            _envelope(contingency_bps=10_001),
            contract.CostRejectCodeV1.CONTINGENCY_OUT_OF_RANGE,
        ),
        (
            _envelope(target_prefund_periods=0),
            contract.CostRejectCodeV1.TARGET_PERIODS_INVALID,
        ),
        (
            replace(_envelope(), estimate_scope="UNKNOWN"),  # type: ignore[arg-type]
            contract.CostRejectCodeV1.ESTIMATE_SCOPE_INVALID,
        ),
        (
            replace(_envelope(), cost_period="WEEK"),  # type: ignore[arg-type]
            contract.CostRejectCodeV1.COST_PERIOD_INVALID,
        ),
    ),
)
def test_invalid_cost_envelopes_reject(
    mutated: contract.ServiceCostEnvelopeV1,
    code: contract.CostRejectCodeV1,
) -> None:
    outcome = contract.assess_service_cost_envelope_v1(mutated)

    assert isinstance(outcome, contract.ServiceCostRejectV1)
    assert outcome.code is code


def test_cost_arithmetic_overflow_rejects() -> None:
    outcome = contract.assess_service_cost_envelope_v1(
        _envelope(
            role_count=contract.MAX_ATOMS,
            infrastructure=_range(2, 2),
            operator=_range(0, 0),
            maximum_jobs_per_period=0,
            variable=_range(0, 0),
            contingency_bps=0,
            target_prefund_periods=1,
        )
    )

    assert isinstance(outcome, contract.ServiceCostRejectV1)
    assert outcome.code is contract.CostRejectCodeV1.ARITHMETIC_OVERFLOW


def test_validator_infrastructure_scenario_is_component_only() -> None:
    scenario = contract.validator_infrastructure_scenario_v1()

    assert scenario.role_count == 7
    assert scenario.monthly_low_atoms == 356_930_000
    assert scenario.monthly_high_atoms == 1_161_930_000
    assert scenario.runway_18_month_low_atoms == 6_424_740_000
    assert scenario.runway_18_month_high_atoms == 20_914_740_000
    assert scenario.runway_36_month_low_atoms == 12_849_480_000
    assert scenario.runway_36_month_high_atoms == 41_829_480_000
    assert scenario.selection_eligible is False


def test_future_revenue_never_counts_as_prefunded_runway() -> None:
    cost = _assessed(
        role_count=1,
        infrastructure=_range(100, 100),
        operator=_range(0, 0),
        maximum_jobs_per_period=0,
        variable=_range(0, 0),
        contingency_bps=0,
        target_prefund_periods=3,
    )
    outcome = contract.assess_service_affordability_v1(
        cost,
        contract.ServiceRevenueForecastV1(
            payment_asset_id="USD_E6",
            realized_purpose_bound_prefund_atoms=0,
            recurring_revenue_per_period=_range(300, 300),
        ),
    )

    assert isinstance(outcome, contract.ServiceAffordabilityAssessmentV1)
    assert outcome.target_prefund_atoms == 300
    assert outcome.prefund_shortfall_atoms == 300
    assert outcome.prefund_target_met is False
    assert outcome.recurring_break_even_at_low is True
    assert outcome.forecast_counts_as_prefund is False


def test_cross_asset_affordability_rejects() -> None:
    outcome = contract.assess_service_affordability_v1(
        _assessed(),
        contract.ServiceRevenueForecastV1(
            payment_asset_id="USDC",
            realized_purpose_bound_prefund_atoms=1_000_000,
            recurring_revenue_per_period=_range(1, 1),
        ),
    )

    assert isinstance(outcome, contract.ServiceCostRejectV1)
    assert outcome.code is contract.CostRejectCodeV1.ASSET_MISMATCH


def test_same_asset_portfolio_sums_and_cross_asset_rejects() -> None:
    validator = _assessed(role_id="validator_finality_operator")
    oracle = _assessed(
        role_id="oracle_reporter_aggregator_disputer_and_watcher",
        role_count=3,
    )
    portfolio = contract.aggregate_service_cost_assessments_v1((validator, oracle))

    assert isinstance(portfolio, contract.ServiceCostPortfolioV1)
    assert portfolio.role_ids == tuple(sorted((validator.role_id, oracle.role_id)))
    assert portfolio.period_cap_atoms == (
        validator.recommended_period_cap_atoms
        + oracle.recommended_period_cap_atoms
    )
    assert portfolio.target_prefund_atoms == (
        validator.target_prefund_atoms + oracle.target_prefund_atoms
    )

    different_asset = _assessed(
        role_id="tau_relayer_and_destination_operator",
        payment_asset_id="USDC",
    )
    rejected = contract.aggregate_service_cost_assessments_v1(
        (validator, different_asset)
    )
    assert isinstance(rejected, contract.ServiceCostRejectV1)
    assert rejected.code is contract.CostRejectCodeV1.ASSET_MISMATCH


def test_cost_sizing_refines_existing_service_budget_arithmetic() -> None:
    cost = _assessed()
    sizing = contract.to_service_budget_sizing_v1(cost)
    policy = funding.ServiceBudgetPolicyV1(
        role_id=cost.role_id,
        payment_asset_id=cost.payment_asset_id,
        funding_source=funding.FundingSourceV1.DEPLOYMENT_CAPITAL_PREFUND,
        opening_reserve_atoms=sizing.target_prefund_atoms,
        fixed_atoms_per_period=sizing.fixed_atoms_per_period,
        maximum_jobs_per_period=sizing.maximum_jobs_per_period,
        maximum_atoms_per_job=sizing.maximum_atoms_per_job,
        period_cap_atoms=sizing.period_cap_atoms,
        target_prefund_periods=sizing.target_prefund_periods,
        period_length_blocks=100,
        policy_root="0" * 64,
    )

    assessment = funding.assess_service_budget_v1(policy)

    assert isinstance(assessment, funding.ServiceBudgetAssessmentV1)
    assert assessment.declared_maximum_period_liability_atoms <= sizing.period_cap_atoms
    assert assessment.required_prefund_atoms == sizing.target_prefund_atoms
    assert assessment.target_met is True


def test_bounded_evidence_closes_declared_arithmetic_queries() -> None:
    evidence = checker.bounded_cost_evidence()

    assert evidence["ceiling_rounding_search"]["counterexample"] is None
    assert evidence["prefund_separation_search"]["counterexample"] is None
    assert {row["id"] for row in evidence["named_mutant_witnesses"]} == {
        "FLOOR_CONTINGENCY_UNDERFUNDS",
        "FORECAST_COUNTED_AS_PREFUND",
        "LOW_CASE_PERIOD_CAP",
        "OMITTED_ROLE_MULTIPLICITY",
        "PROOF_MARKET_CREATES_REWARD",
        "CROSS_ASSET_PORTFOLIO",
    }


def test_proof_compute_quotes_do_not_become_proof_unit_prices() -> None:
    document = checker.build_document()
    proof_packet = document["critical_role_packets"]["proof_prover_and_proof_miner"]

    assert proof_packet["selected_cost_envelope"] is None
    assert proof_packet["proof_unit_price_atoms"] is None
    assert proof_packet["pricing_rule"] == "VERIFIED_BID_CAPPED_BY_PREFUNDED_BUDGET"
    assert document["proof_cost_boundary"]["conversion_allowed"] is False


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
    candidate.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    report = checker.check_artifact(candidate)

    assert report["ok"] is False
    assert any("duplicate JSON keys" in error for error in report["errors"])


def test_selected_cost_mutation_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        contract,
        "SELECTED_CRITICAL_SERVICE_COST_ENVELOPES",
        {
            **contract.SELECTED_CRITICAL_SERVICE_COST_ENVELOPES,
            "validator_finality_operator": {"payment_asset_id": "USD_E6"},
        },
    )

    with pytest.raises(ValueError, match="critical service costs must remain unselected"):
        checker.build_document()


def test_external_quote_mutation_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    quotes = contract.external_benchmark_quotes_v1()
    quote_id = "HETZNER_CCX13_US_MONTH_2026_06_15"
    monkeypatch.setattr(
        contract,
        "_EXTERNAL_BENCHMARK_QUOTES",
        {**quotes, quote_id: replace(quotes[quote_id], amount_atoms=50_980_000)},
    )

    with pytest.raises(ValueError, match="external benchmark quote core differs"):
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

    with pytest.raises(ValueError, match="critical-service research source drift"):
        checker.build_document()
