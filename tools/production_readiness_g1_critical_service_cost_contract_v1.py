"""Typed research contract for critical-service cost and revenue envelopes.

The contract keeps external price observations separate from complete role
compensation, computes exact integer runway caps, and refuses to treat forecast
revenue as prefunded custody.  It grants no payment, work-admission, policy,
settlement, or release authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from types import MappingProxyType
from typing import Final, TypeAlias

MAX_ATOMS: Final = 2**256 - 1
BPS_SCALE: Final = 10_000
USD_E6: Final = "USD_E6"

RESEARCH_SOURCE_PATHS: Final = (
    "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json",
    "tools/production_readiness_g1_service_funding_contract_v1.py",
    "docs/FIRE_REVENUE_SURFACE_ATLAS.md",
    "zk/asset_transfer_module_risc0/README.md",
    "zk/asset_lane_coordinator_risc0/README.md",
)

CRITICAL_SERVICE_ROLE_IDS: Final = frozenset(
    {
        "validator_finality_operator",
        "oracle_reporter_aggregator_disputer_and_watcher",
        "liquidator_and_keeper",
        "tau_relayer_and_destination_operator",
        "proof_prover_and_proof_miner",
    }
)

SELECTED_CRITICAL_SERVICE_COST_ENVELOPES: Final[
    dict[str, dict[str, object] | None]
] = {role_id: None for role_id in sorted(CRITICAL_SERVICE_ROLE_IDS)}

SELECTED_CRITICAL_SERVICE_REVENUE_INPUTS: Final[
    dict[str, dict[str, object] | None]
] = {role_id: None for role_id in sorted(CRITICAL_SERVICE_ROLE_IDS)}


class BenchmarkBillingUnitV1(StrEnum):
    CALENDAR_MONTH = "CALENDAR_MONTH"
    COMPUTE_HOUR = "COMPUTE_HOUR"


class BenchmarkEvidenceScopeV1(StrEnum):
    COMPONENT_ONLY = "COMPONENT_ONLY"


@dataclass(frozen=True, slots=True)
class ExternalBenchmarkQuoteV1:
    quote_id: str
    provider: str
    product: str
    payment_asset_id: str
    billing_unit: BenchmarkBillingUnitV1
    amount_atoms: int
    checked_on: str
    source_url: str
    evidence_scope: BenchmarkEvidenceScopeV1
    exclusions: tuple[str, ...]


_EXTERNAL_BENCHMARK_QUOTES: Final = MappingProxyType(
    {
        "HETZNER_CCX13_US_MONTH_2026_06_15": ExternalBenchmarkQuoteV1(
            quote_id="HETZNER_CCX13_US_MONTH_2026_06_15",
            provider="Hetzner",
            product="CCX13 USA new monthly price excluding IPv4 and tax",
            payment_asset_id=USD_E6,
            billing_unit=BenchmarkBillingUnitV1.CALENDAR_MONTH,
            amount_atoms=50_990_000,
            checked_on="2026-08-16",
            source_url=(
                "https://docs.hetzner.com/general/"
                "infrastructure-and-availability/price-adjustment/"
            ),
            evidence_scope=BenchmarkEvidenceScopeV1.COMPONENT_ONLY,
            exclusions=(
                "IPv4",
                "tax",
                "backups",
                "monitoring",
                "operator labor",
                "key management",
                "incident response",
            ),
        ),
        "HETZNER_CCX33_US_MONTH_2026_06_15": ExternalBenchmarkQuoteV1(
            quote_id="HETZNER_CCX33_US_MONTH_2026_06_15",
            provider="Hetzner",
            product="CCX33 USA new monthly price excluding IPv4 and tax",
            payment_asset_id=USD_E6,
            billing_unit=BenchmarkBillingUnitV1.CALENDAR_MONTH,
            amount_atoms=165_990_000,
            checked_on="2026-08-16",
            source_url=(
                "https://docs.hetzner.com/general/"
                "infrastructure-and-availability/price-adjustment/"
            ),
            evidence_scope=BenchmarkEvidenceScopeV1.COMPONENT_ONLY,
            exclusions=(
                "IPv4",
                "tax",
                "backups",
                "monitoring",
                "operator labor",
                "key management",
                "incident response",
            ),
        ),
        "DIGITALOCEAN_GENERAL_PURPOSE_START_MONTH_2026_08_16": (
            ExternalBenchmarkQuoteV1(
                quote_id=(
                    "DIGITALOCEAN_GENERAL_PURPOSE_START_MONTH_2026_08_16"
                ),
                provider="DigitalOcean",
                product="General Purpose dedicated-CPU Droplet starting price",
                payment_asset_id=USD_E6,
                billing_unit=BenchmarkBillingUnitV1.CALENDAR_MONTH,
                amount_atoms=63_000_000,
                checked_on="2026-08-16",
                source_url="https://www.digitalocean.com/solutions/vps-hosting",
                evidence_scope=BenchmarkEvidenceScopeV1.COMPONENT_ONLY,
                exclusions=(
                    "tax",
                    "backups",
                    "monitoring",
                    "operator labor",
                    "key management",
                    "incident response",
                ),
            )
        ),
        "DIGITALOCEAN_A4000_HOUR_2026_08_16": ExternalBenchmarkQuoteV1(
            quote_id="DIGITALOCEAN_A4000_HOUR_2026_08_16",
            provider="DigitalOcean",
            product="Dedicated NVIDIA A4000 GPU hourly price",
            payment_asset_id=USD_E6,
            billing_unit=BenchmarkBillingUnitV1.COMPUTE_HOUR,
            amount_atoms=760_000,
            checked_on="2026-08-16",
            source_url="https://www.digitalocean.com/pricing/additional-gpus",
            evidence_scope=BenchmarkEvidenceScopeV1.COMPONENT_ONLY,
            exclusions=(
                "proof compatibility",
                "proof cycles",
                "proof latency",
                "queueing",
                "operator margin",
                "verification failure risk",
            ),
        ),
        "DIGITALOCEAN_A100_HOUR_2026_08_16": ExternalBenchmarkQuoteV1(
            quote_id="DIGITALOCEAN_A100_HOUR_2026_08_16",
            provider="DigitalOcean",
            product="Dedicated NVIDIA A100 GPU hourly price",
            payment_asset_id=USD_E6,
            billing_unit=BenchmarkBillingUnitV1.COMPUTE_HOUR,
            amount_atoms=3_090_000,
            checked_on="2026-08-16",
            source_url="https://www.digitalocean.com/pricing/additional-gpus",
            evidence_scope=BenchmarkEvidenceScopeV1.COMPONENT_ONLY,
            exclusions=(
                "proof compatibility",
                "proof cycles",
                "proof latency",
                "queueing",
                "operator margin",
                "verification failure risk",
            ),
        ),
    }
)


def external_benchmark_quotes_v1() -> dict[str, ExternalBenchmarkQuoteV1]:
    return dict(_EXTERNAL_BENCHMARK_QUOTES)


class CostEstimateScopeV1(StrEnum):
    INFRASTRUCTURE_COMPONENT_ONLY = "INFRASTRUCTURE_COMPONENT_ONLY"
    FULL_ROLE_COST_CANDIDATE = "FULL_ROLE_COST_CANDIDATE"


class CostPeriodV1(StrEnum):
    CALENDAR_MONTH_RESEARCH_ONLY = "CALENDAR_MONTH_RESEARCH_ONLY"


@dataclass(frozen=True, slots=True)
class AmountRangeV1:
    low_atoms: int
    high_atoms: int


@dataclass(frozen=True, slots=True)
class ServiceCostEnvelopeV1:
    role_id: str
    payment_asset_id: str
    estimate_scope: CostEstimateScopeV1
    cost_period: CostPeriodV1
    role_count: int
    fixed_infrastructure_per_role: AmountRangeV1
    fixed_operator_per_role: AmountRangeV1
    maximum_jobs_per_period: int
    variable_cost_per_job: AmountRangeV1
    contingency_bps: int
    target_prefund_periods: int


class CostRejectCodeV1(StrEnum):
    ROLE_UNSUPPORTED = "ROLE_UNSUPPORTED"
    ASSET_INVALID = "ASSET_INVALID"
    ASSET_MISMATCH = "ASSET_MISMATCH"
    ESTIMATE_SCOPE_INVALID = "ESTIMATE_SCOPE_INVALID"
    COST_PERIOD_INVALID = "COST_PERIOD_INVALID"
    INTEGER_REQUIRED = "INTEGER_REQUIRED"
    AMOUNT_OUT_OF_RANGE = "AMOUNT_OUT_OF_RANGE"
    RANGE_INVERTED = "RANGE_INVERTED"
    ROLE_COUNT_INVALID = "ROLE_COUNT_INVALID"
    JOB_COUNT_INVALID = "JOB_COUNT_INVALID"
    CONTINGENCY_OUT_OF_RANGE = "CONTINGENCY_OUT_OF_RANGE"
    TARGET_PERIODS_INVALID = "TARGET_PERIODS_INVALID"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"
    EMPTY_PORTFOLIO = "EMPTY_PORTFOLIO"
    DUPLICATE_ROLE = "DUPLICATE_ROLE"


@dataclass(frozen=True, slots=True)
class ServiceCostRejectV1:
    code: CostRejectCodeV1
    detail: str


@dataclass(frozen=True, slots=True)
class ServiceCostAssessmentV1:
    role_id: str
    payment_asset_id: str
    estimate_scope: CostEstimateScopeV1
    cost_period: CostPeriodV1
    role_count: int
    fixed_period_cost_low_atoms: int
    fixed_period_cost_high_atoms: int
    maximum_jobs_per_period: int
    maximum_atoms_per_job: int
    variable_period_cost_low_atoms: int
    variable_period_cost_high_atoms: int
    contingency_bps: int
    raw_period_cost_low_atoms: int
    raw_period_cost_high_atoms: int
    loaded_period_cost_low_atoms: int
    loaded_period_cost_high_atoms: int
    recommended_period_cap_atoms: int
    target_prefund_periods: int
    target_prefund_atoms: int
    component_set_complete: bool
    selection_eligible: bool


ServiceCostOutcomeV1: TypeAlias = ServiceCostAssessmentV1 | ServiceCostRejectV1


def _valid_asset_id(asset_id: object) -> bool:
    return (
        isinstance(asset_id, str)
        and asset_id == asset_id.strip()
        and 1 <= len(asset_id) <= 64
    )


def _validate_exact_int(value: object) -> CostRejectCodeV1 | None:
    if type(value) is not int:
        return CostRejectCodeV1.INTEGER_REQUIRED
    if value < 0 or value > MAX_ATOMS:
        return CostRejectCodeV1.AMOUNT_OUT_OF_RANGE
    return None


def _validate_range(value: AmountRangeV1) -> CostRejectCodeV1 | None:
    low_error = _validate_exact_int(value.low_atoms)
    if low_error is not None:
        return low_error
    high_error = _validate_exact_int(value.high_atoms)
    if high_error is not None:
        return high_error
    if value.low_atoms > value.high_atoms:
        return CostRejectCodeV1.RANGE_INVERTED
    return None


def _checked_add(left: int, right: int) -> int:
    value = left + right
    if value > MAX_ATOMS:
        raise OverflowError
    return value


def _checked_mul(left: int, right: int) -> int:
    value = left * right
    if value > MAX_ATOMS:
        raise OverflowError
    return value


def _ceil_loaded_atoms(value_atoms: int, contingency_bps: int) -> int:
    factor = BPS_SCALE + contingency_bps
    numerator = _checked_mul(value_atoms, factor)
    quotient, remainder = divmod(numerator, BPS_SCALE)
    return _checked_add(quotient, 1 if remainder else 0)


def assess_service_cost_envelope_v1(
    envelope: ServiceCostEnvelopeV1,
) -> ServiceCostOutcomeV1:
    if envelope.role_id not in CRITICAL_SERVICE_ROLE_IDS:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ROLE_UNSUPPORTED,
            "role is outside the exact critical-service registry",
        )
    if not _valid_asset_id(envelope.payment_asset_id):
        return ServiceCostRejectV1(
            CostRejectCodeV1.ASSET_INVALID,
            "payment asset id must be a canonical non-empty string",
        )
    if type(envelope.estimate_scope) is not CostEstimateScopeV1:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ESTIMATE_SCOPE_INVALID,
            "estimate scope must be a closed enum value",
        )
    if type(envelope.cost_period) is not CostPeriodV1:
        return ServiceCostRejectV1(
            CostRejectCodeV1.COST_PERIOD_INVALID,
            "cost period must be a closed enum value",
        )
    for amount_range in (
        envelope.fixed_infrastructure_per_role,
        envelope.fixed_operator_per_role,
        envelope.variable_cost_per_job,
    ):
        error = _validate_range(amount_range)
        if error is not None:
            return ServiceCostRejectV1(error, "cost range is invalid")
    for field_name, value in (
        ("role_count", envelope.role_count),
        ("maximum_jobs_per_period", envelope.maximum_jobs_per_period),
        ("contingency_bps", envelope.contingency_bps),
        ("target_prefund_periods", envelope.target_prefund_periods),
    ):
        error = _validate_exact_int(value)
        if error is not None:
            return ServiceCostRejectV1(error, f"{field_name} must be an exact integer")
    if envelope.role_count == 0:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ROLE_COUNT_INVALID,
            "role count must be positive",
        )
    if envelope.maximum_jobs_per_period > MAX_ATOMS:
        return ServiceCostRejectV1(
            CostRejectCodeV1.JOB_COUNT_INVALID,
            "maximum job count exceeds the integer domain",
        )
    if envelope.contingency_bps > BPS_SCALE:
        return ServiceCostRejectV1(
            CostRejectCodeV1.CONTINGENCY_OUT_OF_RANGE,
            "contingency must be between zero and 10000 basis points",
        )
    if envelope.target_prefund_periods == 0:
        return ServiceCostRejectV1(
            CostRejectCodeV1.TARGET_PERIODS_INVALID,
            "target prefund periods must be positive",
        )

    try:
        fixed_per_role_low = _checked_add(
            envelope.fixed_infrastructure_per_role.low_atoms,
            envelope.fixed_operator_per_role.low_atoms,
        )
        fixed_per_role_high = _checked_add(
            envelope.fixed_infrastructure_per_role.high_atoms,
            envelope.fixed_operator_per_role.high_atoms,
        )
        fixed_low = _checked_mul(fixed_per_role_low, envelope.role_count)
        fixed_high = _checked_mul(fixed_per_role_high, envelope.role_count)
        variable_low = _checked_mul(
            envelope.variable_cost_per_job.low_atoms,
            envelope.maximum_jobs_per_period,
        )
        variable_high = _checked_mul(
            envelope.variable_cost_per_job.high_atoms,
            envelope.maximum_jobs_per_period,
        )
        raw_low = _checked_add(fixed_low, variable_low)
        raw_high = _checked_add(fixed_high, variable_high)
        loaded_low = _ceil_loaded_atoms(raw_low, envelope.contingency_bps)
        loaded_high = _ceil_loaded_atoms(raw_high, envelope.contingency_bps)
        target_prefund = _checked_mul(
            loaded_high,
            envelope.target_prefund_periods,
        )
    except OverflowError:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ARITHMETIC_OVERFLOW,
            "cost-envelope arithmetic exceeds 2^256 - 1",
        )

    complete = (
        envelope.estimate_scope is CostEstimateScopeV1.FULL_ROLE_COST_CANDIDATE
    )
    return ServiceCostAssessmentV1(
        role_id=envelope.role_id,
        payment_asset_id=envelope.payment_asset_id,
        estimate_scope=envelope.estimate_scope,
        cost_period=envelope.cost_period,
        role_count=envelope.role_count,
        fixed_period_cost_low_atoms=fixed_low,
        fixed_period_cost_high_atoms=fixed_high,
        maximum_jobs_per_period=envelope.maximum_jobs_per_period,
        maximum_atoms_per_job=envelope.variable_cost_per_job.high_atoms,
        variable_period_cost_low_atoms=variable_low,
        variable_period_cost_high_atoms=variable_high,
        contingency_bps=envelope.contingency_bps,
        raw_period_cost_low_atoms=raw_low,
        raw_period_cost_high_atoms=raw_high,
        loaded_period_cost_low_atoms=loaded_low,
        loaded_period_cost_high_atoms=loaded_high,
        recommended_period_cap_atoms=loaded_high,
        target_prefund_periods=envelope.target_prefund_periods,
        target_prefund_atoms=target_prefund,
        component_set_complete=complete,
        selection_eligible=complete and loaded_high > 0,
    )


@dataclass(frozen=True, slots=True)
class ServiceRevenueForecastV1:
    payment_asset_id: str
    realized_purpose_bound_prefund_atoms: int
    recurring_revenue_per_period: AmountRangeV1


@dataclass(frozen=True, slots=True)
class ServiceAffordabilityAssessmentV1:
    role_id: str
    payment_asset_id: str
    target_prefund_atoms: int
    realized_purpose_bound_prefund_atoms: int
    prefund_shortfall_atoms: int
    prefund_target_met: bool
    recurring_revenue_low_atoms: int
    recurring_revenue_high_atoms: int
    recurring_low_shortfall_atoms: int
    recurring_high_shortfall_atoms: int
    recurring_break_even_at_low: bool
    recurring_break_even_at_high: bool
    forecast_counts_as_prefund: bool
    sizing_conditions_met: bool


ServiceAffordabilityOutcomeV1: TypeAlias = (
    ServiceAffordabilityAssessmentV1 | ServiceCostRejectV1
)


def assess_service_affordability_v1(
    cost: ServiceCostAssessmentV1,
    revenue: ServiceRevenueForecastV1,
) -> ServiceAffordabilityOutcomeV1:
    if not _valid_asset_id(revenue.payment_asset_id):
        return ServiceCostRejectV1(
            CostRejectCodeV1.ASSET_INVALID,
            "revenue payment asset is invalid",
        )
    if revenue.payment_asset_id != cost.payment_asset_id:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ASSET_MISMATCH,
            "cost and revenue assets differ",
        )
    reserve_error = _validate_exact_int(
        revenue.realized_purpose_bound_prefund_atoms
    )
    if reserve_error is not None:
        return ServiceCostRejectV1(reserve_error, "prefund atoms are invalid")
    range_error = _validate_range(revenue.recurring_revenue_per_period)
    if range_error is not None:
        return ServiceCostRejectV1(range_error, "revenue range is invalid")

    prefund = revenue.realized_purpose_bound_prefund_atoms
    target = cost.target_prefund_atoms
    period_cap = cost.recommended_period_cap_atoms
    low = revenue.recurring_revenue_per_period.low_atoms
    high = revenue.recurring_revenue_per_period.high_atoms
    prefund_shortfall = max(0, target - prefund)
    low_shortfall = max(0, period_cap - low)
    high_shortfall = max(0, period_cap - high)
    target_met = prefund_shortfall == 0
    low_break_even = low_shortfall == 0
    high_break_even = high_shortfall == 0
    return ServiceAffordabilityAssessmentV1(
        role_id=cost.role_id,
        payment_asset_id=cost.payment_asset_id,
        target_prefund_atoms=target,
        realized_purpose_bound_prefund_atoms=prefund,
        prefund_shortfall_atoms=prefund_shortfall,
        prefund_target_met=target_met,
        recurring_revenue_low_atoms=low,
        recurring_revenue_high_atoms=high,
        recurring_low_shortfall_atoms=low_shortfall,
        recurring_high_shortfall_atoms=high_shortfall,
        recurring_break_even_at_low=low_break_even,
        recurring_break_even_at_high=high_break_even,
        forecast_counts_as_prefund=False,
        sizing_conditions_met=(
            cost.selection_eligible and target_met and low_break_even
        ),
    )


@dataclass(frozen=True, slots=True)
class ServiceCostPortfolioV1:
    payment_asset_id: str
    role_ids: tuple[str, ...]
    period_cap_atoms: int
    target_prefund_atoms: int
    selection_eligible: bool


ServiceCostPortfolioOutcomeV1: TypeAlias = (
    ServiceCostPortfolioV1 | ServiceCostRejectV1
)


def aggregate_service_cost_assessments_v1(
    assessments: tuple[ServiceCostAssessmentV1, ...],
) -> ServiceCostPortfolioOutcomeV1:
    if not assessments:
        return ServiceCostRejectV1(
            CostRejectCodeV1.EMPTY_PORTFOLIO,
            "at least one service cost assessment is required",
        )
    assets = {assessment.payment_asset_id for assessment in assessments}
    if len(assets) != 1:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ASSET_MISMATCH,
            "cross-asset costs require a selected conversion and cannot be summed",
        )
    role_ids = [assessment.role_id for assessment in assessments]
    if len(role_ids) != len(set(role_ids)):
        return ServiceCostRejectV1(
            CostRejectCodeV1.DUPLICATE_ROLE,
            "a role may occur only once in a portfolio",
        )
    try:
        period_cap = 0
        target_prefund = 0
        for assessment in assessments:
            period_cap = _checked_add(
                period_cap,
                assessment.recommended_period_cap_atoms,
            )
            target_prefund = _checked_add(
                target_prefund,
                assessment.target_prefund_atoms,
            )
    except OverflowError:
        return ServiceCostRejectV1(
            CostRejectCodeV1.ARITHMETIC_OVERFLOW,
            "portfolio arithmetic exceeds 2^256 - 1",
        )
    return ServiceCostPortfolioV1(
        payment_asset_id=next(iter(assets)),
        role_ids=tuple(sorted(role_ids)),
        period_cap_atoms=period_cap,
        target_prefund_atoms=target_prefund,
        selection_eligible=all(
            assessment.selection_eligible for assessment in assessments
        ),
    )


@dataclass(frozen=True, slots=True)
class ServiceBudgetSizingV1:
    role_id: str
    payment_asset_id: str
    fixed_atoms_per_period: int
    maximum_jobs_per_period: int
    maximum_atoms_per_job: int
    period_cap_atoms: int
    target_prefund_periods: int
    target_prefund_atoms: int


def to_service_budget_sizing_v1(
    cost: ServiceCostAssessmentV1,
) -> ServiceBudgetSizingV1:
    return ServiceBudgetSizingV1(
        role_id=cost.role_id,
        payment_asset_id=cost.payment_asset_id,
        fixed_atoms_per_period=cost.fixed_period_cost_high_atoms,
        maximum_jobs_per_period=cost.maximum_jobs_per_period,
        maximum_atoms_per_job=cost.maximum_atoms_per_job,
        period_cap_atoms=cost.recommended_period_cap_atoms,
        target_prefund_periods=cost.target_prefund_periods,
        target_prefund_atoms=cost.target_prefund_atoms,
    )


@dataclass(frozen=True, slots=True)
class ValidatorInfrastructureScenarioV1:
    payment_asset_id: str
    role_count: int
    monthly_low_atoms: int
    monthly_high_atoms: int
    runway_18_month_low_atoms: int
    runway_18_month_high_atoms: int
    runway_36_month_low_atoms: int
    runway_36_month_high_atoms: int
    selection_eligible: bool


def validator_infrastructure_scenario_v1() -> ValidatorInfrastructureScenarioV1:
    quotes = external_benchmark_quotes_v1()
    low = quotes["HETZNER_CCX13_US_MONTH_2026_06_15"].amount_atoms
    high = quotes["HETZNER_CCX33_US_MONTH_2026_06_15"].amount_atoms
    role_count = 7
    monthly_low = _checked_mul(low, role_count)
    monthly_high = _checked_mul(high, role_count)
    return ValidatorInfrastructureScenarioV1(
        payment_asset_id=USD_E6,
        role_count=role_count,
        monthly_low_atoms=monthly_low,
        monthly_high_atoms=monthly_high,
        runway_18_month_low_atoms=_checked_mul(monthly_low, 18),
        runway_18_month_high_atoms=_checked_mul(monthly_high, 18),
        runway_36_month_low_atoms=_checked_mul(monthly_low, 36),
        runway_36_month_high_atoms=_checked_mul(monthly_high, 36),
        selection_eligible=False,
    )
