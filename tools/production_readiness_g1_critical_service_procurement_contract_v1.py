"""Typed research contract for critical-service procurement and qualification.

The contract makes complete role quotes comparable, binds qualification to an
exact service and benchmark subject, checks a bounded skin-in-the-game
inequality, and exhaustively selects a finite multi-provider set.  Every value
is caller-constructible research data.  The module grants no work-admission,
payment, activation, settlement, or release authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from enum import StrEnum
from itertools import combinations
from typing import Final, TypeAlias

from tools import production_readiness_g1_critical_service_cost_contract_v1 as costs

MAX_ATOMS: Final = 2**256 - 1
BPS_SCALE: Final = 10_000
MAX_RESEARCH_CANDIDATES: Final = 16

RESEARCH_SOURCE_PATHS: Final = (
    "docs/research/PRODUCTION_READINESS_G1_CRITICAL_SERVICE_COSTS_V1.json",
    "tools/production_readiness_g1_critical_service_cost_contract_v1.py",
    "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json",
)

CRITICAL_SERVICE_ROLE_IDS: Final = costs.CRITICAL_SERVICE_ROLE_IDS

SELECTED_PROCUREMENT_POLICIES: Final[dict[str, dict[str, object] | None]] = {
    role_id: None for role_id in sorted(CRITICAL_SERVICE_ROLE_IDS)
}
SELECTED_QUALIFICATION_POLICIES: Final[dict[str, dict[str, object] | None]] = {
    role_id: None for role_id in sorted(CRITICAL_SERVICE_ROLE_IDS)
}
SELECTED_COMPLETE_QUOTES: Final[dict[str, dict[str, object] | None]] = {
    role_id: None for role_id in sorted(CRITICAL_SERVICE_ROLE_IDS)
}

ACTIVATION_AUTHORIZED: Final = False
WORK_ADMISSION_AUTHORIZED: Final = False
PAYMENT_AUTHORIZED: Final = False


class ProcurementRejectCodeV1(StrEnum):
    ROLE_UNSUPPORTED = "ROLE_UNSUPPORTED"
    IDENTIFIER_INVALID = "IDENTIFIER_INVALID"
    ROOT_INVALID = "ROOT_INVALID"
    INTEGER_REQUIRED = "INTEGER_REQUIRED"
    AMOUNT_OUT_OF_RANGE = "AMOUNT_OUT_OF_RANGE"
    CONTINGENCY_OUT_OF_RANGE = "CONTINGENCY_OUT_OF_RANGE"
    EPOCH_RANGE_INVALID = "EPOCH_RANGE_INVALID"
    QUOTE_NOT_CURRENT = "QUOTE_NOT_CURRENT"
    FAILURE_DOMAIN_INVALID = "FAILURE_DOMAIN_INVALID"
    DUPLICATE_FAILURE_DOMAIN_KIND = "DUPLICATE_FAILURE_DOMAIN_KIND"
    QUOTE_ZERO_CAP = "QUOTE_ZERO_CAP"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"
    QUOTE_BINDING_MISMATCH = "QUOTE_BINDING_MISMATCH"
    PROFILE_BINDING_MISMATCH = "PROFILE_BINDING_MISMATCH"
    QUALIFICATION_POLICY_INVALID = "QUALIFICATION_POLICY_INVALID"
    QUALIFICATION_OBSERVATION_INVALID = "QUALIFICATION_OBSERVATION_INVALID"
    INVALID_WORK_ACCEPTED = "INVALID_WORK_ACCEPTED"
    REPLAY_ACCEPTED = "REPLAY_ACCEPTED"
    SAFETY_VIOLATION = "SAFETY_VIOLATION"
    RECOVERY_FAILURE = "RECOVERY_FAILURE"
    QUALIFICATION_THRESHOLD_MISSED = "QUALIFICATION_THRESHOLD_MISSED"
    BOND_ASSET_MISMATCH = "BOND_ASSET_MISMATCH"
    SLASH_EXCEEDS_BOND = "SLASH_EXCEEDS_BOND"
    BOND_INADEQUATE = "BOND_INADEQUATE"
    DUPLICATE_QUOTE = "DUPLICATE_QUOTE"
    CANDIDATE_LIMIT_EXCEEDED = "CANDIDATE_LIMIT_EXCEEDED"
    POLICY_MISMATCH = "POLICY_MISMATCH"
    INSUFFICIENT_QUALIFIED_BIDS = "INSUFFICIENT_QUALIFIED_BIDS"
    NO_FEASIBLE_SELECTION = "NO_FEASIBLE_SELECTION"


@dataclass(frozen=True, slots=True)
class ProcurementRejectV1:
    code: ProcurementRejectCodeV1
    detail: str


@dataclass(frozen=True, slots=True)
class FailureDomainV1:
    kind: str
    value: str


@dataclass(frozen=True, slots=True)
class QuotedCostComponentsV1:
    fixed_infrastructure_atoms: int
    fixed_operator_on_call_atoms: int
    fixed_security_monitoring_atoms: int
    fixed_data_license_external_io_atoms: int
    fixed_risk_capital_insurance_atoms: int
    variable_compute_execution_per_job_atoms: int
    variable_labor_external_per_job_atoms: int
    one_time_onboarding_atoms: int


@dataclass(frozen=True, slots=True)
class CompleteServiceQuoteV1:
    quote_id: str
    role_id: str
    provider_id: str
    beneficial_owner_id: str
    payment_asset_id: str
    valid_from_epoch: int
    valid_through_epoch: int
    service_spec_root: str
    benchmark_profile_root: str
    execution_subject_root: str
    hardware_profile_root: str
    identity_evidence_root: str
    beneficial_owner_evidence_root: str
    signed_quote_evidence_root: str
    failure_domains: tuple[FailureDomainV1, ...]
    cost_components: QuotedCostComponentsV1
    maximum_jobs_per_period: int
    contingency_bps: int
    target_prefund_periods: int


@dataclass(frozen=True, slots=True)
class CompleteQuoteAssessmentV1:
    quote_id: str
    role_id: str
    provider_id: str
    beneficial_owner_id: str
    payment_asset_id: str
    valid_from_epoch: int
    valid_through_epoch: int
    fixed_period_atoms: int
    variable_cost_per_job_atoms: int
    maximum_jobs_per_period: int
    variable_period_atoms: int
    raw_period_atoms: int
    contingency_bps: int
    quoted_period_cap_atoms: int
    one_time_onboarding_atoms: int
    target_prefund_periods: int
    target_prefund_atoms: int
    quote_commitment_root: str
    component_set_complete: bool
    selection_eligible: bool


CompleteQuoteOutcomeV1: TypeAlias = CompleteQuoteAssessmentV1 | ProcurementRejectV1


@dataclass(frozen=True, slots=True)
class BondTermsV1:
    quote_id: str
    payment_asset_id: str
    bond_atoms: int
    slash_atoms: int
    maximum_defect_gain_atoms: int
    future_value_lost_atoms: int
    detection_probability_bps: int


@dataclass(frozen=True, slots=True)
class BondAdequacyAssessmentV1:
    quote_id: str
    payment_asset_id: str
    bond_atoms: int
    slash_atoms: int
    detection_probability_bps: int
    deterrence_left_scaled_atoms: int
    maximum_defect_gain_scaled_atoms: int
    incentive_margin_scaled_atoms: int
    incentive_compatible: bool


BondAdequacyOutcomeV1: TypeAlias = BondAdequacyAssessmentV1 | ProcurementRejectV1


@dataclass(frozen=True, slots=True)
class QualificationPolicyV1:
    role_id: str
    evaluation_epoch: int
    service_spec_root: str
    benchmark_profile_root: str
    execution_subject_root: str
    hardware_profile_root: str
    minimum_successful_trials: int
    maximum_failed_trials: int
    maximum_p95_latency_ms: int
    minimum_availability_bps: int
    maximum_peak_memory_bytes: int


@dataclass(frozen=True, slots=True)
class QualificationObservationV1:
    quote_id: str
    role_id: str
    service_spec_root: str
    benchmark_profile_root: str
    execution_subject_root: str
    hardware_profile_root: str
    evidence_root: str
    successful_trials: int
    failed_trials: int
    invalid_work_accepts: int
    replay_or_duplicate_accepts: int
    safety_violation_events: int
    recovery_failures: int
    p95_latency_ms: int
    availability_bps: int
    peak_memory_bytes: int


@dataclass(frozen=True, slots=True)
class QualifiedServiceBidV1:
    quote_id: str
    role_id: str
    provider_id: str
    beneficial_owner_id: str
    payment_asset_id: str
    valid_from_epoch: int
    valid_through_epoch: int
    service_spec_root: str
    benchmark_profile_root: str
    execution_subject_root: str
    hardware_profile_root: str
    failure_domains: tuple[FailureDomainV1, ...]
    quoted_period_cap_atoms: int
    one_time_onboarding_atoms: int
    target_prefund_periods: int
    target_prefund_atoms: int
    bond_atoms: int
    slash_atoms: int
    quote_commitment_root: str
    qualification_evidence_root: str


QualificationOutcomeV1: TypeAlias = QualifiedServiceBidV1 | ProcurementRejectV1


@dataclass(frozen=True, slots=True)
class FailureDomainCapV1:
    kind: str
    maximum_selected_per_value: int


@dataclass(frozen=True, slots=True)
class ProcurementPolicyV1:
    role_id: str
    payment_asset_id: str
    selection_epoch: int
    service_spec_root: str
    benchmark_profile_root: str
    execution_subject_root: str
    hardware_profile_root: str
    required_winners: int
    period_budget_cap_atoms: int
    onboarding_budget_cap_atoms: int
    maximum_per_beneficial_owner: int
    failure_domain_caps: tuple[FailureDomainCapV1, ...]
    maximum_candidate_count: int


@dataclass(frozen=True, slots=True)
class ProcurementSelectionV1:
    role_id: str
    payment_asset_id: str
    selection_epoch: int
    selected_quote_ids: tuple[str, ...]
    selected_provider_ids: tuple[str, ...]
    total_period_cap_atoms: int
    total_onboarding_atoms: int
    total_bond_atoms: int
    exact_combinations_evaluated: int
    objective: str
    work_admission_authorized: bool
    payment_authorized: bool


ProcurementOutcomeV1: TypeAlias = ProcurementSelectionV1 | ProcurementRejectV1
CostRefinementOutcomeV1: TypeAlias = costs.ServiceCostAssessmentV1 | ProcurementRejectV1


_IDENTIFIER_CHARS: Final = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-"
)
_HEX_CHARS: Final = frozenset("0123456789abcdef")


def _valid_identifier(value: object) -> bool:
    return (
        isinstance(value, str)
        and value == value.strip()
        and 1 <= len(value) <= 128
        and all(character in _IDENTIFIER_CHARS for character in value)
    )


def _valid_root(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in _HEX_CHARS for character in value)
    )


def _integer_error(value: object) -> ProcurementRejectCodeV1 | None:
    if type(value) is not int:
        return ProcurementRejectCodeV1.INTEGER_REQUIRED
    if value < 0 or value > MAX_ATOMS:
        return ProcurementRejectCodeV1.AMOUNT_OUT_OF_RANGE
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


def _checked_sum(values: tuple[int, ...]) -> int:
    total = 0
    for value in values:
        total = _checked_add(total, value)
    return total


def _ceil_contingency(value_atoms: int, contingency_bps: int) -> int:
    numerator = _checked_mul(value_atoms, BPS_SCALE + contingency_bps)
    quotient, remainder = divmod(numerator, BPS_SCALE)
    return _checked_add(quotient, 1 if remainder else 0)


def _quote_commitment_root(quote: CompleteServiceQuoteV1) -> str:
    encoded = json.dumps(
        asdict(quote),
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validate_roots(values: tuple[object, ...]) -> bool:
    return all(_valid_root(value) for value in values)


def assess_complete_quote_v1(
    quote: CompleteServiceQuoteV1,
    *,
    evaluation_epoch: int,
) -> CompleteQuoteOutcomeV1:
    if type(quote) is not CompleteServiceQuoteV1:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUOTE_BINDING_MISMATCH,
            "quote must use the closed typed schema",
        )
    if quote.role_id not in CRITICAL_SERVICE_ROLE_IDS:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROLE_UNSUPPORTED,
            "quote role is outside the exact critical-service registry",
        )
    identifiers = (
        quote.quote_id,
        quote.role_id,
        quote.provider_id,
        quote.beneficial_owner_id,
        quote.payment_asset_id,
    )
    if not all(_valid_identifier(value) for value in identifiers):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.IDENTIFIER_INVALID,
            "quote identifiers must be canonical bounded ASCII tokens",
        )
    roots = (
        quote.service_spec_root,
        quote.benchmark_profile_root,
        quote.execution_subject_root,
        quote.hardware_profile_root,
        quote.identity_evidence_root,
        quote.beneficial_owner_evidence_root,
        quote.signed_quote_evidence_root,
    )
    if not _validate_roots(roots):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROOT_INVALID,
            "quote evidence and subject roots must be lowercase SHA-256 hex",
        )
    for field_name, value in (
        ("valid_from_epoch", quote.valid_from_epoch),
        ("valid_through_epoch", quote.valid_through_epoch),
        ("evaluation_epoch", evaluation_epoch),
        ("maximum_jobs_per_period", quote.maximum_jobs_per_period),
        ("contingency_bps", quote.contingency_bps),
        ("target_prefund_periods", quote.target_prefund_periods),
    ):
        error = _integer_error(value)
        if error is not None:
            return ProcurementRejectV1(error, f"{field_name} must be an exact integer")
    if quote.valid_from_epoch > quote.valid_through_epoch:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.EPOCH_RANGE_INVALID,
            "quote validity range is inverted",
        )
    if not quote.valid_from_epoch <= evaluation_epoch <= quote.valid_through_epoch:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUOTE_NOT_CURRENT,
            "quote is not valid at the evaluation epoch",
        )
    if quote.contingency_bps > BPS_SCALE:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.CONTINGENCY_OUT_OF_RANGE,
            "contingency must be between zero and 10000 basis points",
        )
    if quote.target_prefund_periods == 0:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.AMOUNT_OUT_OF_RANGE,
            "target prefund periods must be positive",
        )
    if type(quote.cost_components) is not QuotedCostComponentsV1:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUALIFICATION_OBSERVATION_INVALID,
            "quote cost components must use the closed typed schema",
        )
    component_values = tuple(asdict(quote.cost_components).values())
    for value in component_values:
        error = _integer_error(value)
        if error is not None:
            return ProcurementRejectV1(error, "every named cost component must be exact")
    if type(quote.failure_domains) is not tuple or not quote.failure_domains:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.FAILURE_DOMAIN_INVALID,
            "at least one typed failure domain is required",
        )
    domain_kinds: list[str] = []
    for domain in quote.failure_domains:
        if (
            type(domain) is not FailureDomainV1
            or not _valid_identifier(domain.kind)
            or not _valid_identifier(domain.value)
        ):
            return ProcurementRejectV1(
                ProcurementRejectCodeV1.FAILURE_DOMAIN_INVALID,
                "failure domains must contain canonical typed identifiers",
            )
        domain_kinds.append(domain.kind)
    if len(domain_kinds) != len(set(domain_kinds)):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.DUPLICATE_FAILURE_DOMAIN_KIND,
            "a quote may declare one value per failure-domain kind",
        )
    if domain_kinds != sorted(domain_kinds):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.FAILURE_DOMAIN_INVALID,
            "failure domains must be in canonical kind order",
        )

    components = quote.cost_components
    try:
        fixed_period_atoms = _checked_sum(
            (
                components.fixed_infrastructure_atoms,
                components.fixed_operator_on_call_atoms,
                components.fixed_security_monitoring_atoms,
                components.fixed_data_license_external_io_atoms,
                components.fixed_risk_capital_insurance_atoms,
            )
        )
        variable_per_job_atoms = _checked_add(
            components.variable_compute_execution_per_job_atoms,
            components.variable_labor_external_per_job_atoms,
        )
        variable_period_atoms = _checked_mul(
            variable_per_job_atoms,
            quote.maximum_jobs_per_period,
        )
        raw_period_atoms = _checked_add(fixed_period_atoms, variable_period_atoms)
        quoted_period_cap_atoms = _ceil_contingency(
            raw_period_atoms,
            quote.contingency_bps,
        )
        target_prefund_atoms = _checked_mul(
            quoted_period_cap_atoms,
            quote.target_prefund_periods,
        )
    except OverflowError:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ARITHMETIC_OVERFLOW,
            "quote arithmetic exceeds 2^256 - 1",
        )
    if quoted_period_cap_atoms == 0:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUOTE_ZERO_CAP,
            "a complete quote must declare a positive recurring period cap",
        )
    return CompleteQuoteAssessmentV1(
        quote_id=quote.quote_id,
        role_id=quote.role_id,
        provider_id=quote.provider_id,
        beneficial_owner_id=quote.beneficial_owner_id,
        payment_asset_id=quote.payment_asset_id,
        valid_from_epoch=quote.valid_from_epoch,
        valid_through_epoch=quote.valid_through_epoch,
        fixed_period_atoms=fixed_period_atoms,
        variable_cost_per_job_atoms=variable_per_job_atoms,
        maximum_jobs_per_period=quote.maximum_jobs_per_period,
        variable_period_atoms=variable_period_atoms,
        raw_period_atoms=raw_period_atoms,
        contingency_bps=quote.contingency_bps,
        quoted_period_cap_atoms=quoted_period_cap_atoms,
        one_time_onboarding_atoms=components.one_time_onboarding_atoms,
        target_prefund_periods=quote.target_prefund_periods,
        target_prefund_atoms=target_prefund_atoms,
        quote_commitment_root=_quote_commitment_root(quote),
        component_set_complete=True,
        selection_eligible=True,
    )


def refine_quote_to_cost_envelope_v1(
    quote: CompleteServiceQuoteV1,
    *,
    evaluation_epoch: int,
) -> CostRefinementOutcomeV1:
    quote_assessment = assess_complete_quote_v1(
        quote,
        evaluation_epoch=evaluation_epoch,
    )
    if isinstance(quote_assessment, ProcurementRejectV1):
        return quote_assessment
    components = quote.cost_components
    try:
        fixed_operator_atoms = _checked_sum(
            (
                components.fixed_operator_on_call_atoms,
                components.fixed_security_monitoring_atoms,
                components.fixed_data_license_external_io_atoms,
                components.fixed_risk_capital_insurance_atoms,
            )
        )
        variable_per_job_atoms = _checked_add(
            components.variable_compute_execution_per_job_atoms,
            components.variable_labor_external_per_job_atoms,
        )
    except OverflowError:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ARITHMETIC_OVERFLOW,
            "cost-envelope refinement arithmetic overflowed",
        )
    envelope = costs.ServiceCostEnvelopeV1(
        role_id=quote.role_id,
        payment_asset_id=quote.payment_asset_id,
        estimate_scope=costs.CostEstimateScopeV1.FULL_ROLE_COST_CANDIDATE,
        cost_period=costs.CostPeriodV1.CALENDAR_MONTH_RESEARCH_ONLY,
        role_count=1,
        fixed_infrastructure_per_role=costs.AmountRangeV1(
            components.fixed_infrastructure_atoms,
            components.fixed_infrastructure_atoms,
        ),
        fixed_operator_per_role=costs.AmountRangeV1(
            fixed_operator_atoms,
            fixed_operator_atoms,
        ),
        maximum_jobs_per_period=quote.maximum_jobs_per_period,
        variable_cost_per_job=costs.AmountRangeV1(
            variable_per_job_atoms,
            variable_per_job_atoms,
        ),
        contingency_bps=quote.contingency_bps,
        target_prefund_periods=quote.target_prefund_periods,
    )
    refined = costs.assess_service_cost_envelope_v1(envelope)
    if not isinstance(refined, costs.ServiceCostAssessmentV1):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.PROFILE_BINDING_MISMATCH,
            "complete quote did not refine to the existing cost contract",
        )
    if (
        refined.recommended_period_cap_atoms != quote_assessment.quoted_period_cap_atoms
        or refined.target_prefund_atoms != quote_assessment.target_prefund_atoms
    ):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.PROFILE_BINDING_MISMATCH,
            "quote and cost-envelope arithmetic diverged",
        )
    return refined


def assess_bond_adequacy_v1(
    terms: BondTermsV1,
    *,
    expected_quote_id: str,
    expected_asset_id: str,
) -> BondAdequacyOutcomeV1:
    if type(terms) is not BondTermsV1:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUOTE_BINDING_MISMATCH,
            "bond terms must use the closed typed schema",
        )
    if not _valid_identifier(terms.quote_id) or terms.quote_id != expected_quote_id:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUOTE_BINDING_MISMATCH,
            "bond terms do not bind the expected quote",
        )
    if not _valid_identifier(terms.payment_asset_id) or terms.payment_asset_id != expected_asset_id:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.BOND_ASSET_MISMATCH,
            "bond and quote payment assets differ",
        )
    for field_name, value in (
        ("bond_atoms", terms.bond_atoms),
        ("slash_atoms", terms.slash_atoms),
        ("maximum_defect_gain_atoms", terms.maximum_defect_gain_atoms),
        ("future_value_lost_atoms", terms.future_value_lost_atoms),
        ("detection_probability_bps", terms.detection_probability_bps),
    ):
        error = _integer_error(value)
        if error is not None:
            return ProcurementRejectV1(error, f"{field_name} must be an exact integer")
    if terms.detection_probability_bps > BPS_SCALE:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.AMOUNT_OUT_OF_RANGE,
            "detection probability exceeds 10000 basis points",
        )
    if terms.slash_atoms > terms.bond_atoms:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.SLASH_EXCEEDS_BOND,
            "declared slash exceeds bonded custody",
        )
    try:
        detected_slash = _checked_mul(
            terms.detection_probability_bps,
            terms.slash_atoms,
        )
        future_value = _checked_mul(BPS_SCALE, terms.future_value_lost_atoms)
        deterrence_left = _checked_add(detected_slash, future_value)
        maximum_gain = _checked_mul(BPS_SCALE, terms.maximum_defect_gain_atoms)
    except OverflowError:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ARITHMETIC_OVERFLOW,
            "bond-adequacy arithmetic exceeds 2^256 - 1",
        )
    if deterrence_left < maximum_gain:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.BOND_INADEQUATE,
            "expected slash plus future value lost is below maximum defect gain",
        )
    return BondAdequacyAssessmentV1(
        quote_id=terms.quote_id,
        payment_asset_id=terms.payment_asset_id,
        bond_atoms=terms.bond_atoms,
        slash_atoms=terms.slash_atoms,
        detection_probability_bps=terms.detection_probability_bps,
        deterrence_left_scaled_atoms=deterrence_left,
        maximum_defect_gain_scaled_atoms=maximum_gain,
        incentive_margin_scaled_atoms=deterrence_left - maximum_gain,
        incentive_compatible=True,
    )


def _validate_qualification_policy(
    policy: QualificationPolicyV1,
) -> ProcurementRejectV1 | None:
    if type(policy) is not QualificationPolicyV1:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUALIFICATION_POLICY_INVALID,
            "qualification policy must use the closed typed schema",
        )
    if policy.role_id not in CRITICAL_SERVICE_ROLE_IDS:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROLE_UNSUPPORTED,
            "qualification role is unsupported",
        )
    if not _validate_roots(
        (
            policy.service_spec_root,
            policy.benchmark_profile_root,
            policy.execution_subject_root,
            policy.hardware_profile_root,
        )
    ):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROOT_INVALID,
            "qualification policy roots are invalid",
        )
    for field_name, value in (
        ("evaluation_epoch", policy.evaluation_epoch),
        ("minimum_successful_trials", policy.minimum_successful_trials),
        ("maximum_failed_trials", policy.maximum_failed_trials),
        ("maximum_p95_latency_ms", policy.maximum_p95_latency_ms),
        ("minimum_availability_bps", policy.minimum_availability_bps),
        ("maximum_peak_memory_bytes", policy.maximum_peak_memory_bytes),
    ):
        error = _integer_error(value)
        if error is not None:
            return ProcurementRejectV1(error, f"{field_name} must be an exact integer")
    if (
        policy.minimum_successful_trials == 0
        or policy.maximum_p95_latency_ms == 0
        or policy.maximum_peak_memory_bytes == 0
        or policy.minimum_availability_bps > BPS_SCALE
    ):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUALIFICATION_POLICY_INVALID,
            "qualification thresholds must be positive and availability bounded",
        )
    return None


def qualify_service_candidate_v1(
    quote: CompleteServiceQuoteV1,
    observation: QualificationObservationV1,
    bond_terms: BondTermsV1,
    policy: QualificationPolicyV1,
) -> QualificationOutcomeV1:
    policy_error = _validate_qualification_policy(policy)
    if policy_error is not None:
        return policy_error
    if type(observation) is not QualificationObservationV1:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUALIFICATION_OBSERVATION_INVALID,
            "qualification observation must use the closed typed schema",
        )
    quote_assessment = assess_complete_quote_v1(
        quote,
        evaluation_epoch=policy.evaluation_epoch,
    )
    if isinstance(quote_assessment, ProcurementRejectV1):
        return quote_assessment
    if observation.quote_id != quote.quote_id or observation.role_id != quote.role_id:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUOTE_BINDING_MISMATCH,
            "qualification observation binds a different quote or role",
        )
    if policy.role_id != quote.role_id:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.PROFILE_BINDING_MISMATCH,
            "qualification policy binds a different role",
        )
    policy_roots = (
        policy.service_spec_root,
        policy.benchmark_profile_root,
        policy.execution_subject_root,
        policy.hardware_profile_root,
    )
    quote_roots = (
        quote.service_spec_root,
        quote.benchmark_profile_root,
        quote.execution_subject_root,
        quote.hardware_profile_root,
    )
    observation_roots = (
        observation.service_spec_root,
        observation.benchmark_profile_root,
        observation.execution_subject_root,
        observation.hardware_profile_root,
    )
    if policy_roots != quote_roots or observation_roots != quote_roots:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.PROFILE_BINDING_MISMATCH,
            "quote, policy, and observation subjects differ",
        )
    if not _valid_root(observation.evidence_root):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROOT_INVALID,
            "qualification evidence root is invalid",
        )
    observed_values = (
        observation.successful_trials,
        observation.failed_trials,
        observation.invalid_work_accepts,
        observation.replay_or_duplicate_accepts,
        observation.safety_violation_events,
        observation.recovery_failures,
        observation.p95_latency_ms,
        observation.availability_bps,
        observation.peak_memory_bytes,
    )
    for value in observed_values:
        error = _integer_error(value)
        if error is not None:
            return ProcurementRejectV1(
                error,
                "qualification observations must be exact nonnegative integers",
            )
    if observation.availability_bps > BPS_SCALE:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUALIFICATION_OBSERVATION_INVALID,
            "observed availability exceeds 10000 basis points",
        )
    if observation.invalid_work_accepts != 0:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.INVALID_WORK_ACCEPTED,
            "qualification observed an invalid accepted result",
        )
    if observation.replay_or_duplicate_accepts != 0:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.REPLAY_ACCEPTED,
            "qualification observed replay or duplicate acceptance",
        )
    if observation.safety_violation_events != 0:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.SAFETY_VIOLATION,
            "qualification observed a role-specific safety violation",
        )
    if observation.recovery_failures != 0:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.RECOVERY_FAILURE,
            "qualification observed a recovery failure",
        )
    thresholds_met = (
        observation.successful_trials >= policy.minimum_successful_trials
        and observation.failed_trials <= policy.maximum_failed_trials
        and observation.p95_latency_ms <= policy.maximum_p95_latency_ms
        and observation.availability_bps >= policy.minimum_availability_bps
        and observation.peak_memory_bytes <= policy.maximum_peak_memory_bytes
    )
    if not thresholds_met:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.QUALIFICATION_THRESHOLD_MISSED,
            "one or more exact qualification thresholds were missed",
        )
    bond = assess_bond_adequacy_v1(
        bond_terms,
        expected_quote_id=quote.quote_id,
        expected_asset_id=quote.payment_asset_id,
    )
    if isinstance(bond, ProcurementRejectV1):
        return bond
    return QualifiedServiceBidV1(
        quote_id=quote.quote_id,
        role_id=quote.role_id,
        provider_id=quote.provider_id,
        beneficial_owner_id=quote.beneficial_owner_id,
        payment_asset_id=quote.payment_asset_id,
        valid_from_epoch=quote.valid_from_epoch,
        valid_through_epoch=quote.valid_through_epoch,
        service_spec_root=quote.service_spec_root,
        benchmark_profile_root=quote.benchmark_profile_root,
        execution_subject_root=quote.execution_subject_root,
        hardware_profile_root=quote.hardware_profile_root,
        failure_domains=quote.failure_domains,
        quoted_period_cap_atoms=quote_assessment.quoted_period_cap_atoms,
        one_time_onboarding_atoms=quote_assessment.one_time_onboarding_atoms,
        target_prefund_periods=quote_assessment.target_prefund_periods,
        target_prefund_atoms=quote_assessment.target_prefund_atoms,
        bond_atoms=bond.bond_atoms,
        slash_atoms=bond.slash_atoms,
        quote_commitment_root=quote_assessment.quote_commitment_root,
        qualification_evidence_root=observation.evidence_root,
    )


def _validate_procurement_policy(
    policy: ProcurementPolicyV1,
) -> ProcurementRejectV1 | None:
    if type(policy) is not ProcurementPolicyV1:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.POLICY_MISMATCH,
            "procurement policy must use the closed typed schema",
        )
    if policy.role_id not in CRITICAL_SERVICE_ROLE_IDS:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROLE_UNSUPPORTED,
            "procurement role is unsupported",
        )
    if not _valid_identifier(policy.payment_asset_id):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.IDENTIFIER_INVALID,
            "procurement payment asset is invalid",
        )
    if not _validate_roots(
        (
            policy.service_spec_root,
            policy.benchmark_profile_root,
            policy.execution_subject_root,
            policy.hardware_profile_root,
        )
    ):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.ROOT_INVALID,
            "procurement profile roots are invalid",
        )
    for field_name, value in (
        ("selection_epoch", policy.selection_epoch),
        ("required_winners", policy.required_winners),
        ("period_budget_cap_atoms", policy.period_budget_cap_atoms),
        ("onboarding_budget_cap_atoms", policy.onboarding_budget_cap_atoms),
        ("maximum_per_beneficial_owner", policy.maximum_per_beneficial_owner),
        ("maximum_candidate_count", policy.maximum_candidate_count),
    ):
        error = _integer_error(value)
        if error is not None:
            return ProcurementRejectV1(error, f"{field_name} must be an exact integer")
    if (
        policy.required_winners == 0
        or policy.maximum_per_beneficial_owner == 0
        or policy.maximum_candidate_count == 0
        or policy.maximum_candidate_count > MAX_RESEARCH_CANDIDATES
        or policy.required_winners > policy.maximum_candidate_count
    ):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.CANDIDATE_LIMIT_EXCEEDED,
            "winner and candidate bounds are outside the finite research domain",
        )
    if type(policy.failure_domain_caps) is not tuple or not policy.failure_domain_caps:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.FAILURE_DOMAIN_INVALID,
            "procurement requires explicit failure-domain caps",
        )
    kinds: list[str] = []
    for domain_cap in policy.failure_domain_caps:
        if type(domain_cap) is not FailureDomainCapV1 or not _valid_identifier(domain_cap.kind):
            return ProcurementRejectV1(
                ProcurementRejectCodeV1.FAILURE_DOMAIN_INVALID,
                "failure-domain cap is malformed",
            )
        error = _integer_error(domain_cap.maximum_selected_per_value)
        if error is not None or domain_cap.maximum_selected_per_value == 0:
            return ProcurementRejectV1(
                error or ProcurementRejectCodeV1.FAILURE_DOMAIN_INVALID,
                "failure-domain cap must be a positive exact integer",
            )
        kinds.append(domain_cap.kind)
    if kinds != sorted(kinds) or len(kinds) != len(set(kinds)):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.DUPLICATE_FAILURE_DOMAIN_KIND,
            "failure-domain caps must have unique canonical kind order",
        )
    return None


def _qualified_bid_matches_policy(
    bid: QualifiedServiceBidV1,
    policy: ProcurementPolicyV1,
) -> bool:
    if type(bid) is not QualifiedServiceBidV1:
        return False
    if not (
        bid.role_id == policy.role_id
        and bid.payment_asset_id == policy.payment_asset_id
        and bid.service_spec_root == policy.service_spec_root
        and bid.benchmark_profile_root == policy.benchmark_profile_root
        and bid.execution_subject_root == policy.execution_subject_root
        and bid.hardware_profile_root == policy.hardware_profile_root
        and _valid_identifier(bid.quote_id)
        and _valid_identifier(bid.provider_id)
        and _valid_identifier(bid.beneficial_owner_id)
        and _valid_root(bid.quote_commitment_root)
        and _valid_root(bid.qualification_evidence_root)
    ):
        return False
    integer_values = (
        bid.valid_from_epoch,
        bid.valid_through_epoch,
        bid.quoted_period_cap_atoms,
        bid.one_time_onboarding_atoms,
        bid.target_prefund_periods,
        bid.target_prefund_atoms,
        bid.bond_atoms,
        bid.slash_atoms,
    )
    if any(_integer_error(value) is not None for value in integer_values):
        return False
    if not bid.valid_from_epoch <= policy.selection_epoch <= bid.valid_through_epoch:
        return False
    if (
        bid.quoted_period_cap_atoms == 0
        or bid.target_prefund_periods == 0
        or bid.slash_atoms > bid.bond_atoms
    ):
        return False
    if type(bid.failure_domains) is not tuple or not bid.failure_domains:
        return False
    domain_kinds: list[str] = []
    for domain in bid.failure_domains:
        if (
            type(domain) is not FailureDomainV1
            or not _valid_identifier(domain.kind)
            or not _valid_identifier(domain.value)
        ):
            return False
        domain_kinds.append(domain.kind)
    if domain_kinds != sorted(set(domain_kinds)):
        return False
    try:
        expected_prefund = _checked_mul(
            bid.quoted_period_cap_atoms,
            bid.target_prefund_periods,
        )
    except OverflowError:
        return False
    return bid.target_prefund_atoms == expected_prefund


def _combination_feasible(
    selected: tuple[QualifiedServiceBidV1, ...],
    policy: ProcurementPolicyV1,
) -> tuple[int, int, int] | None:
    owner_counts: dict[str, int] = {}
    cap_by_kind = {cap.kind: cap.maximum_selected_per_value for cap in policy.failure_domain_caps}
    domain_counts: dict[tuple[str, str], int] = {}
    expected_domain_kinds = tuple(sorted(cap_by_kind))
    try:
        total_period = 0
        total_onboarding = 0
        total_bond = 0
        for bid in selected:
            total_period = _checked_add(total_period, bid.quoted_period_cap_atoms)
            total_onboarding = _checked_add(
                total_onboarding,
                bid.one_time_onboarding_atoms,
            )
            total_bond = _checked_add(total_bond, bid.bond_atoms)
            owner_counts[bid.beneficial_owner_id] = owner_counts.get(bid.beneficial_owner_id, 0) + 1
            domains = {domain.kind: domain.value for domain in bid.failure_domains}
            if tuple(sorted(domains)) != expected_domain_kinds:
                return None
            for kind, value in domains.items():
                key = (kind, value)
                domain_counts[key] = domain_counts.get(key, 0) + 1
    except OverflowError:
        return None
    if total_period > policy.period_budget_cap_atoms:
        return None
    if total_onboarding > policy.onboarding_budget_cap_atoms:
        return None
    if any(count > policy.maximum_per_beneficial_owner for count in owner_counts.values()):
        return None
    if any(count > cap_by_kind[kind] for (kind, _), count in domain_counts.items()):
        return None
    return total_period, total_onboarding, total_bond


def select_service_bids_v1(
    bids: tuple[QualifiedServiceBidV1, ...],
    policy: ProcurementPolicyV1,
) -> ProcurementOutcomeV1:
    policy_error = _validate_procurement_policy(policy)
    if policy_error is not None:
        return policy_error
    if type(bids) is not tuple:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.POLICY_MISMATCH,
            "qualified bids must be supplied as an immutable tuple",
        )
    if len(bids) > policy.maximum_candidate_count:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.CANDIDATE_LIMIT_EXCEEDED,
            "candidate count exceeds the selected finite bound",
        )
    if any(type(bid) is not QualifiedServiceBidV1 for bid in bids):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.POLICY_MISMATCH,
            "every candidate must use the qualified-bid schema",
        )
    quote_ids = [bid.quote_id for bid in bids]
    if len(quote_ids) != len(set(quote_ids)):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.DUPLICATE_QUOTE,
            "quote identifiers must be unique within one selection",
        )
    if any(not _qualified_bid_matches_policy(bid, policy) for bid in bids):
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.POLICY_MISMATCH,
            "a qualified bid differs from the procurement policy subject",
        )
    if len(bids) < policy.required_winners:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.INSUFFICIENT_QUALIFIED_BIDS,
            "fewer qualified bids exist than required winners",
        )

    ordered = tuple(sorted(bids, key=lambda bid: bid.quote_id))
    best: (
        tuple[
            tuple[int, int, tuple[str, ...]],
            tuple[QualifiedServiceBidV1, ...],
            tuple[int, int, int],
        ]
        | None
    ) = None
    evaluated = 0
    for selected in combinations(ordered, policy.required_winners):
        evaluated += 1
        totals = _combination_feasible(selected, policy)
        if totals is None:
            continue
        quote_id_tuple = tuple(bid.quote_id for bid in selected)
        objective = (totals[0], totals[1], quote_id_tuple)
        if best is None or objective < best[0]:
            best = (objective, selected, totals)
    if best is None:
        return ProcurementRejectV1(
            ProcurementRejectCodeV1.NO_FEASIBLE_SELECTION,
            "no qualified combination satisfies ownership, domain, and budget caps",
        )
    _, selected, totals = best
    return ProcurementSelectionV1(
        role_id=policy.role_id,
        payment_asset_id=policy.payment_asset_id,
        selection_epoch=policy.selection_epoch,
        selected_quote_ids=tuple(bid.quote_id for bid in selected),
        selected_provider_ids=tuple(bid.provider_id for bid in selected),
        total_period_cap_atoms=totals[0],
        total_onboarding_atoms=totals[1],
        total_bond_atoms=totals[2],
        exact_combinations_evaluated=evaluated,
        objective=("MINIMIZE_HIGH_CASE_PERIOD_CAP_THEN_ONBOARDING_THEN_QUOTE_IDS"),
        work_admission_authorized=False,
        payment_authorized=False,
    )
