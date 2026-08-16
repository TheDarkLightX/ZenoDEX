"""Typed research contract for ZenoDEX participant-service funding.

The contract models purpose-bound service budgets, worst-case runway, payment
caps, exhaustion, and replay.  It grants no work-admission, payment, genesis,
settlement, or release authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import StrEnum
from types import MappingProxyType
from typing import Final, TypeAlias

MAX_ATOMS: Final = 2**256 - 1


class ParticipantFundingBoundaryV1(StrEnum):
    PROPERTY_OR_LIABILITY = "PROPERTY_OR_LIABILITY"
    PROPERTY_WITH_OPTIONAL_REWARD = "PROPERTY_WITH_OPTIONAL_REWARD"
    SERVICE_BUDGET = "SERVICE_BUDGET"
    OPERATIONS_OR_SERVICE_BUDGET = "OPERATIONS_OR_SERVICE_BUDGET"
    SERVICE_OR_DISTRIBUTION_PROGRAM = "SERVICE_OR_DISTRIBUTION_PROGRAM"
    DISTRIBUTION_PROGRAM = "DISTRIBUTION_PROGRAM"
    GENESIS_DISTRIBUTION_PROGRAM = "GENESIS_DISTRIBUTION_PROGRAM"
    RESERVE_AND_EXECUTION = "RESERVE_AND_EXECUTION"


class ServiceCriticalityV1(StrEnum):
    CONSENSUS_CRITICAL = "CONSENSUS_CRITICAL"
    RISK_CRITICAL = "RISK_CRITICAL"
    EXTERNAL_IO_CRITICAL = "EXTERNAL_IO_CRITICAL"
    OPTIONAL_SCALING = "OPTIONAL_SCALING"
    OPTIONAL_GROWTH = "OPTIONAL_GROWTH"
    GOVERNED_OPERATIONS = "GOVERNED_OPERATIONS"


@dataclass(frozen=True, slots=True)
class ParticipantFundingRouteV1:
    boundary: ParticipantFundingBoundaryV1
    service_criticality: ServiceCriticalityV1 | None
    unfunded_behavior: str


_PARTICIPANT_FUNDING_REGISTRY: Final = MappingProxyType(
    {
        "spot_trader_and_order_user": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "PROPERTY_CLAIM_PERSISTS",
        ),
        "liquidity_provider": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "PROPERTY_CLAIM_PERSISTS",
        ),
        "zusd_borrower_and_redeemer": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "PROPERTY_CLAIM_PERSISTS",
        ),
        "stability_pool_depositor": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_WITH_OPTIONAL_REWARD,
            ServiceCriticalityV1.OPTIONAL_GROWTH,
            "PRINCIPAL_AND_GAINS_PERSIST_OPTIONAL_REWARD_STOPS",
        ),
        "liquidator_and_keeper": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.RISK_CRITICAL,
            "AFFECTED_AUTOMATION_OR_RISK_INCREASE_DISABLES",
        ),
        "oracle_reporter_aggregator_disputer_and_watcher": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.RISK_CRITICAL,
            "ORACLE_DEPENDENT_RISK_INCREASE_DISABLES",
        ),
        "perps_trader_and_funding_counterparty": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "PROPERTY_CLAIM_PERSISTS",
        ),
        "insurance_and_bad_debt_backstop": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.RISK_CRITICAL,
            "AFFECTED_RISK_PROFILE_DISABLES",
        ),
        "sealed_bid_seller": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "PROPERTY_CLAIM_PERSISTS",
        ),
        "sealed_bid_bidder_and_private_swap_party": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "PROPERTY_CLAIM_PERSISTS",
        ),
        "tau_depositor_and_withdrawer": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.PROPERTY_OR_LIABILITY,
            None,
            "WITHDRAWAL_REMAINS_PENDING_OR_REFUNDS",
        ),
        "tau_relayer_and_destination_operator": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.EXTERNAL_IO_CRITICAL,
            "TAU_EXTERNAL_IO_REMAINS_PENDING",
        ),
        "proof_prover_and_proof_miner": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.OPTIONAL_SCALING,
            "PROOF_REWARD_STOPS_AND_DIRECT_EXECUTION_CONTINUES",
        ),
        "validator_finality_operator": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.CONSENSUS_CRITICAL,
            "UNFUNDED_VALIDATOR_PERIOD_CANNOT_ACTIVATE",
        ),
        "solver_batcher_and_sequencer": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_BUDGET,
            ServiceCriticalityV1.OPTIONAL_SCALING,
            "PAID_SERVICE_STOPS_OR_SAFE_FALLBACK_EXECUTES",
        ),
        "interface_api_and_static_host": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.OPERATIONS_OR_SERVICE_BUDGET,
            ServiceCriticalityV1.GOVERNED_OPERATIONS,
            "PAID_REFERENCE_SERVICE_STOPS_PERMISSIONLESS_MIRRORS_REMAIN",
        ),
        "security_auditor_and_bounty_researcher": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.OPERATIONS_OR_SERVICE_BUDGET,
            ServiceCriticalityV1.GOVERNED_OPERATIONS,
            "NO_NEW_PAID_WORK_BEYOND_BUDGET",
        ),
        "core_contributor_contractor_and_operations_provider": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.OPERATIONS_OR_SERVICE_BUDGET,
            ServiceCriticalityV1.GOVERNED_OPERATIONS,
            "NO_NEW_PAID_WORK_BEYOND_BUDGET",
        ),
        "liquidity_bootstrapper_and_market_maker": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.SERVICE_OR_DISTRIBUTION_PROGRAM,
            ServiceCriticalityV1.OPTIONAL_GROWTH,
            "LIQUIDITY_SUBSIDY_PROGRAM_STOPS",
        ),
        "community_testnet_and_usage_award_recipient": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.DISTRIBUTION_PROGRAM,
            None,
            "PROGRAM_REMAINS_DISABLED",
        ),
        "founder_team_partner_and_capital_recipient": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.GENESIS_DISTRIBUTION_PROGRAM,
            None,
            "GENESIS_TRANSFER_REMAINS_DISABLED",
        ),
        "protocol_treasury_reserve_and_buyburn_executor": ParticipantFundingRouteV1(
            ParticipantFundingBoundaryV1.RESERVE_AND_EXECUTION,
            None,
            "FUNDS_REMAIN_IN_TYPED_CARRY",
        ),
    }
)


ALL_PARTICIPANT_IDS: Final[frozenset[str]] = frozenset(
    _PARTICIPANT_FUNDING_REGISTRY
)
BUDGET_ELIGIBLE_ROLE_IDS: Final[frozenset[str]] = frozenset(
    role_id
    for role_id, route in _PARTICIPANT_FUNDING_REGISTRY.items()
    if route.service_criticality is not None
)


def participant_funding_registry_v1() -> dict[str, ParticipantFundingRouteV1]:
    return dict(_PARTICIPANT_FUNDING_REGISTRY)


class FundingSourceV1(StrEnum):
    DEPLOYMENT_CAPITAL_PREFUND = "DEPLOYMENT_CAPITAL_PREFUND"
    SELECTED_GENESIS_SERVICE_LOT = "SELECTED_GENESIS_SERVICE_LOT"
    FINALIZED_PROTOCOL_REVENUE_PREFUND = "FINALIZED_PROTOCOL_REVENUE_PREFUND"
    SELECTED_ACTION_FEE = "SELECTED_ACTION_FEE"
    EXPLICIT_EXTERNAL_IO_FEE = "EXPLICIT_EXTERNAL_IO_FEE"
    SIGNED_USER_INTERFACE_FEE = "SIGNED_USER_INTERFACE_FEE"
    USER_GRANTED_EXECUTION_IMPROVEMENT = "USER_GRANTED_EXECUTION_IMPROVEMENT"


_COMMON_FUNDING: Final = frozenset(
    {
        FundingSourceV1.DEPLOYMENT_CAPITAL_PREFUND,
        FundingSourceV1.SELECTED_GENESIS_SERVICE_LOT,
        FundingSourceV1.FINALIZED_PROTOCOL_REVENUE_PREFUND,
    }
)


_ALLOWED_FUNDING_SOURCES: Final = MappingProxyType(
    {
        "stability_pool_depositor": _COMMON_FUNDING,
        "liquidator_and_keeper": _COMMON_FUNDING
        | {FundingSourceV1.SELECTED_ACTION_FEE},
        "oracle_reporter_aggregator_disputer_and_watcher": _COMMON_FUNDING,
        "insurance_and_bad_debt_backstop": _COMMON_FUNDING,
        "tau_relayer_and_destination_operator": _COMMON_FUNDING
        | {FundingSourceV1.EXPLICIT_EXTERNAL_IO_FEE},
        "proof_prover_and_proof_miner": _COMMON_FUNDING,
        "validator_finality_operator": _COMMON_FUNDING,
        "solver_batcher_and_sequencer": _COMMON_FUNDING
        | {FundingSourceV1.USER_GRANTED_EXECUTION_IMPROVEMENT},
        "interface_api_and_static_host": _COMMON_FUNDING
        | {FundingSourceV1.SIGNED_USER_INTERFACE_FEE},
        "security_auditor_and_bounty_researcher": _COMMON_FUNDING,
        "core_contributor_contractor_and_operations_provider": _COMMON_FUNDING,
        "liquidity_bootstrapper_and_market_maker": _COMMON_FUNDING,
    }
)


def allowed_funding_sources_v1() -> dict[str, frozenset[FundingSourceV1]]:
    return dict(_ALLOWED_FUNDING_SOURCES)


SELECTED_ROLE_BUDGETS: Final[dict[str, dict[str, object] | None]] = {
    role_id: None for role_id in sorted(BUDGET_ELIGIBLE_ROLE_IDS)
}


@dataclass(frozen=True, slots=True)
class ServiceBudgetPolicyV1:
    role_id: str
    payment_asset_id: str
    funding_source: FundingSourceV1
    opening_reserve_atoms: int
    fixed_atoms_per_period: int
    maximum_jobs_per_period: int
    maximum_atoms_per_job: int
    period_cap_atoms: int
    target_prefund_periods: int
    period_length_blocks: int
    policy_root: str


class ServiceBudgetRejectCodeV1(StrEnum):
    ROLE_NOT_BUDGET_ELIGIBLE = "ROLE_NOT_BUDGET_ELIGIBLE"
    FUNDING_SOURCE_NOT_ALLOWED = "FUNDING_SOURCE_NOT_ALLOWED"
    INVALID_IDENTIFIER = "INVALID_IDENTIFIER"
    INVALID_AMOUNT = "INVALID_AMOUNT"
    INVALID_PERIOD = "INVALID_PERIOD"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"
    PERIOD_CAP_TOO_SMALL = "PERIOD_CAP_TOO_SMALL"
    CURRENT_PERIOD_NOT_PREFUNDED = "CURRENT_PERIOD_NOT_PREFUNDED"
    TARGET_PREFUND_NOT_MET = "TARGET_PREFUND_NOT_MET"
    INVALID_STATE = "INVALID_STATE"
    POLICY_STATE_MISMATCH = "POLICY_STATE_MISMATCH"
    INVALID_WORK_WITNESS = "INVALID_WORK_WITNESS"
    INVALID_PAYMENT_KIND = "INVALID_PAYMENT_KIND"
    PAYMENT_PERIOD_MISMATCH = "PAYMENT_PERIOD_MISMATCH"
    JOB_ALREADY_PAID = "JOB_ALREADY_PAID"
    FIXED_PAYMENT_ALREADY_MADE = "FIXED_PAYMENT_ALREADY_MADE"
    FIXED_PAYMENT_MISMATCH = "FIXED_PAYMENT_MISMATCH"
    JOB_CAP_EXCEEDED = "JOB_CAP_EXCEEDED"
    JOB_COUNT_EXCEEDED = "JOB_COUNT_EXCEEDED"
    PERIOD_CAP_EXCEEDED = "PERIOD_CAP_EXCEEDED"
    RESERVE_EXHAUSTED = "RESERVE_EXHAUSTED"
    UNPAID_FIXED_OBLIGATION = "UNPAID_FIXED_OBLIGATION"
    NONSEQUENTIAL_PERIOD = "NONSEQUENTIAL_PERIOD"
    NEXT_PERIOD_NOT_PREFUNDED = "NEXT_PERIOD_NOT_PREFUNDED"
    TOPUP_ALREADY_CONSUMED = "TOPUP_ALREADY_CONSUMED"
    TOPUP_OVERFLOW = "TOPUP_OVERFLOW"


@dataclass(frozen=True, slots=True)
class ServiceBudgetRejectV1:
    code: ServiceBudgetRejectCodeV1
    detail: str


@dataclass(frozen=True, slots=True)
class ServiceBudgetAssessmentV1:
    policy: ServiceBudgetPolicyV1
    declared_maximum_period_liability_atoms: int
    required_prefund_atoms: int
    funded_full_periods: int
    prefund_remainder_atoms: int
    prefund_shortfall_atoms: int
    target_met: bool


ServiceBudgetAssessmentOutcomeV1: TypeAlias = (
    ServiceBudgetAssessmentV1 | ServiceBudgetRejectV1
)


def _is_hex_root(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and value == value.lower()
        and all(character in "0123456789abcdef" for character in value)
    )


def _valid_asset_id(value: object) -> bool:
    return (
        isinstance(value, str)
        and 1 <= len(value) <= 32
        and value == value.upper()
        and all(
            character.isascii()
            and (character.isalnum() or character in "._-")
            for character in value
        )
    )


def _valid_actor_id(value: object) -> bool:
    return (
        isinstance(value, str)
        and 1 <= len(value) <= 64
        and value == value.upper()
        and all(
            character.isascii()
            and (character.isalnum() or character in "._-")
            for character in value
        )
    )


def _is_bounded_nonnegative(value: object) -> bool:
    return (
        isinstance(value, int)
        and not isinstance(value, bool)
        and 0 <= value <= MAX_ATOMS
    )


def _checked_add(first: int, second: int) -> int | None:
    result = first + second
    return result if result <= MAX_ATOMS else None


def _checked_mul(first: int, second: int) -> int | None:
    result = first * second
    return result if result <= MAX_ATOMS else None


def assess_service_budget_v1(
    policy: ServiceBudgetPolicyV1,
) -> ServiceBudgetAssessmentOutcomeV1:
    """Assess exact worst-case prefunding in one payment asset."""

    if policy.role_id not in BUDGET_ELIGIBLE_ROLE_IDS:
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.ROLE_NOT_BUDGET_ELIGIBLE,
            "property, distribution, and reserve roles cannot open service budgets",
        )
    if policy.funding_source not in _ALLOWED_FUNDING_SOURCES[policy.role_id]:
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.FUNDING_SOURCE_NOT_ALLOWED,
            "the funding source is not admitted for this role",
        )
    if not _valid_asset_id(policy.payment_asset_id) or not _is_hex_root(
        policy.policy_root
    ):
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.INVALID_IDENTIFIER,
            "payment asset and policy root must be canonical",
        )
    quantities = (
        policy.opening_reserve_atoms,
        policy.fixed_atoms_per_period,
        policy.maximum_jobs_per_period,
        policy.maximum_atoms_per_job,
        policy.period_cap_atoms,
        policy.target_prefund_periods,
        policy.period_length_blocks,
    )
    if any(not _is_bounded_nonnegative(value) for value in quantities):
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.INVALID_AMOUNT,
            "budget quantities must be bounded nonnegative integers",
        )
    if (
        policy.period_cap_atoms == 0
        or policy.target_prefund_periods == 0
        or policy.period_length_blocks == 0
    ):
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.INVALID_PERIOD,
            "enabled budgets require positive cap, target periods, and block length",
        )

    maximum_variable = _checked_mul(
        policy.maximum_jobs_per_period,
        policy.maximum_atoms_per_job,
    )
    if maximum_variable is None:
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.ARITHMETIC_OVERFLOW,
            "maximum variable liability exceeds the atom domain",
        )
    maximum_liability = _checked_add(
        policy.fixed_atoms_per_period,
        maximum_variable,
    )
    required_prefund = _checked_mul(
        policy.period_cap_atoms,
        policy.target_prefund_periods,
    )
    if maximum_liability is None or required_prefund is None:
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.ARITHMETIC_OVERFLOW,
            "period liability or target prefund exceeds the atom domain",
        )
    if maximum_liability > policy.period_cap_atoms:
        return ServiceBudgetRejectV1(
            ServiceBudgetRejectCodeV1.PERIOD_CAP_TOO_SMALL,
            "period cap cannot pay every declared fixed and maximum job liability",
        )

    shortfall = max(0, required_prefund - policy.opening_reserve_atoms)
    return ServiceBudgetAssessmentV1(
        policy=policy,
        declared_maximum_period_liability_atoms=maximum_liability,
        required_prefund_atoms=required_prefund,
        funded_full_periods=(
            policy.opening_reserve_atoms // policy.period_cap_atoms
        ),
        prefund_remainder_atoms=(
            policy.opening_reserve_atoms % policy.period_cap_atoms
        ),
        prefund_shortfall_atoms=shortfall,
        target_met=shortfall == 0,
    )


@dataclass(frozen=True, slots=True)
class ServiceBudgetStateV1:
    role_id: str
    payment_asset_id: str
    remaining_reserve_atoms: int
    period_index: int
    period_spent_atoms: int
    fixed_payment_made: bool
    variable_jobs_paid: int
    paid_job_ids: frozenset[str]
    consumed_topup_ids: frozenset[str]
    policy_root: str


@dataclass(frozen=True, slots=True)
class ServiceBudgetOpenAcceptV1:
    state: ServiceBudgetStateV1
    assessment: ServiceBudgetAssessmentV1


@dataclass(frozen=True, slots=True)
class ServiceBudgetOpenRejectV1:
    code: ServiceBudgetRejectCodeV1
    detail: str


ServiceBudgetOpenOutcomeV1: TypeAlias = (
    ServiceBudgetOpenAcceptV1 | ServiceBudgetOpenRejectV1
)


def open_service_budget_v1(
    policy: ServiceBudgetPolicyV1,
    *,
    initial_period_index: int,
) -> ServiceBudgetOpenOutcomeV1:
    assessment = assess_service_budget_v1(policy)
    if isinstance(assessment, ServiceBudgetRejectV1):
        return ServiceBudgetOpenRejectV1(assessment.code, assessment.detail)
    if not _is_bounded_nonnegative(initial_period_index):
        return ServiceBudgetOpenRejectV1(
            ServiceBudgetRejectCodeV1.INVALID_PERIOD,
            "initial period index must be a bounded nonnegative integer",
        )
    if policy.opening_reserve_atoms < policy.period_cap_atoms:
        return ServiceBudgetOpenRejectV1(
            ServiceBudgetRejectCodeV1.CURRENT_PERIOD_NOT_PREFUNDED,
            "an enabled service period must have its complete cap prefunded",
        )
    if not assessment.target_met:
        return ServiceBudgetOpenRejectV1(
            ServiceBudgetRejectCodeV1.TARGET_PREFUND_NOT_MET,
            "the declared target runway must be purpose-bound before activation",
        )
    return ServiceBudgetOpenAcceptV1(
        state=ServiceBudgetStateV1(
            role_id=policy.role_id,
            payment_asset_id=policy.payment_asset_id,
            remaining_reserve_atoms=policy.opening_reserve_atoms,
            period_index=initial_period_index,
            period_spent_atoms=0,
            fixed_payment_made=False,
            variable_jobs_paid=0,
            paid_job_ids=frozenset(),
            consumed_topup_ids=frozenset(),
            policy_root=policy.policy_root,
        ),
        assessment=assessment,
    )


class ServicePaymentKindV1(StrEnum):
    FIXED_PERIOD = "FIXED_PERIOD"
    VARIABLE_JOB = "VARIABLE_JOB"


@dataclass(frozen=True, slots=True)
class ServicePaymentV1:
    role_id: str
    payment_asset_id: str
    payment_kind: ServicePaymentKindV1
    period_index: int
    job_id: str
    claimant_id: str
    requested_atoms: int
    admitted_work_witness_root: str


@dataclass(frozen=True, slots=True)
class AdvanceServiceBudgetPeriodV1:
    next_period_index: int
    authorization_root: str


@dataclass(frozen=True, slots=True)
class TopUpServiceBudgetV1:
    role_id: str
    payment_asset_id: str
    topup_id: str
    amount_atoms: int
    admitted_source_witness_root: str


ServiceBudgetCommandV1: TypeAlias = (
    ServicePaymentV1 | AdvanceServiceBudgetPeriodV1 | TopUpServiceBudgetV1
)


@dataclass(frozen=True, slots=True)
class ServiceBudgetTransitionAcceptV1:
    state: ServiceBudgetStateV1
    paid_atoms: int
    reserve_increase_atoms: int


@dataclass(frozen=True, slots=True)
class ServiceBudgetTransitionRejectV1:
    code: ServiceBudgetRejectCodeV1
    detail: str
    state: ServiceBudgetStateV1


ServiceBudgetTransitionOutcomeV1: TypeAlias = (
    ServiceBudgetTransitionAcceptV1 | ServiceBudgetTransitionRejectV1
)


def _transition_reject(
    state: ServiceBudgetStateV1,
    code: ServiceBudgetRejectCodeV1,
    detail: str,
) -> ServiceBudgetTransitionRejectV1:
    return ServiceBudgetTransitionRejectV1(code, detail, state)


def _state_matches_policy(
    state: ServiceBudgetStateV1,
    policy: ServiceBudgetPolicyV1,
) -> bool:
    return (
        state.role_id == policy.role_id
        and state.payment_asset_id == policy.payment_asset_id
        and state.policy_root == policy.policy_root
    )


def _state_is_valid(
    state: ServiceBudgetStateV1,
    policy: ServiceBudgetPolicyV1,
) -> bool:
    return (
        _state_matches_policy(state, policy)
        and _is_bounded_nonnegative(state.remaining_reserve_atoms)
        and _is_bounded_nonnegative(state.period_index)
        and _is_bounded_nonnegative(state.period_spent_atoms)
        and state.period_spent_atoms <= policy.period_cap_atoms
        and isinstance(state.fixed_payment_made, bool)
        and _is_bounded_nonnegative(state.variable_jobs_paid)
        and state.variable_jobs_paid <= policy.maximum_jobs_per_period
        and all(_is_hex_root(job_id) for job_id in state.paid_job_ids)
        and all(_is_hex_root(topup_id) for topup_id in state.consumed_topup_ids)
    )


def run_service_budget_transition_v1(
    state: ServiceBudgetStateV1,
    policy: ServiceBudgetPolicyV1,
    command: ServiceBudgetCommandV1,
) -> ServiceBudgetTransitionOutcomeV1:
    """Run one deterministic payment or period-advance transition."""

    assessment = assess_service_budget_v1(policy)
    if isinstance(assessment, ServiceBudgetRejectV1):
        return _transition_reject(state, assessment.code, assessment.detail)
    if not _state_matches_policy(state, policy):
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.POLICY_STATE_MISMATCH,
            "budget state does not belong to this policy",
        )
    if not _state_is_valid(state, policy):
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.INVALID_STATE,
            "budget state violates its cap, count, or identifier invariant",
        )

    if isinstance(command, AdvanceServiceBudgetPeriodV1):
        if not _is_hex_root(command.authorization_root):
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.INVALID_IDENTIFIER,
                "period advance requires a canonical authorization root",
            )
        if not _is_bounded_nonnegative(command.next_period_index):
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.INVALID_PERIOD,
                "next period index must remain inside the bounded integer domain",
            )
        if command.next_period_index != state.period_index + 1:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.NONSEQUENTIAL_PERIOD,
                "budget periods advance exactly one index at a time",
            )
        if policy.fixed_atoms_per_period > 0 and not state.fixed_payment_made:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.UNPAID_FIXED_OBLIGATION,
                "a declared fixed service obligation cannot be silently expired",
            )
        if state.remaining_reserve_atoms < policy.period_cap_atoms:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.NEXT_PERIOD_NOT_PREFUNDED,
                "the next service period lacks its complete prefunded cap",
            )
        return ServiceBudgetTransitionAcceptV1(
            state=replace(
                state,
                period_index=command.next_period_index,
                period_spent_atoms=0,
                fixed_payment_made=False,
                variable_jobs_paid=0,
            ),
            paid_atoms=0,
            reserve_increase_atoms=0,
        )

    if isinstance(command, TopUpServiceBudgetV1):
        if (
            command.role_id != state.role_id
            or command.payment_asset_id != state.payment_asset_id
        ):
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.POLICY_STATE_MISMATCH,
                "top-up role and asset must match the purpose-bound budget",
            )
        if not _is_hex_root(command.topup_id) or not _is_hex_root(
            command.admitted_source_witness_root
        ):
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.INVALID_WORK_WITNESS,
                "top-up id and admitted source witness must be canonical",
            )
        if command.topup_id in state.consumed_topup_ids:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.TOPUP_ALREADY_CONSUMED,
                "the admitted funding source was already consumed",
            )
        if not _is_bounded_nonnegative(command.amount_atoms) or command.amount_atoms == 0:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.INVALID_AMOUNT,
                "top-up must contain positive bounded integer atoms",
            )
        updated_reserve = _checked_add(
            state.remaining_reserve_atoms,
            command.amount_atoms,
        )
        if updated_reserve is None:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.TOPUP_OVERFLOW,
                "top-up would exceed the budget atom domain",
            )
        return ServiceBudgetTransitionAcceptV1(
            state=replace(
                state,
                remaining_reserve_atoms=updated_reserve,
                consumed_topup_ids=state.consumed_topup_ids.union(
                    {command.topup_id}
                ),
            ),
            paid_atoms=0,
            reserve_increase_atoms=command.amount_atoms,
        )

    if (
        command.role_id != state.role_id
        or command.payment_asset_id != state.payment_asset_id
    ):
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.POLICY_STATE_MISMATCH,
            "payment role and asset must match the purpose-bound budget",
        )
    payment_kind_value: object = command.payment_kind
    if not isinstance(payment_kind_value, ServicePaymentKindV1):
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.INVALID_PAYMENT_KIND,
            "payment kind must be a closed service-payment variant",
        )
    if (
        not _is_hex_root(command.job_id)
        or not _valid_actor_id(command.claimant_id)
        or not _is_hex_root(command.admitted_work_witness_root)
    ):
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.INVALID_WORK_WITNESS,
            "job, claimant, and work witness identifiers must be canonical",
        )
    if command.period_index != state.period_index:
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.PAYMENT_PERIOD_MISMATCH,
            "payment evidence must bind the active budget period",
        )
    if command.job_id in state.paid_job_ids:
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.JOB_ALREADY_PAID,
            "the service job nullifier was already consumed",
        )
    if not _is_bounded_nonnegative(command.requested_atoms) or command.requested_atoms == 0:
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.INVALID_AMOUNT,
            "service payments must be positive bounded integer atoms",
        )

    if command.payment_kind is ServicePaymentKindV1.FIXED_PERIOD:
        if state.fixed_payment_made:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.FIXED_PAYMENT_ALREADY_MADE,
                "the fixed period obligation was already paid",
            )
        if command.requested_atoms != policy.fixed_atoms_per_period:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.FIXED_PAYMENT_MISMATCH,
                "fixed payment must equal the declared period liability exactly",
            )
        fixed_payment_made = True
        variable_jobs_paid = state.variable_jobs_paid
    else:
        if command.requested_atoms > policy.maximum_atoms_per_job:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.JOB_CAP_EXCEEDED,
                "variable payment exceeds the selected per-job cap",
            )
        if state.variable_jobs_paid >= policy.maximum_jobs_per_period:
            return _transition_reject(
                state,
                ServiceBudgetRejectCodeV1.JOB_COUNT_EXCEEDED,
                "the selected maximum jobs for this period was reached",
            )
        fixed_payment_made = state.fixed_payment_made
        variable_jobs_paid = state.variable_jobs_paid + 1

    updated_spent = _checked_add(
        state.period_spent_atoms,
        command.requested_atoms,
    )
    if updated_spent is None or updated_spent > policy.period_cap_atoms:
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.PERIOD_CAP_EXCEEDED,
            "payment would exceed the purpose-bound period cap",
        )
    if command.requested_atoms > state.remaining_reserve_atoms:
        return _transition_reject(
            state,
            ServiceBudgetRejectCodeV1.RESERVE_EXHAUSTED,
            "payment would exceed the remaining purpose-bound reserve",
        )
    return ServiceBudgetTransitionAcceptV1(
        state=replace(
            state,
            remaining_reserve_atoms=(
                state.remaining_reserve_atoms - command.requested_atoms
            ),
            period_spent_atoms=updated_spent,
            fixed_payment_made=fixed_payment_made,
            variable_jobs_paid=variable_jobs_paid,
            paid_job_ids=state.paid_job_ids.union({command.job_id}),
        ),
        paid_atoms=command.requested_atoms,
        reserve_increase_atoms=0,
    )


RESEARCH_SOURCE_PATHS: Final[tuple[str, ...]] = (
    "docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json",
    "docs/research/PRODUCTION_READINESS_G1_CLBF_MODEL_V1.json",
)
