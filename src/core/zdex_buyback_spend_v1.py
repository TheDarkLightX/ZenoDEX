"""Governed same-occurrence ZDEX buyback reserve-spend core.

Fee allocation is recomputed from the canonical ``ZDEXFeeStateV1``. The only
separate state is cadence; no second reserve balance exists. A release-aware
wrapper must supply an authenticated Spot/Oracle safety limit. This pure module
is unmounted and carries no settlement authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    GlobalEconomicEffectPlanV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    hash_global_v1,
)
from .zdex_fee_allocation_types_v1 import (
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeAllocationRejectedV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeStateV1,
)
from .zdex_fee_allocation_v1 import transition_zdex_fee_allocation_v1

ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1: Final = "zenodex/zdex-buyback-spend-policy/v1"
ZDEX_BUYBACK_SPEND_POLICY_KIND_V1: Final = "zdex_buyback_spend_v1"
ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1: Final = "zenodex/zdex-buyback-spend-state/v1"
ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1: Final = "zenodex/zdex-buyback-spend-context/v1"
ZDEX_BUYBACK_SPEND_INTENT_SCHEMA_V1: Final = "zenodex/zdex-buyback-spend-intent/v1"


class ZDEXBuybackSpendRejectCodeV1(str, Enum):
    POLICY_MISMATCH = "POLICY_MISMATCH"
    SAME_OCCURRENCE_MISMATCH = "SAME_OCCURRENCE_MISMATCH"
    STALE_STATE = "STALE_STATE"
    HEIGHT_REGRESSION = "HEIGHT_REGRESSION"
    COOLDOWN_NOT_ELAPSED = "COOLDOWN_NOT_ELAPSED"
    FEE_INGRESS_MISMATCH = "FEE_INGRESS_MISMATCH"
    FEE_ALLOCATION_REJECTED = "FEE_ALLOCATION_REJECTED"
    VERIFIED_SAFETY_MISMATCH = "VERIFIED_SAFETY_MISMATCH"
    ROUTE_SAFE_LIMIT_ZERO = "ROUTE_SAFE_LIMIT_ZERO"
    SPEND_BELOW_MINIMUM = "SPEND_BELOW_MINIMUM"


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpendPolicyV1:
    quote_asset_id: str
    minimum_quote_spend_atoms: int
    per_command_quote_cap_atoms: int
    minimum_interval_blocks: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.quote_asset_id) is not str:
            raise TypeError("ZDEX buyback spend quote asset must be exact str")
        _require_root(self.quote_asset_id, name="ZDEX buyback spend quote asset")
        _require_atoms_u128(self.minimum_quote_spend_atoms, name="ZDEX buyback minimum")
        _require_atoms_u128(self.per_command_quote_cap_atoms, name="ZDEX buyback cap")
        interval = _require_nonnegative_int(
            self.minimum_interval_blocks,
            name="ZDEX buyback minimum interval blocks",
        )
        if self.minimum_quote_spend_atoms == 0:
            raise ValueError("ZDEX buyback minimum quote spend must be positive")
        if (
            self.per_command_quote_cap_atoms < self.minimum_quote_spend_atoms
            or self.per_command_quote_cap_atoms > MAX_DELTA_ATOMS_V1
        ):
            raise ValueError("ZDEX buyback cap must admit the minimum and fit signed effects")
        if interval == 0:
            raise ValueError("ZDEX buyback minimum interval must be positive")

    @property
    def policy_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-buyback-spend-policy-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1,
            "quote_asset_id": self.quote_asset_id,
            "minimum_quote_spend_atoms": self.minimum_quote_spend_atoms,
            "per_command_quote_cap_atoms": self.per_command_quote_cap_atoms,
            "minimum_interval_blocks": self.minimum_interval_blocks,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpendStateV1:
    """Tokenomics cadence state; the canonical reserve stays in fee state."""

    quote_asset_id: str
    policy_root: str
    last_execution_height: int | None

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for name in ("quote_asset_id", "policy_root"):
            value = getattr(self, name)
            if type(value) is not str:
                raise TypeError(f"ZDEX buyback {name} must be exact str")
            _require_root(value, name=f"ZDEX buyback {name}")
        if self.last_execution_height is not None:
            _require_nonnegative_int(
                self.last_execution_height,
                name="ZDEX buyback last execution height",
            )

    @property
    def state_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-buyback-spend-state-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1,
            "quote_asset_id": self.quote_asset_id,
            "policy_root": self.policy_root,
            "last_execution_height": self.last_execution_height,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpendContextV1:
    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    expected_fee_pre_state_root: str
    expected_cadence_pre_state_root: str
    safety_limit_binding_root: str
    quote_asset_id: str
    current_height: int
    route_safe_quote_limit_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "expected_fee_pre_state_root",
            "expected_cadence_pre_state_root",
            "safety_limit_binding_root",
            "quote_asset_id",
        ):
            value = getattr(self, name)
            if type(value) is not str:
                raise TypeError(f"ZDEX buyback {name} must be exact str")
            _require_root(value, name=f"ZDEX buyback {name}")
        _require_nonnegative_int(self.current_height, name="ZDEX buyback consensus height")
        _require_atoms_u128(
            self.route_safe_quote_limit_atoms,
            name="ZDEX buyback route safe quote limit",
        )
        if self.route_safe_quote_limit_atoms > MAX_DELTA_ATOMS_V1:
            raise ValueError("ZDEX buyback safe limit must fit signed effects")


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpendIntentV1:
    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    spend_policy_root: str
    cadence_pre_state_root: str
    fee_allocation_occurrence_root: str
    fee_pre_state_root: str
    fee_allocated_state_root: str
    safety_limit_binding_root: str
    quote_asset_id: str
    current_height: int
    buyback_reserve_before_atoms: int
    buyback_allocation_atoms: int
    available_buyback_reserve_atoms: int
    quote_spend_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "spend_policy_root",
            "cadence_pre_state_root",
            "fee_allocation_occurrence_root",
            "fee_pre_state_root",
            "fee_allocated_state_root",
            "safety_limit_binding_root",
            "quote_asset_id",
        ):
            value = getattr(self, name)
            if type(value) is not str:
                raise TypeError(f"ZDEX buyback intent {name} must be exact str")
            _require_root(value, name=f"ZDEX buyback intent {name}")
        _require_nonnegative_int(self.current_height, name="ZDEX buyback intent height")
        for name in (
            "buyback_reserve_before_atoms",
            "buyback_allocation_atoms",
            "available_buyback_reserve_atoms",
            "quote_spend_atoms",
        ):
            _require_atoms_u128(getattr(self, name), name=f"ZDEX buyback intent {name}")
        if self.quote_spend_atoms == 0 or self.quote_spend_atoms > MAX_DELTA_ATOMS_V1:
            raise ValueError("ZDEX buyback intent spend must fit positive signed effects")
        if (
            self.buyback_reserve_before_atoms + self.buyback_allocation_atoms
            != self.available_buyback_reserve_atoms
            or self.quote_spend_atoms > self.available_buyback_reserve_atoms
        ):
            raise ValueError("ZDEX buyback intent reserve projection is inconsistent")

    @property
    def intent_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-buyback-spend-intent-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_SPEND_INTENT_SCHEMA_V1,
            "profile_root": self.profile_root,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "spend_policy_root": self.spend_policy_root,
            "cadence_pre_state_root": self.cadence_pre_state_root,
            "fee_allocation_occurrence_root": self.fee_allocation_occurrence_root,
            "fee_pre_state_root": self.fee_pre_state_root,
            "fee_allocated_state_root": self.fee_allocated_state_root,
            "safety_limit_binding_root": self.safety_limit_binding_root,
            "quote_asset_id": self.quote_asset_id,
            "current_height": self.current_height,
            "buyback_reserve_before_atoms": self.buyback_reserve_before_atoms,
            "buyback_allocation_atoms": self.buyback_allocation_atoms,
            "available_buyback_reserve_atoms": self.available_buyback_reserve_atoms,
            "quote_spend_atoms": self.quote_spend_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpendAcceptedV1:
    policy: ZDEXBuybackSpendPolicyV1
    cadence_pre_state: ZDEXBuybackSpendStateV1
    cadence_post_state: ZDEXBuybackSpendStateV1
    fee_policy: ZDEXFeeAllocationPolicyV1
    fee_context: ZDEXFeeAllocationContextV1
    fee_command: ZDEXFeeAllocationCommandV1
    fee_allocation: ZDEXFeeAllocationAcceptedV1
    fee_post_state: ZDEXFeeStateV1
    context: ZDEXBuybackSpendContextV1
    intent: ZDEXBuybackSpendIntentV1

    def __post_init__(self) -> None:
        expected = (
            (self.policy, ZDEXBuybackSpendPolicyV1),
            (self.cadence_pre_state, ZDEXBuybackSpendStateV1),
            (self.cadence_post_state, ZDEXBuybackSpendStateV1),
            (self.fee_policy, ZDEXFeeAllocationPolicyV1),
            (self.fee_context, ZDEXFeeAllocationContextV1),
            (self.fee_command, ZDEXFeeAllocationCommandV1),
            (self.fee_allocation, ZDEXFeeAllocationAcceptedV1),
            (self.fee_post_state, ZDEXFeeStateV1),
            (self.context, ZDEXBuybackSpendContextV1),
            (self.intent, ZDEXBuybackSpendIntentV1),
        )
        if any(type(value) is not kind for value, kind in expected):
            raise TypeError("ZDEX buyback accepted values must be exact typed data")
        allocation = self.fee_allocation
        intent = self.intent
        context = self.context
        recomputed = transition_zdex_fee_allocation_v1(
            self.fee_context,
            allocation.pre_state,
            self.fee_policy,
            self.fee_command,
        )
        before = allocation.pre_state.destination_balances[0].allocation_atoms
        available = allocation.post_state.destination_balances[0].allocation_atoms
        expected_fee_post = _replace_buyback_balance(
            allocation.post_state,
            available - intent.quote_spend_atoms,
        )
        if (
            recomputed != allocation
            or self.fee_command.fee_charged_atoms
            != allocation.pre_state.fee_ingress_atoms
            or intent.spend_policy_root != self.policy.policy_root
            or intent.cadence_pre_state_root != self.cadence_pre_state.state_root
            or intent.fee_allocation_occurrence_root != allocation.occurrence.occurrence_root
            or intent.fee_pre_state_root != allocation.pre_state.state_root
            or intent.fee_allocated_state_root != allocation.post_state.state_root
            or intent.buyback_reserve_before_atoms != before
            or intent.buyback_allocation_atoms != allocation.occurrence.buyback_quote_atoms
            or intent.available_buyback_reserve_atoms != available
            or self.fee_post_state != expected_fee_post
            or self.cadence_post_state
            != replace(self.cadence_pre_state, last_execution_height=intent.current_height)
            or intent.profile_root != context.profile_root
            or intent.route_release_id != context.route_release_id
            or intent.command_occurrence_id != context.command_occurrence_id
            or intent.safety_limit_binding_root != context.safety_limit_binding_root
            or intent.quote_asset_id != context.quote_asset_id
            or intent.current_height != context.current_height
            or intent.quote_spend_atoms
            != min(
                available,
                self.policy.per_command_quote_cap_atoms,
                context.route_safe_quote_limit_atoms,
            )
            or intent.quote_spend_atoms < self.policy.minimum_quote_spend_atoms
        ):
            raise ValueError("ZDEX buyback accepted projection is inconsistent")


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpendRejectedV1:
    code: ZDEXBuybackSpendRejectCodeV1
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None
    cadence_pre_state: ZDEXBuybackSpendStateV1
    cadence_post_state: ZDEXBuybackSpendStateV1
    fee_pre_state: ZDEXFeeStateV1
    fee_post_state: ZDEXFeeStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXBuybackSpendRejectCodeV1:
            raise TypeError("ZDEX buyback reject code must be closed")
        if self.code is ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED:
            if type(self.fee_code) is not ZDEXFeeAllocationRejectCodeV1:
                raise TypeError("ZDEX buyback fee rejection requires a typed fee code")
        elif self.fee_code is not None:
            raise ValueError("ZDEX buyback rejection carries an unexpected fee code")
        if (
            self.cadence_post_state is not self.cadence_pre_state
            or self.fee_post_state is not self.fee_pre_state
            or type(self.effects) is not GlobalEconomicEffectPlanV1
            or not self.effects.is_empty
        ):
            raise ValueError("ZDEX buyback rejection must be an exact no-effect no-op")


ZDEXBuybackSpendResultV1 = ZDEXBuybackSpendAcceptedV1 | ZDEXBuybackSpendRejectedV1


def _reject(
    code: ZDEXBuybackSpendRejectCodeV1,
    cadence: ZDEXBuybackSpendStateV1,
    fee_state: ZDEXFeeStateV1,
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None = None,
) -> ZDEXBuybackSpendRejectedV1:
    return ZDEXBuybackSpendRejectedV1(code, fee_code, cadence, cadence, fee_state, fee_state)


def _replace_buyback_balance(state: ZDEXFeeStateV1, amount: int) -> ZDEXFeeStateV1:
    balances = list(state.destination_balances)
    balances[0] = ZDEXFeeDestinationAmountV1(balances[0].destination, amount)
    return replace(state, destination_balances=tuple(balances))


def _binding_rejection(
    spend_policy: ZDEXBuybackSpendPolicyV1,
    cadence: ZDEXBuybackSpendStateV1,
    fee_pre_state: ZDEXFeeStateV1,
    fee_context: ZDEXFeeAllocationContextV1,
    context: ZDEXBuybackSpendContextV1,
) -> ZDEXBuybackSpendRejectedV1 | None:
    if (
        cadence.policy_root != spend_policy.policy_root
        or cadence.quote_asset_id != spend_policy.quote_asset_id
        or fee_pre_state.fee_asset_id != spend_policy.quote_asset_id
        or context.quote_asset_id != spend_policy.quote_asset_id
    ):
        return _reject(ZDEXBuybackSpendRejectCodeV1.POLICY_MISMATCH, cadence, fee_pre_state)
    if (
        context.expected_fee_pre_state_root != fee_pre_state.state_root
        or context.expected_cadence_pre_state_root != cadence.state_root
    ):
        return _reject(ZDEXBuybackSpendRejectCodeV1.STALE_STATE, cadence, fee_pre_state)
    if (
        fee_context.profile_root != context.profile_root
        or fee_context.allocation_route_release_id != context.route_release_id
        or fee_context.authorized_buyback_route_release_id != context.route_release_id
        or fee_context.command_occurrence_id != context.command_occurrence_id
    ):
        return _reject(
            ZDEXBuybackSpendRejectCodeV1.SAME_OCCURRENCE_MISMATCH, cadence, fee_pre_state
        )
    return None


def _cadence_rejection(
    spend_policy: ZDEXBuybackSpendPolicyV1,
    cadence: ZDEXBuybackSpendStateV1,
    fee_pre_state: ZDEXFeeStateV1,
    context: ZDEXBuybackSpendContextV1,
) -> ZDEXBuybackSpendRejectedV1 | None:
    if cadence.last_execution_height is None:
        return None
    if context.current_height < cadence.last_execution_height:
        return _reject(ZDEXBuybackSpendRejectCodeV1.HEIGHT_REGRESSION, cadence, fee_pre_state)
    if (
        context.current_height - cadence.last_execution_height
        < spend_policy.minimum_interval_blocks
    ):
        return _reject(
            ZDEXBuybackSpendRejectCodeV1.COOLDOWN_NOT_ELAPSED,
            cadence,
            fee_pre_state,
        )
    return None


def transition_zdex_buyback_spend_v1(
    spend_policy: ZDEXBuybackSpendPolicyV1,
    cadence: ZDEXBuybackSpendStateV1,
    fee_policy: ZDEXFeeAllocationPolicyV1,
    fee_pre_state: ZDEXFeeStateV1,
    fee_context: ZDEXFeeAllocationContextV1,
    fee_command: ZDEXFeeAllocationCommandV1,
    context: ZDEXBuybackSpendContextV1,
) -> ZDEXBuybackSpendResultV1:
    """Allocate fees and derive one capped debit from the canonical reserve."""

    expected = (
        (spend_policy, ZDEXBuybackSpendPolicyV1),
        (cadence, ZDEXBuybackSpendStateV1),
        (fee_policy, ZDEXFeeAllocationPolicyV1),
        (fee_pre_state, ZDEXFeeStateV1),
        (fee_context, ZDEXFeeAllocationContextV1),
        (fee_command, ZDEXFeeAllocationCommandV1),
        (context, ZDEXBuybackSpendContextV1),
    )
    if any(type(value) is not kind for value, kind in expected):
        raise TypeError("ZDEX buyback spend transition requires exact typed inputs")
    if rejected := _binding_rejection(spend_policy, cadence, fee_pre_state, fee_context, context):
        return rejected
    if rejected := _cadence_rejection(spend_policy, cadence, fee_pre_state, context):
        return rejected
    if fee_command.fee_charged_atoms != fee_pre_state.fee_ingress_atoms:
        return _reject(
            ZDEXBuybackSpendRejectCodeV1.FEE_INGRESS_MISMATCH,
            cadence,
            fee_pre_state,
        )
    allocation = transition_zdex_fee_allocation_v1(
        fee_context, fee_pre_state, fee_policy, fee_command
    )
    if isinstance(allocation, ZDEXFeeAllocationRejectedV1):
        return _reject(
            ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED,
            cadence,
            fee_pre_state,
            allocation.code,
        )
    if context.route_safe_quote_limit_atoms == 0:
        return _reject(ZDEXBuybackSpendRejectCodeV1.ROUTE_SAFE_LIMIT_ZERO, cadence, fee_pre_state)
    before = allocation.pre_state.destination_balances[0].allocation_atoms
    added = allocation.occurrence.buyback_quote_atoms
    available = allocation.post_state.destination_balances[0].allocation_atoms
    if before + added != available:
        raise ValueError("ZDEX fee allocation buyback projection is inconsistent")
    selected = min(
        available,
        spend_policy.per_command_quote_cap_atoms,
        context.route_safe_quote_limit_atoms,
    )
    if selected < spend_policy.minimum_quote_spend_atoms:
        return _reject(ZDEXBuybackSpendRejectCodeV1.SPEND_BELOW_MINIMUM, cadence, fee_pre_state)
    intent = ZDEXBuybackSpendIntentV1(
        context.profile_root,
        context.route_release_id,
        context.command_occurrence_id,
        spend_policy.policy_root,
        cadence.state_root,
        allocation.occurrence.occurrence_root,
        allocation.pre_state.state_root,
        allocation.post_state.state_root,
        context.safety_limit_binding_root,
        context.quote_asset_id,
        context.current_height,
        before,
        added,
        available,
        selected,
    )
    fee_post = _replace_buyback_balance(allocation.post_state, available - selected)
    cadence_post = replace(cadence, last_execution_height=context.current_height)
    return ZDEXBuybackSpendAcceptedV1(
        spend_policy,
        cadence,
        cadence_post,
        fee_policy,
        fee_context,
        fee_command,
        allocation,
        fee_post,
        context,
        intent,
    )


__all__ = [
    "ZDEXBuybackSpendAcceptedV1",
    "ZDEXBuybackSpendContextV1",
    "ZDEXBuybackSpendIntentV1",
    "ZDEXBuybackSpendPolicyV1",
    "ZDEXBuybackSpendRejectCodeV1",
    "ZDEXBuybackSpendRejectedV1",
    "ZDEXBuybackSpendResultV1",
    "ZDEXBuybackSpendStateV1",
    "ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1",
    "ZDEX_BUYBACK_SPEND_INTENT_SCHEMA_V1",
    "ZDEX_BUYBACK_SPEND_POLICY_KIND_V1",
    "ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1",
    "ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1",
    "transition_zdex_buyback_spend_v1",
]
