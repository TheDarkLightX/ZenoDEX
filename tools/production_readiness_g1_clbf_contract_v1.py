"""Typed research contract for the unselected CLBF mechanism candidate.

This module is an executable accounting model.  It grants no payment, burn,
distribution, settlement, or release authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import StrEnum
from types import MappingProxyType
from typing import Final, TypeAlias

BPS_DENOMINATOR: Final = 10_000
MAX_ATOMS: Final = 2**256 - 1


class LotTypeV1(StrEnum):
    THIRD_PARTY_PROPERTY = "THIRD_PARTY_PROPERTY"
    REFUNDABLE_SERVICE_BOND = "REFUNDABLE_SERVICE_BOND"
    BACKSTOP_RISK_PRINCIPAL = "BACKSTOP_RISK_PRINCIPAL"
    MARKET_MAKER_LIQUIDITY = "MARKET_MAKER_LIQUIDITY"
    UNRESTRICTED_PROTOCOL_REVENUE = "UNRESTRICTED_PROTOCOL_REVENUE"
    REVENUE_CARRY = "REVENUE_CARRY"
    SERVICE_PREFUND = "SERVICE_PREFUND"
    OPERATIONS_PREFUND = "OPERATIONS_PREFUND"
    ADMITTED_SLASH_PROCEEDS = "ADMITTED_SLASH_PROCEEDS"
    CREDIT_RESERVE = "CREDIT_RESERVE"
    BUYBACK_CARRY = "BUYBACK_CARRY"
    GENESIS_LOT = "GENESIS_LOT"


class LotDestinationV1(StrEnum):
    P0_AUTHORIZED_SETTLEMENT = "P0_AUTHORIZED_SETTLEMENT"
    P0_REFUND_OR_WITHDRAWAL = "P0_REFUND_OR_WITHDRAWAL"
    P0_CONTRACTUAL_LOSS = "P0_CONTRACTUAL_LOSS"
    P0_ADMITTED_SLASH_TRANSFORM = "P0_ADMITTED_SLASH_TRANSFORM"
    P0_RESTITUTION = "P0_RESTITUTION"
    P0_CARRY = "P0_CARRY"
    P1_SAFETY_RESERVE = "P1_SAFETY_RESERVE"
    P2_SERVICE_PAYMENT = "P2_SERVICE_PAYMENT"
    P3_OPERATIONS_PAYMENT = "P3_OPERATIONS_PAYMENT"
    G_CREDIT_RESERVE_CREATE = "G_CREDIT_RESERVE_CREATE"
    X_BUYBACK_EXECUTION = "X_BUYBACK_EXECUTION"
    GENESIS_DISTRIBUTION = "GENESIS_DISTRIBUTION"
    CREDIT_REDEMPTION = "CREDIT_REDEMPTION"
    CREDIT_EXPIRY_TO_BUYBACK = "CREDIT_EXPIRY_TO_BUYBACK"
    C_REVENUE_CARRY = "C_REVENUE_CARRY"
    C_SERVICE_CARRY = "C_SERVICE_CARRY"
    C_OPERATIONS_CARRY = "C_OPERATIONS_CARRY"
    C_SLASH_CARRY = "C_SLASH_CARRY"
    C_CREDIT_RESERVE = "C_CREDIT_RESERVE"
    C_BUYBACK_CARRY = "C_BUYBACK_CARRY"
    C_GENESIS_CARRY = "C_GENESIS_CARRY"


_DESTINATION_ORDER: Final = {
    destination: index for index, destination in enumerate(LotDestinationV1)
}


_ALLOWED_DESTINATIONS: Final = MappingProxyType(
    {
        LotTypeV1.THIRD_PARTY_PROPERTY: frozenset(
            {
                LotDestinationV1.P0_AUTHORIZED_SETTLEMENT,
                LotDestinationV1.P0_REFUND_OR_WITHDRAWAL,
                LotDestinationV1.P0_CARRY,
            }
        ),
        LotTypeV1.REFUNDABLE_SERVICE_BOND: frozenset(
            {
                LotDestinationV1.P0_REFUND_OR_WITHDRAWAL,
                LotDestinationV1.P0_ADMITTED_SLASH_TRANSFORM,
                LotDestinationV1.P0_CARRY,
            }
        ),
        LotTypeV1.BACKSTOP_RISK_PRINCIPAL: frozenset(
            {
                LotDestinationV1.P0_REFUND_OR_WITHDRAWAL,
                LotDestinationV1.P0_CONTRACTUAL_LOSS,
                LotDestinationV1.P0_ADMITTED_SLASH_TRANSFORM,
                LotDestinationV1.P0_CARRY,
            }
        ),
        LotTypeV1.MARKET_MAKER_LIQUIDITY: frozenset(
            {
                LotDestinationV1.P0_AUTHORIZED_SETTLEMENT,
                LotDestinationV1.P0_REFUND_OR_WITHDRAWAL,
                LotDestinationV1.P0_CONTRACTUAL_LOSS,
                LotDestinationV1.P0_CARRY,
            }
        ),
        LotTypeV1.UNRESTRICTED_PROTOCOL_REVENUE: frozenset(
            {
                LotDestinationV1.P1_SAFETY_RESERVE,
                LotDestinationV1.P2_SERVICE_PAYMENT,
                LotDestinationV1.P3_OPERATIONS_PAYMENT,
                LotDestinationV1.G_CREDIT_RESERVE_CREATE,
                LotDestinationV1.X_BUYBACK_EXECUTION,
                LotDestinationV1.C_REVENUE_CARRY,
                LotDestinationV1.C_BUYBACK_CARRY,
            }
        ),
        LotTypeV1.REVENUE_CARRY: frozenset(
            {
                LotDestinationV1.P1_SAFETY_RESERVE,
                LotDestinationV1.P2_SERVICE_PAYMENT,
                LotDestinationV1.P3_OPERATIONS_PAYMENT,
                LotDestinationV1.G_CREDIT_RESERVE_CREATE,
                LotDestinationV1.X_BUYBACK_EXECUTION,
                LotDestinationV1.C_REVENUE_CARRY,
                LotDestinationV1.C_BUYBACK_CARRY,
            }
        ),
        LotTypeV1.SERVICE_PREFUND: frozenset(
            {
                LotDestinationV1.P0_REFUND_OR_WITHDRAWAL,
                LotDestinationV1.P2_SERVICE_PAYMENT,
                LotDestinationV1.C_SERVICE_CARRY,
            }
        ),
        LotTypeV1.OPERATIONS_PREFUND: frozenset(
            {
                LotDestinationV1.P0_REFUND_OR_WITHDRAWAL,
                LotDestinationV1.P3_OPERATIONS_PAYMENT,
                LotDestinationV1.C_OPERATIONS_CARRY,
            }
        ),
        LotTypeV1.ADMITTED_SLASH_PROCEEDS: frozenset(
            {
                LotDestinationV1.P0_RESTITUTION,
                LotDestinationV1.P1_SAFETY_RESERVE,
                LotDestinationV1.C_SLASH_CARRY,
            }
        ),
        LotTypeV1.CREDIT_RESERVE: frozenset(
            {
                LotDestinationV1.CREDIT_REDEMPTION,
                LotDestinationV1.CREDIT_EXPIRY_TO_BUYBACK,
                LotDestinationV1.C_CREDIT_RESERVE,
            }
        ),
        LotTypeV1.BUYBACK_CARRY: frozenset(
            {
                LotDestinationV1.X_BUYBACK_EXECUTION,
                LotDestinationV1.C_BUYBACK_CARRY,
            }
        ),
        LotTypeV1.GENESIS_LOT: frozenset(
            {
                LotDestinationV1.GENESIS_DISTRIBUTION,
                LotDestinationV1.C_GENESIS_CARRY,
            }
        ),
    }
)


_SUCCESSOR_TYPE: Final = MappingProxyType(
    {
        LotDestinationV1.P0_ADMITTED_SLASH_TRANSFORM:
            LotTypeV1.ADMITTED_SLASH_PROCEEDS,
        LotDestinationV1.G_CREDIT_RESERVE_CREATE: LotTypeV1.CREDIT_RESERVE,
        LotDestinationV1.CREDIT_EXPIRY_TO_BUYBACK: LotTypeV1.BUYBACK_CARRY,
        LotDestinationV1.C_REVENUE_CARRY: LotTypeV1.REVENUE_CARRY,
        LotDestinationV1.C_SERVICE_CARRY: LotTypeV1.SERVICE_PREFUND,
        LotDestinationV1.C_OPERATIONS_CARRY: LotTypeV1.OPERATIONS_PREFUND,
        LotDestinationV1.C_SLASH_CARRY: LotTypeV1.ADMITTED_SLASH_PROCEEDS,
        LotDestinationV1.C_CREDIT_RESERVE: LotTypeV1.CREDIT_RESERVE,
        LotDestinationV1.C_BUYBACK_CARRY: LotTypeV1.BUYBACK_CARRY,
        LotDestinationV1.C_GENESIS_CARRY: LotTypeV1.GENESIS_LOT,
    }
)


def allowed_destinations_v1() -> dict[LotTypeV1, frozenset[LotDestinationV1]]:
    """Return a detached copy of the closed lot-routing registry."""

    return dict(_ALLOWED_DESTINATIONS)


@dataclass(frozen=True, slots=True)
class SourceLotV1:
    lot_id: str
    asset_id: str
    lot_type: LotTypeV1
    amount_atoms: int
    parent_lot_id: str | None
    source_root: str


@dataclass(frozen=True, slots=True)
class LotAllocationV1:
    destination: LotDestinationV1
    amount_atoms: int
    successor_lot_id: str | None = None


@dataclass(frozen=True, slots=True)
class LotSpendV1:
    source_lot: SourceLotV1
    allocations: tuple[LotAllocationV1, ...]


@dataclass(frozen=True, slots=True)
class LotTransitionV1:
    transition_id: str
    spends: tuple[LotSpendV1, ...]
    successor_lots: tuple[SourceLotV1, ...]
    authorization_root: str


class LotRejectCodeV1(StrEnum):
    INVALID_IDENTIFIER = "INVALID_IDENTIFIER"
    INVALID_AMOUNT = "INVALID_AMOUNT"
    EMPTY_TRANSITION = "EMPTY_TRANSITION"
    DUPLICATE_SOURCE_LOT = "DUPLICATE_SOURCE_LOT"
    LOT_ALREADY_CONSUMED = "LOT_ALREADY_CONSUMED"
    NONCANONICAL_SPEND_ORDER = "NONCANONICAL_SPEND_ORDER"
    NONCANONICAL_ALLOCATION_ORDER = "NONCANONICAL_ALLOCATION_ORDER"
    DUPLICATE_DESTINATION = "DUPLICATE_DESTINATION"
    ALLOCATION_SUM_MISMATCH = "ALLOCATION_SUM_MISMATCH"
    DESTINATION_NOT_ALLOWED = "DESTINATION_NOT_ALLOWED"
    SUCCESSOR_REQUIRED = "SUCCESSOR_REQUIRED"
    UNEXPECTED_SUCCESSOR = "UNEXPECTED_SUCCESSOR"
    SUCCESSOR_NOT_FOUND = "SUCCESSOR_NOT_FOUND"
    SUCCESSOR_TYPE_MISMATCH = "SUCCESSOR_TYPE_MISMATCH"
    SUCCESSOR_ASSET_MISMATCH = "SUCCESSOR_ASSET_MISMATCH"
    SUCCESSOR_AMOUNT_MISMATCH = "SUCCESSOR_AMOUNT_MISMATCH"
    SUCCESSOR_PARENT_MISMATCH = "SUCCESSOR_PARENT_MISMATCH"
    DUPLICATE_SUCCESSOR = "DUPLICATE_SUCCESSOR"
    NONCANONICAL_SUCCESSOR_ORDER = "NONCANONICAL_SUCCESSOR_ORDER"
    ORPHAN_SUCCESSOR = "ORPHAN_SUCCESSOR"


@dataclass(frozen=True, slots=True)
class LotAcceptV1:
    transition: LotTransitionV1
    consumed_lot_ids_after: frozenset[str]


@dataclass(frozen=True, slots=True)
class LotRejectV1:
    code: LotRejectCodeV1
    detail: str
    consumed_lot_ids_after: frozenset[str]


LotOutcomeV1: TypeAlias = LotAcceptV1 | LotRejectV1


def _is_hex_root(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and value == value.lower()
        and all(character in "0123456789abcdef" for character in value)
    )


def _is_atom_amount(value: object, *, allow_zero: bool = False) -> bool:
    lower_bound = 0 if allow_zero else 1
    return (
        isinstance(value, int)
        and not isinstance(value, bool)
        and lower_bound <= value <= MAX_ATOMS
    )


def _valid_asset_id(value: object) -> bool:
    return (
        isinstance(value, str)
        and 1 <= len(value) <= 32
        and value == value.upper()
        and all(character.isascii() and (character.isalnum() or character in "._-") for character in value)
    )


def _lot_reject(
    code: LotRejectCodeV1,
    detail: str,
    consumed_lot_ids: frozenset[str],
) -> LotRejectV1:
    return LotRejectV1(code, detail, consumed_lot_ids)


def validate_lot_transition_v1(
    transition: LotTransitionV1,
    consumed_lot_ids: frozenset[str],
) -> LotOutcomeV1:
    """Validate one immutable, single-use source-lot transition."""

    if not _is_hex_root(transition.transition_id) or not _is_hex_root(
        transition.authorization_root
    ):
        return _lot_reject(
            LotRejectCodeV1.INVALID_IDENTIFIER,
            "transition and authorization roots must be canonical SHA-256 hex",
            consumed_lot_ids,
        )
    if not transition.spends:
        return _lot_reject(
            LotRejectCodeV1.EMPTY_TRANSITION,
            "at least one source lot is required",
            consumed_lot_ids,
        )

    source_ids = tuple(spend.source_lot.lot_id for spend in transition.spends)
    if len(set(source_ids)) != len(source_ids):
        return _lot_reject(
            LotRejectCodeV1.DUPLICATE_SOURCE_LOT,
            "a source lot appears more than once",
            consumed_lot_ids,
        )
    if source_ids != tuple(sorted(source_ids)):
        return _lot_reject(
            LotRejectCodeV1.NONCANONICAL_SPEND_ORDER,
            "source lots must be ordered by lot id",
            consumed_lot_ids,
        )
    if any(source_id in consumed_lot_ids for source_id in source_ids):
        return _lot_reject(
            LotRejectCodeV1.LOT_ALREADY_CONSUMED,
            "a source lot was already consumed",
            consumed_lot_ids,
        )

    successor_ids = tuple(lot.lot_id for lot in transition.successor_lots)
    if len(set(successor_ids)) != len(successor_ids):
        return _lot_reject(
            LotRejectCodeV1.DUPLICATE_SUCCESSOR,
            "successor lot ids must be unique",
            consumed_lot_ids,
        )
    if successor_ids != tuple(sorted(successor_ids)):
        return _lot_reject(
            LotRejectCodeV1.NONCANONICAL_SUCCESSOR_ORDER,
            "successor lots must be ordered by lot id",
            consumed_lot_ids,
        )
    if set(successor_ids) & set(source_ids):
        return _lot_reject(
            LotRejectCodeV1.DUPLICATE_SUCCESSOR,
            "a successor id cannot also be an input id",
            consumed_lot_ids,
        )

    successors: dict[str, SourceLotV1] = {}
    for successor in transition.successor_lots:
        if (
            not _is_hex_root(successor.lot_id)
            or not _is_hex_root(successor.source_root)
            or (
                successor.parent_lot_id is not None
                and not _is_hex_root(successor.parent_lot_id)
            )
            or not _valid_asset_id(successor.asset_id)
        ):
            return _lot_reject(
                LotRejectCodeV1.INVALID_IDENTIFIER,
                "successor identifiers are not canonical",
                consumed_lot_ids,
            )
        if not _is_atom_amount(successor.amount_atoms):
            return _lot_reject(
                LotRejectCodeV1.INVALID_AMOUNT,
                "successor amounts must be positive integer atoms",
                consumed_lot_ids,
            )
        successors[successor.lot_id] = successor

    referenced_successors: set[str] = set()
    for spend in transition.spends:
        source = spend.source_lot
        if (
            not _is_hex_root(source.lot_id)
            or not _is_hex_root(source.source_root)
            or (
                source.parent_lot_id is not None
                and not _is_hex_root(source.parent_lot_id)
            )
            or not _valid_asset_id(source.asset_id)
        ):
            return _lot_reject(
                LotRejectCodeV1.INVALID_IDENTIFIER,
                "source identifiers are not canonical",
                consumed_lot_ids,
            )
        if not _is_atom_amount(source.amount_atoms):
            return _lot_reject(
                LotRejectCodeV1.INVALID_AMOUNT,
                "source amounts must be positive integer atoms",
                consumed_lot_ids,
            )
        if not spend.allocations:
            return _lot_reject(
                LotRejectCodeV1.ALLOCATION_SUM_MISMATCH,
                "a source lot must be allocated completely",
                consumed_lot_ids,
            )
        if any(not _is_atom_amount(item.amount_atoms) for item in spend.allocations):
            return _lot_reject(
                LotRejectCodeV1.INVALID_AMOUNT,
                "allocation amounts must be positive integer atoms",
                consumed_lot_ids,
            )
        if sum(item.amount_atoms for item in spend.allocations) != source.amount_atoms:
            return _lot_reject(
                LotRejectCodeV1.ALLOCATION_SUM_MISMATCH,
                "allocation atoms must equal source atoms exactly",
                consumed_lot_ids,
            )

        observed_order = tuple(
            _DESTINATION_ORDER[item.destination] for item in spend.allocations
        )
        if observed_order != tuple(sorted(observed_order)):
            return _lot_reject(
                LotRejectCodeV1.NONCANONICAL_ALLOCATION_ORDER,
                "allocations must follow the closed destination order",
                consumed_lot_ids,
            )
        destinations = tuple(item.destination for item in spend.allocations)
        if len(set(destinations)) != len(destinations):
            return _lot_reject(
                LotRejectCodeV1.DUPLICATE_DESTINATION,
                "one source lot may name each destination at most once",
                consumed_lot_ids,
            )

        allowed = _ALLOWED_DESTINATIONS[source.lot_type]
        for allocation in spend.allocations:
            if allocation.destination not in allowed:
                return _lot_reject(
                    LotRejectCodeV1.DESTINATION_NOT_ALLOWED,
                    f"{source.lot_type.value} cannot route to "
                    f"{allocation.destination.value}",
                    consumed_lot_ids,
                )
            expected_type = _SUCCESSOR_TYPE.get(allocation.destination)
            if allocation.destination is LotDestinationV1.P0_CARRY:
                expected_type = source.lot_type
            if expected_type is None:
                if allocation.successor_lot_id is not None:
                    return _lot_reject(
                        LotRejectCodeV1.UNEXPECTED_SUCCESSOR,
                        "terminal destinations cannot name a successor",
                        consumed_lot_ids,
                    )
                continue
            if allocation.successor_lot_id is None:
                return _lot_reject(
                    LotRejectCodeV1.SUCCESSOR_REQUIRED,
                    "carry and transformation destinations require a successor",
                    consumed_lot_ids,
                )
            resolved_successor = successors.get(allocation.successor_lot_id)
            if resolved_successor is None:
                return _lot_reject(
                    LotRejectCodeV1.SUCCESSOR_NOT_FOUND,
                    "the referenced successor was not supplied",
                    consumed_lot_ids,
                )
            referenced_successors.add(resolved_successor.lot_id)
            if resolved_successor.lot_type is not expected_type:
                return _lot_reject(
                    LotRejectCodeV1.SUCCESSOR_TYPE_MISMATCH,
                    "the successor lot type does not match its destination",
                    consumed_lot_ids,
                )
            if resolved_successor.asset_id != source.asset_id:
                return _lot_reject(
                    LotRejectCodeV1.SUCCESSOR_ASSET_MISMATCH,
                    "a successor cannot silently change assets",
                    consumed_lot_ids,
                )
            if resolved_successor.amount_atoms != allocation.amount_atoms:
                return _lot_reject(
                    LotRejectCodeV1.SUCCESSOR_AMOUNT_MISMATCH,
                    "successor atoms must equal allocated atoms",
                    consumed_lot_ids,
                )
            if resolved_successor.parent_lot_id != source.lot_id:
                return _lot_reject(
                    LotRejectCodeV1.SUCCESSOR_PARENT_MISMATCH,
                    "the successor must bind its exact source lot",
                    consumed_lot_ids,
                )

    if referenced_successors != set(successors):
        return _lot_reject(
            LotRejectCodeV1.ORPHAN_SUCCESSOR,
            "every successor must be referenced exactly once",
            consumed_lot_ids,
        )
    return LotAcceptV1(
        transition,
        consumed_lot_ids.union(source_ids),
    )


@dataclass(frozen=True, slots=True)
class RevenueWaterfallV1:
    asset_id: str
    finalized_unrestricted_revenue_atoms: int
    p1_safety_shortfall_atoms: int
    p2_service_shortfall_atoms: int
    p3_operations_shortfall_atoms: int
    requested_growth_reserve_atoms: int
    selected_growth_reserve_bps: int
    requested_buyback_atoms: int
    requested_buyback_carry_atoms: int
    obligation_snapshot_root: str
    revenue_source_root: str


@dataclass(frozen=True, slots=True)
class RevenueWaterfallAllocationV1:
    p1_safety_atoms: int
    p2_service_atoms: int
    p3_operations_atoms: int
    growth_reserve_atoms: int
    buyback_atoms: int
    buyback_carry_atoms: int
    pre_growth_surplus_atoms: int
    eligible_surplus_atoms: int


class RevenueWaterfallRejectCodeV1(StrEnum):
    INVALID_IDENTIFIER = "INVALID_IDENTIFIER"
    INVALID_AMOUNT = "INVALID_AMOUNT"
    GROWTH_BPS_OUT_OF_RANGE = "GROWTH_BPS_OUT_OF_RANGE"
    REQUIRED_FUNDING_EXCEEDS_REVENUE = "REQUIRED_FUNDING_EXCEEDS_REVENUE"
    GROWTH_RESERVE_CAP_EXCEEDED = "GROWTH_RESERVE_CAP_EXCEEDED"
    SURPLUS_ALLOCATION_MISMATCH = "SURPLUS_ALLOCATION_MISMATCH"


@dataclass(frozen=True, slots=True)
class RevenueWaterfallAcceptV1:
    allocation: RevenueWaterfallAllocationV1


@dataclass(frozen=True, slots=True)
class RevenueWaterfallRejectV1:
    code: RevenueWaterfallRejectCodeV1
    detail: str


RevenueWaterfallOutcomeV1: TypeAlias = (
    RevenueWaterfallAcceptV1 | RevenueWaterfallRejectV1
)


def validate_revenue_waterfall_v1(
    candidate: RevenueWaterfallV1,
) -> RevenueWaterfallOutcomeV1:
    """Allocate one asset's revenue only after all declared shortfalls."""

    if (
        not _valid_asset_id(candidate.asset_id)
        or not _is_hex_root(candidate.obligation_snapshot_root)
        or not _is_hex_root(candidate.revenue_source_root)
    ):
        return RevenueWaterfallRejectV1(
            RevenueWaterfallRejectCodeV1.INVALID_IDENTIFIER,
            "asset, obligation, and revenue identifiers must be canonical",
        )
    quantities = (
        candidate.finalized_unrestricted_revenue_atoms,
        candidate.p1_safety_shortfall_atoms,
        candidate.p2_service_shortfall_atoms,
        candidate.p3_operations_shortfall_atoms,
        candidate.requested_growth_reserve_atoms,
        candidate.requested_buyback_atoms,
        candidate.requested_buyback_carry_atoms,
    )
    if any(not _is_atom_amount(value, allow_zero=True) for value in quantities):
        return RevenueWaterfallRejectV1(
            RevenueWaterfallRejectCodeV1.INVALID_AMOUNT,
            "waterfall quantities must be nonnegative integer atoms",
        )
    if not 0 <= candidate.selected_growth_reserve_bps < BPS_DENOMINATOR:
        return RevenueWaterfallRejectV1(
            RevenueWaterfallRejectCodeV1.GROWTH_BPS_OUT_OF_RANGE,
            "growth reserve basis points must be below the complete surplus",
        )

    required_funding = (
        candidate.p1_safety_shortfall_atoms
        + candidate.p2_service_shortfall_atoms
        + candidate.p3_operations_shortfall_atoms
    )
    revenue = candidate.finalized_unrestricted_revenue_atoms
    if required_funding > revenue:
        return RevenueWaterfallRejectV1(
            RevenueWaterfallRejectCodeV1.REQUIRED_FUNDING_EXCEEDS_REVENUE,
            "safety, service, and operations shortfalls consume all available revenue",
        )
    pre_growth_surplus = revenue - required_funding
    maximum_growth_reserve = (
        pre_growth_surplus
        * candidate.selected_growth_reserve_bps
        // BPS_DENOMINATOR
    )
    if candidate.requested_growth_reserve_atoms > maximum_growth_reserve:
        return RevenueWaterfallRejectV1(
            RevenueWaterfallRejectCodeV1.GROWTH_RESERVE_CAP_EXCEEDED,
            "growth reserve exceeds its selected share of pre-growth surplus",
        )
    eligible_surplus = pre_growth_surplus - candidate.requested_growth_reserve_atoms
    if (
        candidate.requested_buyback_atoms
        + candidate.requested_buyback_carry_atoms
        != eligible_surplus
    ):
        return RevenueWaterfallRejectV1(
            RevenueWaterfallRejectCodeV1.SURPLUS_ALLOCATION_MISMATCH,
            "eligible surplus must route exactly to buyback or buyback carry",
        )
    return RevenueWaterfallAcceptV1(
        RevenueWaterfallAllocationV1(
            p1_safety_atoms=candidate.p1_safety_shortfall_atoms,
            p2_service_atoms=candidate.p2_service_shortfall_atoms,
            p3_operations_atoms=candidate.p3_operations_shortfall_atoms,
            growth_reserve_atoms=candidate.requested_growth_reserve_atoms,
            buyback_atoms=candidate.requested_buyback_atoms,
            buyback_carry_atoms=candidate.requested_buyback_carry_atoms,
            pre_growth_surplus_atoms=pre_growth_surplus,
            eligible_surplus_atoms=eligible_surplus,
        )
    )


class CreditStatusV1(StrEnum):
    EMPTY = "EMPTY"
    PENDING = "PENDING"
    MATURED = "MATURED"
    REDEEMED = "REDEEMED"
    CANCELED = "CANCELED"
    EXPIRED = "EXPIRED"


@dataclass(frozen=True, slots=True)
class CreditStateV1:
    asset_id: str
    status: CreditStatusV1
    reserve_atoms: int
    pending_credit_atoms: int
    matured_credit_atoms: int
    buyback_carry_atoms: int
    earned_epoch: int | None
    maturity_epoch: int | None
    expiry_epoch: int | None
    cumulative_external_cash_fee_atoms: int
    cumulative_reserve_release_atoms: int
    cumulative_fee_settlement_atoms: int


@dataclass(frozen=True, slots=True)
class CreditEffectV1:
    external_cash_fee_atoms: int = 0
    reserve_release_atoms: int = 0
    fee_settlement_atoms: int = 0
    new_credit_atoms: int = 0
    buyback_carry_increase_atoms: int = 0


@dataclass(frozen=True, slots=True)
class EarnCreditV1:
    cash_fee_atoms: int
    requested_credit_atoms: int
    earn_bps: int
    available_growth_reserve_atoms: int
    earned_epoch: int
    maturity_epoch: int
    expiry_epoch: int
    continuous_lock_witness_root: str


@dataclass(frozen=True, slots=True)
class MatureCreditV1:
    current_epoch: int
    continuous_lock_witness_root: str


@dataclass(frozen=True, slots=True)
class RedeemCreditV1:
    gross_fee_atoms: int
    requested_credit_atoms: int
    redemption_bps: int
    current_epoch: int


@dataclass(frozen=True, slots=True)
class EarlyUnlockCreditV1:
    current_epoch: int


@dataclass(frozen=True, slots=True)
class ExpireCreditV1:
    current_epoch: int


CreditCommandV1: TypeAlias = (
    EarnCreditV1
    | MatureCreditV1
    | RedeemCreditV1
    | EarlyUnlockCreditV1
    | ExpireCreditV1
)


class CreditRejectCodeV1(StrEnum):
    INVALID_STATE = "INVALID_STATE"
    INVALID_PHASE = "INVALID_PHASE"
    INVALID_AMOUNT = "INVALID_AMOUNT"
    INVALID_EPOCH = "INVALID_EPOCH"
    INVALID_LOCK_WITNESS = "INVALID_LOCK_WITNESS"
    EARN_BPS_OUT_OF_RANGE = "EARN_BPS_OUT_OF_RANGE"
    EARN_CAP_EXCEEDED = "EARN_CAP_EXCEEDED"
    GROWTH_RESERVE_EXCEEDED = "GROWTH_RESERVE_EXCEEDED"
    REDEMPTION_BPS_OUT_OF_RANGE = "REDEMPTION_BPS_OUT_OF_RANGE"
    REDEMPTION_CAP_EXCEEDED = "REDEMPTION_CAP_EXCEEDED"
    CREDIT_BALANCE_EXCEEDED = "CREDIT_BALANCE_EXCEEDED"
    NOT_MATURE = "NOT_MATURE"
    ALREADY_EXPIRED = "ALREADY_EXPIRED"
    NOT_EXPIRED = "NOT_EXPIRED"


@dataclass(frozen=True, slots=True)
class CreditAcceptV1:
    state: CreditStateV1
    effect: CreditEffectV1


@dataclass(frozen=True, slots=True)
class CreditRejectV1:
    code: CreditRejectCodeV1
    detail: str
    state: CreditStateV1


CreditOutcomeV1: TypeAlias = CreditAcceptV1 | CreditRejectV1


def empty_credit_state_v1(asset_id: str) -> CreditStateV1:
    if not _valid_asset_id(asset_id):
        raise ValueError("asset_id must be a canonical uppercase identifier")
    return CreditStateV1(
        asset_id=asset_id,
        status=CreditStatusV1.EMPTY,
        reserve_atoms=0,
        pending_credit_atoms=0,
        matured_credit_atoms=0,
        buyback_carry_atoms=0,
        earned_epoch=None,
        maturity_epoch=None,
        expiry_epoch=None,
        cumulative_external_cash_fee_atoms=0,
        cumulative_reserve_release_atoms=0,
        cumulative_fee_settlement_atoms=0,
    )


def _credit_reject(
    state: CreditStateV1,
    code: CreditRejectCodeV1,
    detail: str,
) -> CreditRejectV1:
    return CreditRejectV1(code, detail, state)


def _credit_state_is_valid(state: CreditStateV1) -> bool:
    quantities = (
        state.reserve_atoms,
        state.pending_credit_atoms,
        state.matured_credit_atoms,
        state.buyback_carry_atoms,
        state.cumulative_external_cash_fee_atoms,
        state.cumulative_reserve_release_atoms,
        state.cumulative_fee_settlement_atoms,
    )
    return (
        _valid_asset_id(state.asset_id)
        and all(_is_atom_amount(value, allow_zero=True) for value in quantities)
        and state.reserve_atoms
        == state.pending_credit_atoms + state.matured_credit_atoms
    )


def _bounded_sum(*values: int) -> int | None:
    total = sum(values)
    return total if _is_atom_amount(total, allow_zero=True) else None


def run_credit_transition_v1(
    state: CreditStateV1,
    command: CreditCommandV1,
) -> CreditOutcomeV1:
    """Run one total, phase-specific, reject-is-no-op credit transition."""

    if not _credit_state_is_valid(state):
        return _credit_reject(
            state,
            CreditRejectCodeV1.INVALID_STATE,
            "credit reserve must equal pending plus matured credit",
        )

    if isinstance(command, EarnCreditV1):
        if state.status is not CreditStatusV1.EMPTY:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_PHASE,
                "credit may be earned only from an empty cohort",
            )
        if not (0 <= command.earn_bps < BPS_DENOMINATOR):
            return _credit_reject(
                state,
                CreditRejectCodeV1.EARN_BPS_OUT_OF_RANGE,
                "earn basis points must be below the complete fee",
            )
        if (
            not _is_atom_amount(command.cash_fee_atoms, allow_zero=True)
            or not _is_atom_amount(command.requested_credit_atoms)
            or not _is_atom_amount(
                command.available_growth_reserve_atoms, allow_zero=True
            )
        ):
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_AMOUNT,
                "fees and reserves use nonnegative integer atoms; credit is positive",
            )
        if not (
            0 <= command.earned_epoch
            < command.maturity_epoch
            < command.expiry_epoch
        ):
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_EPOCH,
                "credit epochs must be strictly ordered",
            )
        if not _is_hex_root(command.continuous_lock_witness_root):
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_LOCK_WITNESS,
                "earning requires a canonical lock witness root",
            )
        earned_cap = command.cash_fee_atoms * command.earn_bps // BPS_DENOMINATOR
        if command.requested_credit_atoms > earned_cap:
            return _credit_reject(
                state,
                CreditRejectCodeV1.EARN_CAP_EXCEEDED,
                "new credit exceeds the irreversible cash-fee cap",
            )
        if command.requested_credit_atoms > command.available_growth_reserve_atoms:
            return _credit_reject(
                state,
                CreditRejectCodeV1.GROWTH_RESERVE_EXCEEDED,
                "new credit exceeds its named prefunded reserve",
            )
        cumulative_external = _bounded_sum(
            state.cumulative_external_cash_fee_atoms,
            command.cash_fee_atoms,
        )
        cumulative_settlement = _bounded_sum(
            state.cumulative_fee_settlement_atoms,
            command.cash_fee_atoms,
        )
        if cumulative_external is None or cumulative_settlement is None:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_AMOUNT,
                "credit accounting cumulative totals exceed the atom bound",
            )
        new_state = replace(
            state,
            status=CreditStatusV1.PENDING,
            reserve_atoms=command.requested_credit_atoms,
            pending_credit_atoms=command.requested_credit_atoms,
            earned_epoch=command.earned_epoch,
            maturity_epoch=command.maturity_epoch,
            expiry_epoch=command.expiry_epoch,
            cumulative_external_cash_fee_atoms=cumulative_external,
            cumulative_fee_settlement_atoms=cumulative_settlement,
        )
        return CreditAcceptV1(
            new_state,
            CreditEffectV1(
                external_cash_fee_atoms=command.cash_fee_atoms,
                fee_settlement_atoms=command.cash_fee_atoms,
                new_credit_atoms=command.requested_credit_atoms,
            ),
        )

    if isinstance(command, MatureCreditV1):
        if state.status is not CreditStatusV1.PENDING:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_PHASE,
                "only pending credit can mature",
            )
        if not _is_hex_root(command.continuous_lock_witness_root):
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_LOCK_WITNESS,
                "maturity requires a canonical continuous-lock witness",
            )
        if state.maturity_epoch is None or command.current_epoch < state.maturity_epoch:
            return _credit_reject(
                state,
                CreditRejectCodeV1.NOT_MATURE,
                "the maturity epoch has not been reached",
            )
        if state.expiry_epoch is None or command.current_epoch >= state.expiry_epoch:
            return _credit_reject(
                state,
                CreditRejectCodeV1.ALREADY_EXPIRED,
                "expired credit cannot mature",
            )
        return CreditAcceptV1(
            replace(
                state,
                status=CreditStatusV1.MATURED,
                pending_credit_atoms=0,
                matured_credit_atoms=state.pending_credit_atoms,
            ),
            CreditEffectV1(),
        )

    if isinstance(command, RedeemCreditV1):
        if state.status is not CreditStatusV1.MATURED:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_PHASE,
                "only matured credit can be redeemed",
            )
        if not (0 <= command.redemption_bps < BPS_DENOMINATOR):
            return _credit_reject(
                state,
                CreditRejectCodeV1.REDEMPTION_BPS_OUT_OF_RANGE,
                "redemption basis points must be below the complete fee",
            )
        if (
            not _is_atom_amount(command.gross_fee_atoms, allow_zero=True)
            or not _is_atom_amount(command.requested_credit_atoms)
        ):
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_AMOUNT,
                "gross fee is nonnegative and redeemed credit is positive",
            )
        if state.expiry_epoch is None or command.current_epoch >= state.expiry_epoch:
            return _credit_reject(
                state,
                CreditRejectCodeV1.ALREADY_EXPIRED,
                "expired credit cannot be redeemed",
            )
        redemption_cap = (
            command.gross_fee_atoms * command.redemption_bps // BPS_DENOMINATOR
        )
        if command.requested_credit_atoms > redemption_cap:
            return _credit_reject(
                state,
                CreditRejectCodeV1.REDEMPTION_CAP_EXCEEDED,
                "requested credit exceeds the current gross-fee cap",
            )
        if command.requested_credit_atoms > state.matured_credit_atoms:
            return _credit_reject(
                state,
                CreditRejectCodeV1.CREDIT_BALANCE_EXCEEDED,
                "requested credit exceeds the matured reserve",
            )
        remaining = state.matured_credit_atoms - command.requested_credit_atoms
        external_cash = command.gross_fee_atoms - command.requested_credit_atoms
        cumulative_external = _bounded_sum(
            state.cumulative_external_cash_fee_atoms,
            external_cash,
        )
        cumulative_release = _bounded_sum(
            state.cumulative_reserve_release_atoms,
            command.requested_credit_atoms,
        )
        cumulative_settlement = _bounded_sum(
            state.cumulative_fee_settlement_atoms,
            command.gross_fee_atoms,
        )
        if (
            cumulative_external is None
            or cumulative_release is None
            or cumulative_settlement is None
        ):
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_AMOUNT,
                "credit accounting cumulative totals exceed the atom bound",
            )
        return CreditAcceptV1(
            replace(
                state,
                status=(
                    CreditStatusV1.REDEEMED
                    if remaining == 0
                    else CreditStatusV1.MATURED
                ),
                reserve_atoms=remaining,
                matured_credit_atoms=remaining,
                cumulative_external_cash_fee_atoms=cumulative_external,
                cumulative_reserve_release_atoms=cumulative_release,
                cumulative_fee_settlement_atoms=cumulative_settlement,
            ),
            CreditEffectV1(
                external_cash_fee_atoms=external_cash,
                reserve_release_atoms=command.requested_credit_atoms,
                fee_settlement_atoms=command.gross_fee_atoms,
            ),
        )

    if isinstance(command, EarlyUnlockCreditV1):
        if state.status is not CreditStatusV1.PENDING:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_PHASE,
                "early unlock applies only to pending credit",
            )
        if state.maturity_epoch is None or command.current_epoch >= state.maturity_epoch:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_EPOCH,
                "unlock at or after maturity is not an early unlock",
            )
        released = state.reserve_atoms
        updated_carry = _bounded_sum(state.buyback_carry_atoms, released)
        if updated_carry is None:
            return _credit_reject(
                state,
                CreditRejectCodeV1.INVALID_AMOUNT,
                "buyback carry exceeds the atom bound",
            )
        return CreditAcceptV1(
            replace(
                state,
                status=CreditStatusV1.CANCELED,
                reserve_atoms=0,
                pending_credit_atoms=0,
                matured_credit_atoms=0,
                buyback_carry_atoms=updated_carry,
            ),
            CreditEffectV1(buyback_carry_increase_atoms=released),
        )

    if state.status not in {CreditStatusV1.PENDING, CreditStatusV1.MATURED}:
        return _credit_reject(
            state,
            CreditRejectCodeV1.INVALID_PHASE,
            "only outstanding credit can expire",
        )
    if state.expiry_epoch is None or command.current_epoch < state.expiry_epoch:
        return _credit_reject(
            state,
            CreditRejectCodeV1.NOT_EXPIRED,
            "the expiry epoch has not been reached",
        )
    released = state.reserve_atoms
    updated_carry = _bounded_sum(state.buyback_carry_atoms, released)
    if updated_carry is None:
        return _credit_reject(
            state,
            CreditRejectCodeV1.INVALID_AMOUNT,
            "buyback carry exceeds the atom bound",
        )
    return CreditAcceptV1(
        replace(
            state,
            status=CreditStatusV1.EXPIRED,
            reserve_atoms=0,
            pending_credit_atoms=0,
            matured_credit_atoms=0,
            buyback_carry_atoms=updated_carry,
        ),
        CreditEffectV1(buyback_carry_increase_atoms=released),
    )


SELECTED_CLBF_PARAMETERS: Final[dict[str, int | None]] = {
    "growth_reserve_bps": None,
    "earn_bps": None,
    "redemption_bps": None,
    "event_benefit_bps": None,
    "maturity_epochs": None,
    "expiry_epochs": None,
    "lock_epochs": None,
    "lock_value_multiple_bps": None,
    "aggregate_liability_bps": None,
}


RESEARCH_SOURCE_PATHS: Final[tuple[str, ...]] = (
    "docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json",
    "docs/research/ZDEX_VOLUME_HOLDING_HYPERDEFLATION_MECHANISM_REPORT_V1.md",
)
