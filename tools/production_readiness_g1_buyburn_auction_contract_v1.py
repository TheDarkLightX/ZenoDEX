"""Research contract for a competitive ZDEX burn-to-claim auction.

Eligible surplus is offered as a source-bound lot.  Bidders reveal fully
escrowed ZDEX burn bids, and the largest reserve-clearing bid becomes a
settlement candidate.  The protocol never places a market buy or takes custody
of acquired ZDEX in this model.  All witnesses are caller-constructible Python
values, so this module grants no burn, transfer, settlement, profile, or release
authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, replace
from enum import StrEnum
from typing import Final, TypeAlias

MAX_ATOMS: Final = 2**256 - 1
BPS_SCALE: Final = 10_000
MAX_RESEARCH_BIDS: Final = 32

ZDEX_WHOLE_TOKEN_SUPPLY: Final = 2_000_000_000
ZDEX_UNIT_SCALE: Final = 10**18
ZDEX_GENESIS_SUPPLY_ATOMS: Final = ZDEX_WHOLE_TOKEN_SUPPLY * ZDEX_UNIT_SCALE
ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS: Final = 200_000_000 * ZDEX_UNIT_SCALE
ZDEX_ABSOLUTE_FLOOR_ATOMS: Final = 1

RESEARCH_SOURCE_PATHS: Final = (
    "docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json",
    "docs/research/PRODUCTION_READINESS_G1_CLBF_MODEL_V1.json",
    "tools/production_readiness_g1_clbf_contract_v1.py",
    "docs/research/PRODUCTION_READINESS_G1_PROFILE_INPUTS_V1.json",
    "src/core/m6_safe_mount_transition_v1.py",
)

SELECTED_BUYBURN_ROUTE_V1: Final[dict[str, object] | None] = None
ACTIVATION_AUTHORIZED: Final = False
SETTLEMENT_AUTHORIZED: Final = False


class BurnAuctionLotTypeV1(StrEnum):
    UNRESTRICTED_PROTOCOL_REVENUE = "UNRESTRICTED_PROTOCOL_REVENUE"
    BUYBACK_CARRY = "BUYBACK_CARRY"


class BurnAuctionRejectCodeV1(StrEnum):
    TYPE_INVALID = "TYPE_INVALID"
    IDENTIFIER_INVALID = "IDENTIFIER_INVALID"
    ROOT_INVALID = "ROOT_INVALID"
    INTEGER_REQUIRED = "INTEGER_REQUIRED"
    AMOUNT_OUT_OF_RANGE = "AMOUNT_OUT_OF_RANGE"
    POLICY_INVALID = "POLICY_INVALID"
    POLICY_BINDING_MISMATCH = "POLICY_BINDING_MISMATCH"
    STATE_INVALID = "STATE_INVALID"
    AUCTION_PHASE_INVALID = "AUCTION_PHASE_INVALID"
    AUCTION_ALREADY_SETTLED = "AUCTION_ALREADY_SETTLED"
    LOT_ALREADY_CONSUMED = "LOT_ALREADY_CONSUMED"
    LOT_TYPE_NOT_ALLOWED = "LOT_TYPE_NOT_ALLOWED"
    LOT_ASSET_MISMATCH = "LOT_ASSET_MISMATCH"
    SOURCE_LOT_TOO_RECENT = "SOURCE_LOT_TOO_RECENT"
    VALUATION_BINDING_MISMATCH = "VALUATION_BINDING_MISMATCH"
    REFERENCE_TOO_RECENT = "REFERENCE_TOO_RECENT"
    REFERENCE_STALE = "REFERENCE_STALE"
    REFERENCE_DIVERSITY_INSUFFICIENT = "REFERENCE_DIVERSITY_INSUFFICIENT"
    REVEAL_SET_INCOMPLETE = "REVEAL_SET_INCOMPLETE"
    REVEAL_SET_ROOT_MISMATCH = "REVEAL_SET_ROOT_MISMATCH"
    BID_COUNT_EXCEEDED = "BID_COUNT_EXCEEDED"
    NONCANONICAL_BID_ORDER = "NONCANONICAL_BID_ORDER"
    DUPLICATE_COMMITMENT = "DUPLICATE_COMMITMENT"
    DUPLICATE_BIDDER = "DUPLICATE_BIDDER"
    BID_BINDING_MISMATCH = "BID_BINDING_MISMATCH"
    BID_NOT_FULLY_ESCROWED = "BID_NOT_FULLY_ESCROWED"
    COMMITMENT_MISMATCH = "COMMITMENT_MISMATCH"
    BURN_CAP_EXCEEDED = "BURN_CAP_EXCEEDED"
    BURN_INTERVAL_NOT_MET = "BURN_INTERVAL_NOT_MET"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"


class BurnAuctionCarryReasonV1(StrEnum):
    NO_REVEALED_BIDS = "NO_REVEALED_BIDS"
    RESERVE_NOT_MET = "RESERVE_NOT_MET"


class BurnEscrowDispositionKindV1(StrEnum):
    BURN = "BURN"
    RETURN = "RETURN"


@dataclass(frozen=True, slots=True)
class BurnAuctionPolicyV1:
    protocol_asset_id: str
    quote_asset_id: str
    supply_ceiling_atoms: int
    active_floor_atoms: int
    absolute_floor_atoms: int
    reserve_value_bps: int
    maximum_epoch_burn_bps: int
    maximum_epoch_burn_atoms: int
    minimum_source_lag_epochs: int
    minimum_reference_lag_epochs: int
    maximum_reference_age_epochs: int
    minimum_independent_reference_sources: int
    maximum_revealed_bids: int
    minimum_burn_interval_epochs: int
    profile_root: str
    valuation_profile_root: str
    admission_profile_root: str
    burn_authority_id: str


@dataclass(frozen=True, slots=True)
class BurnAuctionStateV1:
    supply_atoms: int
    cumulative_burn_atoms: int
    active_floor_atoms: int
    absolute_floor_atoms: int
    last_burn_epoch: int
    writer_epoch: int
    active_profile_root: str
    consumed_lot_ids: frozenset[str]
    settled_auction_ids: frozenset[str]


@dataclass(frozen=True, slots=True)
class BurnAuctionLotV1:
    lot_id: str
    lot_type: BurnAuctionLotTypeV1
    asset_id: str
    amount_atoms: int
    source_epoch: int
    source_root: str


@dataclass(frozen=True, slots=True)
class BurnAuctionV1:
    auction_id: str
    lot: BurnAuctionLotV1
    current_epoch: int
    commit_close_epoch: int
    reveal_close_epoch: int
    settlement_deadline_epoch: int
    expected_writer_epoch: int
    profile_root: str
    admission_profile_root: str
    complete_reveal_set_root: str
    admitted_reveal_count: int


@dataclass(frozen=True, slots=True)
class BurnAuctionValuationV1:
    lot_id: str
    quote_asset_id: str
    certified_lot_value_quote_atoms: int
    reference_quote_atoms: int
    reference_zdex_atoms: int
    occurrence_epoch: int
    independent_reference_source_count: int
    occurrence_root: str
    valuation_profile_root: str


@dataclass(frozen=True, slots=True)
class RevealedBurnBidV1:
    commitment_id: str
    auction_id: str
    lot_id: str
    profile_root: str
    bidder_capability_id: str
    recipient_id: str
    burn_bid_atoms: int
    escrowed_zdex_atoms: int
    reveal_epoch: int
    salt_root: str
    admission_witness_root: str


@dataclass(frozen=True, slots=True)
class BurnEscrowDispositionV1:
    commitment_id: str
    bidder_capability_id: str
    amount_atoms: int
    kind: BurnEscrowDispositionKindV1


@dataclass(frozen=True, slots=True)
class BurnAuctionEffectPlanV1:
    auction_id: str
    consumed_lot_id: str
    winner_capability_id: str
    winner_recipient_id: str
    burned_zdex_atoms: int
    transferred_lot_asset_id: str
    transferred_lot_atoms: int
    protocol_acquired_zdex_atoms: int
    escrow_dispositions: tuple[BurnEscrowDispositionV1, ...]
    burn_authority_id: str
    external_outbox_effect_count: int


@dataclass(frozen=True, slots=True)
class BurnAuctionCarryEffectPlanV1:
    auction_id: str
    carried_lot_id: str
    escrow_returns: tuple[BurnEscrowDispositionV1, ...]
    external_outbox_effect_count: int


@dataclass(frozen=True, slots=True)
class BurnAuctionSettlementCandidateV1:
    winner: RevealedBurnBidV1
    candidate_state_after: BurnAuctionStateV1
    effect_plan: BurnAuctionEffectPlanV1
    maximum_admissible_burn_atoms: int
    reserve_left_scaled_atoms: int
    reserve_right_scaled_atoms: int
    settlement_authorized: bool


@dataclass(frozen=True, slots=True)
class BurnAuctionCarryCandidateV1:
    reason: BurnAuctionCarryReasonV1
    lot_id: str
    candidate_state_after: BurnAuctionStateV1
    effect_plan: BurnAuctionCarryEffectPlanV1
    settlement_authorized: bool


@dataclass(frozen=True, slots=True)
class BurnAuctionRejectV1:
    code: BurnAuctionRejectCodeV1
    detail: str
    state_after: BurnAuctionStateV1
    effect_plan: tuple[BurnAuctionEffectPlanV1, ...]


BurnAuctionOutcomeV1: TypeAlias = (
    BurnAuctionSettlementCandidateV1 | BurnAuctionCarryCandidateV1 | BurnAuctionRejectV1
)


class FloorDescentRejectCodeV1(StrEnum):
    TYPE_INVALID = "TYPE_INVALID"
    ROOT_INVALID = "ROOT_INVALID"
    INTEGER_REQUIRED = "INTEGER_REQUIRED"
    AMOUNT_OUT_OF_RANGE = "AMOUNT_OUT_OF_RANGE"
    PROFILE_BINDING_MISMATCH = "PROFILE_BINDING_MISMATCH"
    ABSOLUTE_FLOOR_CHANGED = "ABSOLUTE_FLOOR_CHANGED"
    UNIT_SCALE_CHANGED = "UNIT_SCALE_CHANGED"
    FLOOR_NOT_LOWER = "FLOOR_NOT_LOWER"
    BELOW_ABSOLUTE_FLOOR = "BELOW_ABSOLUTE_FLOOR"
    ACTIVATION_TOO_EARLY = "ACTIVATION_TOO_EARLY"
    REDUCTION_TOO_DEEP = "REDUCTION_TOO_DEEP"
    POLICY_INVALID = "POLICY_INVALID"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"


@dataclass(frozen=True, slots=True)
class FloorProfileV1:
    profile_root: str
    predecessor_profile_root: str | None
    activation_epoch: int
    active_floor_atoms: int
    absolute_floor_atoms: int
    unit_scale: int


@dataclass(frozen=True, slots=True)
class FloorDescentPolicyV1:
    minimum_activation_delay_epochs: int
    maximum_reduction_bps: int


@dataclass(frozen=True, slots=True)
class FloorDescentCandidateV1:
    current_profile_root: str
    successor_profile_root: str
    release_root: str
    current_floor_atoms: int
    successor_floor_atoms: int
    minimum_permitted_successor_floor_atoms: int
    activation_epoch: int
    activation_authorized: bool


@dataclass(frozen=True, slots=True)
class FloorDescentRejectV1:
    code: FloorDescentRejectCodeV1
    detail: str


FloorDescentOutcomeV1: TypeAlias = FloorDescentCandidateV1 | FloorDescentRejectV1


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


def _integer_error(value: object) -> BurnAuctionRejectCodeV1 | None:
    if type(value) is not int:
        return BurnAuctionRejectCodeV1.INTEGER_REQUIRED
    if value < 0 or value > MAX_ATOMS:
        return BurnAuctionRejectCodeV1.AMOUNT_OUT_OF_RANGE
    return None


def _floor_integer_error(value: object) -> FloorDescentRejectCodeV1 | None:
    if type(value) is not int:
        return FloorDescentRejectCodeV1.INTEGER_REQUIRED
    if value < 0 or value > MAX_ATOMS:
        return FloorDescentRejectCodeV1.AMOUNT_OUT_OF_RANGE
    return None


def _checked_add(left: int, right: int) -> int:
    result = left + right
    if result > MAX_ATOMS:
        raise OverflowError
    return result


def _checked_mul(left: int, right: int) -> int:
    result = left * right
    if result > MAX_ATOMS:
        raise OverflowError
    return result


def _ceil_ratio(numerator: int, denominator: int) -> int:
    quotient, remainder = divmod(numerator, denominator)
    return _checked_add(quotient, 1 if remainder else 0)


def zeno_burn_cap_v1(supply_atoms: int, active_floor_atoms: int) -> int:
    """Return floor((supply-floor)/2), with zero at or below the floor."""

    if type(supply_atoms) is not int or type(active_floor_atoms) is not int:
        raise TypeError("supply and floor must be exact integers")
    if supply_atoms < 0 or active_floor_atoms < 0:
        raise ValueError("supply and floor must be nonnegative")
    if supply_atoms <= active_floor_atoms:
        return 0
    return (supply_atoms - active_floor_atoms) // 2


def burn_bid_commitment_v1(
    *,
    auction_id: str,
    lot_id: str,
    profile_root: str,
    bidder_capability_id: str,
    recipient_id: str,
    burn_bid_atoms: int,
    salt_root: str,
) -> str:
    payload = {
        "auction_id": auction_id,
        "bidder_capability_id": bidder_capability_id,
        "burn_bid_atoms": burn_bid_atoms,
        "domain": "zenodex/competitive-burn-to-claim-bid/v1",
        "lot_id": lot_id,
        "profile_root": profile_root,
        "recipient_id": recipient_id,
        "salt_root": salt_root,
    }
    encoded = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def reserve_value_cross_products_v1(
    *,
    burn_bid_atoms: int,
    reference_quote_atoms: int,
    certified_lot_value_quote_atoms: int,
    reference_zdex_atoms: int,
    reserve_value_bps: int,
) -> tuple[int, int]:
    """Return exact scaled sides of the reserve-value inequality."""

    left = _checked_mul(burn_bid_atoms, reference_quote_atoms)
    left = _checked_mul(left, BPS_SCALE)
    right = _checked_mul(
        certified_lot_value_quote_atoms,
        reference_zdex_atoms,
    )
    right = _checked_mul(right, reserve_value_bps)
    return left, right


def complete_reveal_set_root_v1(
    *,
    auction_id: str,
    admission_profile_root: str,
    bids: tuple[RevealedBurnBidV1, ...],
) -> str:
    payload = {
        "admission_profile_root": admission_profile_root,
        "auction_id": auction_id,
        "domain": "zenodex/competitive-burn-to-claim-reveal-set/v1",
        "reveals": [
            {
                "admission_witness_root": bid.admission_witness_root,
                "commitment_id": bid.commitment_id,
            }
            for bid in bids
        ],
    }
    encoded = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _reject(
    code: BurnAuctionRejectCodeV1,
    detail: str,
    state: BurnAuctionStateV1,
) -> BurnAuctionRejectV1:
    return BurnAuctionRejectV1(code, detail, state, ())


def _validate_policy(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
) -> BurnAuctionRejectV1 | None:
    if type(policy) is not BurnAuctionPolicyV1:
        return _reject(
            BurnAuctionRejectCodeV1.TYPE_INVALID,
            "policy must use the closed typed schema",
            state,
        )
    if not _valid_identifier(policy.protocol_asset_id) or not _valid_identifier(
        policy.quote_asset_id
    ):
        return _reject(
            BurnAuctionRejectCodeV1.IDENTIFIER_INVALID,
            "policy asset identifiers are invalid",
            state,
        )
    if policy.protocol_asset_id != "ZDEX":
        return _reject(
            BurnAuctionRejectCodeV1.POLICY_INVALID,
            "the research controller is scoped only to ZDEX",
            state,
        )
    if policy.quote_asset_id == policy.protocol_asset_id:
        return _reject(
            BurnAuctionRejectCodeV1.POLICY_INVALID,
            "the auction lot cannot itself use the protocol burn asset",
            state,
        )
    if not _valid_identifier(policy.burn_authority_id) or not all(
        _valid_root(root)
        for root in (
            policy.profile_root,
            policy.valuation_profile_root,
            policy.admission_profile_root,
        )
    ):
        return _reject(
            BurnAuctionRejectCodeV1.ROOT_INVALID,
            "policy authority and profile bindings are invalid",
            state,
        )
    integer_fields = asdict(policy)
    for field_name in (
        "supply_ceiling_atoms",
        "active_floor_atoms",
        "absolute_floor_atoms",
        "reserve_value_bps",
        "maximum_epoch_burn_bps",
        "maximum_epoch_burn_atoms",
        "minimum_source_lag_epochs",
        "minimum_reference_lag_epochs",
        "maximum_reference_age_epochs",
        "minimum_independent_reference_sources",
        "maximum_revealed_bids",
        "minimum_burn_interval_epochs",
    ):
        error = _integer_error(integer_fields[field_name])
        if error is not None:
            return _reject(error, f"{field_name} must be an exact integer", state)
    if (
        policy.absolute_floor_atoms == 0
        or policy.active_floor_atoms < policy.absolute_floor_atoms
        or policy.supply_ceiling_atoms < policy.active_floor_atoms
        or policy.reserve_value_bps > BPS_SCALE
        or policy.reserve_value_bps == 0
        or policy.maximum_epoch_burn_bps > BPS_SCALE
        or policy.maximum_epoch_burn_bps == 0
        or policy.maximum_epoch_burn_atoms == 0
        or policy.minimum_source_lag_epochs == 0
        or policy.minimum_reference_lag_epochs == 0
        or policy.minimum_independent_reference_sources == 0
        or policy.maximum_revealed_bids == 0
        or policy.maximum_revealed_bids > MAX_RESEARCH_BIDS
        or policy.minimum_burn_interval_epochs == 0
        or policy.maximum_reference_age_epochs < policy.minimum_reference_lag_epochs
    ):
        return _reject(
            BurnAuctionRejectCodeV1.POLICY_INVALID,
            "policy bounds are inconsistent",
            state,
        )
    return None


def _validate_state(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
) -> BurnAuctionRejectV1 | None:
    for field_name, value in (
        ("supply_atoms", state.supply_atoms),
        ("cumulative_burn_atoms", state.cumulative_burn_atoms),
        ("active_floor_atoms", state.active_floor_atoms),
        ("absolute_floor_atoms", state.absolute_floor_atoms),
        ("last_burn_epoch", state.last_burn_epoch),
        ("writer_epoch", state.writer_epoch),
    ):
        error = _integer_error(value)
        if error is not None:
            return _reject(error, f"{field_name} must be an exact integer", state)
    if not _valid_root(state.active_profile_root):
        return _reject(
            BurnAuctionRejectCodeV1.ROOT_INVALID,
            "active profile root is invalid",
            state,
        )
    if (
        state.active_profile_root != policy.profile_root
        or state.active_floor_atoms != policy.active_floor_atoms
        or state.absolute_floor_atoms != policy.absolute_floor_atoms
    ):
        return _reject(
            BurnAuctionRejectCodeV1.POLICY_BINDING_MISMATCH,
            "state and policy floor or profile bindings differ",
            state,
        )
    if (
        state.supply_atoms > policy.supply_ceiling_atoms
        or state.supply_atoms < state.active_floor_atoms
        or type(state.consumed_lot_ids) is not frozenset
        or type(state.settled_auction_ids) is not frozenset
        or any(not _valid_root(value) for value in state.consumed_lot_ids)
        or any(not _valid_root(value) for value in state.settled_auction_ids)
    ):
        return _reject(
            BurnAuctionRejectCodeV1.STATE_INVALID,
            "state supply, nullifier, or floor shape is invalid",
            state,
        )
    if state.cumulative_burn_atoms != policy.supply_ceiling_atoms - state.supply_atoms:
        return _reject(
            BurnAuctionRejectCodeV1.STATE_INVALID,
            "supply plus cumulative burn must reconcile to the policy ceiling",
            state,
        )
    return None


def _validate_auction(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
    auction: BurnAuctionV1,
) -> BurnAuctionRejectV1 | None:
    if type(auction) is not BurnAuctionV1 or type(auction.lot) is not BurnAuctionLotV1:
        return _reject(
            BurnAuctionRejectCodeV1.TYPE_INVALID,
            "auction and lot must use the closed typed schema",
            state,
        )
    lot = auction.lot
    roots = (
        auction.auction_id,
        auction.profile_root,
        auction.admission_profile_root,
        auction.complete_reveal_set_root,
        lot.lot_id,
        lot.source_root,
    )
    if not all(_valid_root(root) for root in roots):
        return _reject(
            BurnAuctionRejectCodeV1.ROOT_INVALID,
            "auction, lot, or reveal-set root is invalid",
            state,
        )
    if auction.auction_id in state.settled_auction_ids:
        return _reject(
            BurnAuctionRejectCodeV1.AUCTION_ALREADY_SETTLED,
            "auction id was already settled",
            state,
        )
    if lot.lot_id in state.consumed_lot_ids:
        return _reject(
            BurnAuctionRejectCodeV1.LOT_ALREADY_CONSUMED,
            "surplus lot was already consumed",
            state,
        )
    if type(lot.lot_type) is not BurnAuctionLotTypeV1:
        return _reject(
            BurnAuctionRejectCodeV1.LOT_TYPE_NOT_ALLOWED,
            "only unrestricted protocol revenue and buyback carry may be auctioned",
            state,
        )
    if not _valid_identifier(lot.asset_id) or lot.asset_id != policy.quote_asset_id:
        return _reject(
            BurnAuctionRejectCodeV1.LOT_ASSET_MISMATCH,
            "lot asset differs from the policy quote asset",
            state,
        )
    for field_name, value in (
        ("lot.amount_atoms", lot.amount_atoms),
        ("lot.source_epoch", lot.source_epoch),
        ("current_epoch", auction.current_epoch),
        ("commit_close_epoch", auction.commit_close_epoch),
        ("reveal_close_epoch", auction.reveal_close_epoch),
        ("settlement_deadline_epoch", auction.settlement_deadline_epoch),
        ("expected_writer_epoch", auction.expected_writer_epoch),
        ("admitted_reveal_count", auction.admitted_reveal_count),
    ):
        error = _integer_error(value)
        if error is not None:
            return _reject(error, f"{field_name} must be an exact integer", state)
    if lot.amount_atoms == 0:
        return _reject(
            BurnAuctionRejectCodeV1.AMOUNT_OUT_OF_RANGE,
            "surplus lot must be positive",
            state,
        )
    if (
        auction.profile_root != policy.profile_root
        or auction.admission_profile_root != policy.admission_profile_root
        or auction.expected_writer_epoch != state.writer_epoch
    ):
        return _reject(
            BurnAuctionRejectCodeV1.POLICY_BINDING_MISMATCH,
            "auction profile or writer epoch differs from state",
            state,
        )
    if lot.source_epoch > auction.commit_close_epoch or (
        auction.current_epoch - lot.source_epoch < policy.minimum_source_lag_epochs
    ):
        return _reject(
            BurnAuctionRejectCodeV1.SOURCE_LOT_TOO_RECENT,
            "the lot must exist before commit close and satisfy the source lag",
            state,
        )
    if not (
        auction.commit_close_epoch
        < auction.reveal_close_epoch
        < auction.current_epoch
        <= auction.settlement_deadline_epoch
    ):
        return _reject(
            BurnAuctionRejectCodeV1.AUCTION_PHASE_INVALID,
            "settlement must follow closed commit and reveal phases before deadline",
            state,
        )
    if auction.admitted_reveal_count > policy.maximum_revealed_bids:
        return _reject(
            BurnAuctionRejectCodeV1.BID_COUNT_EXCEEDED,
            "admitted reveal count exceeds the finite policy bound",
            state,
        )
    if (
        auction.current_epoch < state.last_burn_epoch
        or auction.current_epoch - state.last_burn_epoch < policy.minimum_burn_interval_epochs
    ):
        return _reject(
            BurnAuctionRejectCodeV1.BURN_INTERVAL_NOT_MET,
            "minimum interval since the prior burn has not elapsed",
            state,
        )
    return None


def _validate_valuation(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
    auction: BurnAuctionV1,
    valuation: BurnAuctionValuationV1,
) -> BurnAuctionRejectV1 | None:
    if type(valuation) is not BurnAuctionValuationV1:
        return _reject(
            BurnAuctionRejectCodeV1.TYPE_INVALID,
            "valuation must use the closed typed schema",
            state,
        )
    if not _valid_root(valuation.occurrence_root) or not _valid_root(
        valuation.valuation_profile_root
    ):
        return _reject(
            BurnAuctionRejectCodeV1.ROOT_INVALID,
            "valuation roots are invalid",
            state,
        )
    if (
        valuation.lot_id != auction.lot.lot_id
        or valuation.quote_asset_id != policy.quote_asset_id
        or valuation.valuation_profile_root != policy.valuation_profile_root
    ):
        return _reject(
            BurnAuctionRejectCodeV1.VALUATION_BINDING_MISMATCH,
            "valuation differs from lot, asset, or selected profile",
            state,
        )
    for field_name, value in (
        ("certified_lot_value_quote_atoms", valuation.certified_lot_value_quote_atoms),
        ("reference_quote_atoms", valuation.reference_quote_atoms),
        ("reference_zdex_atoms", valuation.reference_zdex_atoms),
        ("occurrence_epoch", valuation.occurrence_epoch),
        (
            "independent_reference_source_count",
            valuation.independent_reference_source_count,
        ),
    ):
        error = _integer_error(value)
        if error is not None:
            return _reject(error, f"{field_name} must be an exact integer", state)
    if (
        valuation.certified_lot_value_quote_atoms == 0
        or valuation.reference_quote_atoms == 0
        or valuation.reference_zdex_atoms == 0
    ):
        return _reject(
            BurnAuctionRejectCodeV1.AMOUNT_OUT_OF_RANGE,
            "valuation ratios and lot value must be positive",
            state,
        )
    if valuation.occurrence_epoch > auction.commit_close_epoch or (
        auction.current_epoch - valuation.occurrence_epoch < policy.minimum_reference_lag_epochs
    ):
        return _reject(
            BurnAuctionRejectCodeV1.REFERENCE_TOO_RECENT,
            "valuation must precede commit close and satisfy the reference lag",
            state,
        )
    if auction.current_epoch - valuation.occurrence_epoch > policy.maximum_reference_age_epochs:
        return _reject(
            BurnAuctionRejectCodeV1.REFERENCE_STALE,
            "valuation occurrence is stale",
            state,
        )
    if valuation.independent_reference_source_count < policy.minimum_independent_reference_sources:
        return _reject(
            BurnAuctionRejectCodeV1.REFERENCE_DIVERSITY_INSUFFICIENT,
            "valuation has too few independently qualified sources",
            state,
        )
    return None


def _maximum_admissible_burn(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
) -> int:
    zeno_cap = zeno_burn_cap_v1(state.supply_atoms, state.active_floor_atoms)
    rate_cap = (
        _checked_mul(
            state.supply_atoms,
            policy.maximum_epoch_burn_bps,
        )
        // BPS_SCALE
    )
    return min(zeno_cap, rate_cap, policy.maximum_epoch_burn_atoms)


def _validate_bids(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
    auction: BurnAuctionV1,
    bids: tuple[RevealedBurnBidV1, ...],
    maximum_burn_atoms: int,
) -> BurnAuctionRejectV1 | None:
    if type(bids) is not tuple or any(type(bid) is not RevealedBurnBidV1 for bid in bids):
        return _reject(
            BurnAuctionRejectCodeV1.TYPE_INVALID,
            "revealed bids must use the immutable typed schema",
            state,
        )
    if len(bids) != auction.admitted_reveal_count:
        return _reject(
            BurnAuctionRejectCodeV1.REVEAL_SET_INCOMPLETE,
            "bid tuple does not match the complete admitted reveal-set count",
            state,
        )
    commitment_ids = tuple(bid.commitment_id for bid in bids)
    if commitment_ids != tuple(sorted(commitment_ids)):
        return _reject(
            BurnAuctionRejectCodeV1.NONCANONICAL_BID_ORDER,
            "revealed bids must be ordered by commitment id",
            state,
        )
    if len(commitment_ids) != len(set(commitment_ids)):
        return _reject(
            BurnAuctionRejectCodeV1.DUPLICATE_COMMITMENT,
            "commitment ids must be unique",
            state,
        )
    bidder_ids = tuple(bid.bidder_capability_id for bid in bids)
    if len(bidder_ids) != len(set(bidder_ids)):
        return _reject(
            BurnAuctionRejectCodeV1.DUPLICATE_BIDDER,
            "one bidder capability may reveal at most one bid",
            state,
        )
    for bid in bids:
        if not all(
            _valid_root(root)
            for root in (
                bid.commitment_id,
                bid.auction_id,
                bid.lot_id,
                bid.profile_root,
                bid.salt_root,
                bid.admission_witness_root,
            )
        ) or not all(
            _valid_identifier(identifier)
            for identifier in (bid.bidder_capability_id, bid.recipient_id)
        ):
            return _reject(
                BurnAuctionRejectCodeV1.IDENTIFIER_INVALID,
                "bid identifiers or roots are invalid",
                state,
            )
        for field_name, value in (
            ("burn_bid_atoms", bid.burn_bid_atoms),
            ("escrowed_zdex_atoms", bid.escrowed_zdex_atoms),
            ("reveal_epoch", bid.reveal_epoch),
        ):
            error = _integer_error(value)
            if error is not None:
                return _reject(error, f"{field_name} must be an exact integer", state)
        if (
            bid.auction_id != auction.auction_id
            or bid.lot_id != auction.lot.lot_id
            or bid.profile_root != policy.profile_root
            or not auction.commit_close_epoch < bid.reveal_epoch <= auction.reveal_close_epoch
        ):
            return _reject(
                BurnAuctionRejectCodeV1.BID_BINDING_MISMATCH,
                "bid differs from auction, lot, profile, or reveal window",
                state,
            )
        if bid.burn_bid_atoms == 0 or bid.escrowed_zdex_atoms != bid.burn_bid_atoms:
            return _reject(
                BurnAuctionRejectCodeV1.BID_NOT_FULLY_ESCROWED,
                "each revealed burn bid must be positive and fully escrowed",
                state,
            )
        expected_commitment = burn_bid_commitment_v1(
            auction_id=bid.auction_id,
            lot_id=bid.lot_id,
            profile_root=bid.profile_root,
            bidder_capability_id=bid.bidder_capability_id,
            recipient_id=bid.recipient_id,
            burn_bid_atoms=bid.burn_bid_atoms,
            salt_root=bid.salt_root,
        )
        if bid.commitment_id != expected_commitment:
            return _reject(
                BurnAuctionRejectCodeV1.COMMITMENT_MISMATCH,
                "revealed bid does not open its commitment",
                state,
            )
        if bid.burn_bid_atoms > maximum_burn_atoms:
            return _reject(
                BurnAuctionRejectCodeV1.BURN_CAP_EXCEEDED,
                "revealed bid exceeds the epoch, rate, or strict Zeno cap",
                state,
            )
    expected_reveal_set_root = complete_reveal_set_root_v1(
        auction_id=auction.auction_id,
        admission_profile_root=auction.admission_profile_root,
        bids=bids,
    )
    if auction.complete_reveal_set_root != expected_reveal_set_root:
        return _reject(
            BurnAuctionRejectCodeV1.REVEAL_SET_ROOT_MISMATCH,
            "complete reveal-set root differs from the canonical supplied reveals",
            state,
        )
    return None


def _escrow_dispositions(
    bids: tuple[RevealedBurnBidV1, ...],
    *,
    winner_commitment_id: str | None,
) -> tuple[BurnEscrowDispositionV1, ...]:
    return tuple(
        BurnEscrowDispositionV1(
            commitment_id=bid.commitment_id,
            bidder_capability_id=bid.bidder_capability_id,
            amount_atoms=bid.escrowed_zdex_atoms,
            kind=(
                BurnEscrowDispositionKindV1.BURN
                if bid.commitment_id == winner_commitment_id
                else BurnEscrowDispositionKindV1.RETURN
            ),
        )
        for bid in bids
    )


def _carry_candidate(
    state: BurnAuctionStateV1,
    auction: BurnAuctionV1,
    bids: tuple[RevealedBurnBidV1, ...],
    reason: BurnAuctionCarryReasonV1,
) -> BurnAuctionCarryCandidateV1:
    candidate_state = replace(
        state,
        settled_auction_ids=state.settled_auction_ids | {auction.auction_id},
    )
    returns = _escrow_dispositions(bids, winner_commitment_id=None)
    return BurnAuctionCarryCandidateV1(
        reason=reason,
        lot_id=auction.lot.lot_id,
        candidate_state_after=candidate_state,
        effect_plan=BurnAuctionCarryEffectPlanV1(
            auction_id=auction.auction_id,
            carried_lot_id=auction.lot.lot_id,
            escrow_returns=returns,
            external_outbox_effect_count=0,
        ),
        settlement_authorized=False,
    )


def assess_burn_auction_settlement_v1(
    policy: BurnAuctionPolicyV1,
    state: BurnAuctionStateV1,
    auction: BurnAuctionV1,
    valuation: BurnAuctionValuationV1,
    bids: tuple[RevealedBurnBidV1, ...],
) -> BurnAuctionOutcomeV1:
    """Return a deterministic settlement candidate or an exact no-op outcome."""

    if type(state) is not BurnAuctionStateV1:
        raise TypeError("state must use BurnAuctionStateV1")
    for validator in (
        lambda: _validate_policy(policy, state),
        lambda: _validate_state(policy, state),
        lambda: _validate_auction(policy, state, auction),
        lambda: _validate_valuation(policy, state, auction, valuation),
    ):
        error = validator()
        if error is not None:
            return error
    try:
        maximum_burn_atoms = _maximum_admissible_burn(policy, state)
    except OverflowError:
        return _reject(
            BurnAuctionRejectCodeV1.ARITHMETIC_OVERFLOW,
            "burn-cap arithmetic exceeds 2^256 - 1",
            state,
        )
    bid_error = _validate_bids(
        policy,
        state,
        auction,
        bids,
        maximum_burn_atoms,
    )
    if bid_error is not None:
        return bid_error
    if not bids:
        return _carry_candidate(
            state,
            auction,
            bids,
            BurnAuctionCarryReasonV1.NO_REVEALED_BIDS,
        )
    winner = min(
        bids,
        key=lambda bid: (-bid.burn_bid_atoms, bid.commitment_id),
    )
    try:
        reserve_left, reserve_right = reserve_value_cross_products_v1(
            burn_bid_atoms=winner.burn_bid_atoms,
            reference_quote_atoms=valuation.reference_quote_atoms,
            certified_lot_value_quote_atoms=(valuation.certified_lot_value_quote_atoms),
            reference_zdex_atoms=valuation.reference_zdex_atoms,
            reserve_value_bps=policy.reserve_value_bps,
        )
    except OverflowError:
        return _reject(
            BurnAuctionRejectCodeV1.ARITHMETIC_OVERFLOW,
            "reserve-value cross multiplication exceeds 2^256 - 1",
            state,
        )
    if reserve_left < reserve_right:
        return _carry_candidate(
            state,
            auction,
            bids,
            BurnAuctionCarryReasonV1.RESERVE_NOT_MET,
        )
    supply_after = state.supply_atoms - winner.burn_bid_atoms
    if supply_after <= state.active_floor_atoms:
        return _reject(
            BurnAuctionRejectCodeV1.BURN_CAP_EXCEEDED,
            "settlement would reach or cross the active floor",
            state,
        )
    try:
        cumulative_burn_after = _checked_add(
            state.cumulative_burn_atoms,
            winner.burn_bid_atoms,
        )
    except OverflowError:
        return _reject(
            BurnAuctionRejectCodeV1.ARITHMETIC_OVERFLOW,
            "cumulative burn exceeds 2^256 - 1",
            state,
        )
    candidate_state = replace(
        state,
        supply_atoms=supply_after,
        cumulative_burn_atoms=cumulative_burn_after,
        last_burn_epoch=auction.current_epoch,
        consumed_lot_ids=state.consumed_lot_ids | {auction.lot.lot_id},
        settled_auction_ids=state.settled_auction_ids | {auction.auction_id},
    )
    effect = BurnAuctionEffectPlanV1(
        auction_id=auction.auction_id,
        consumed_lot_id=auction.lot.lot_id,
        winner_capability_id=winner.bidder_capability_id,
        winner_recipient_id=winner.recipient_id,
        burned_zdex_atoms=winner.burn_bid_atoms,
        transferred_lot_asset_id=auction.lot.asset_id,
        transferred_lot_atoms=auction.lot.amount_atoms,
        protocol_acquired_zdex_atoms=0,
        escrow_dispositions=_escrow_dispositions(
            bids,
            winner_commitment_id=winner.commitment_id,
        ),
        burn_authority_id=policy.burn_authority_id,
        external_outbox_effect_count=0,
    )
    return BurnAuctionSettlementCandidateV1(
        winner=winner,
        candidate_state_after=candidate_state,
        effect_plan=effect,
        maximum_admissible_burn_atoms=maximum_burn_atoms,
        reserve_left_scaled_atoms=reserve_left,
        reserve_right_scaled_atoms=reserve_right,
        settlement_authorized=False,
    )


def assess_floor_descent_v1(
    current: FloorProfileV1,
    successor: FloorProfileV1,
    policy: FloorDescentPolicyV1,
    *,
    current_epoch: int,
    release_root: str,
) -> FloorDescentOutcomeV1:
    if (
        type(current) is not FloorProfileV1
        or type(successor) is not FloorProfileV1
        or type(policy) is not FloorDescentPolicyV1
    ):
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.TYPE_INVALID,
            "floor profiles and policy must use the closed typed schema",
        )
    roots = (
        current.profile_root,
        successor.profile_root,
        release_root,
    )
    if (
        not all(_valid_root(root) for root in roots)
        or (
            current.predecessor_profile_root is not None
            and not _valid_root(current.predecessor_profile_root)
        )
        or (
            successor.predecessor_profile_root is not None
            and not _valid_root(successor.predecessor_profile_root)
        )
    ):
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.ROOT_INVALID,
            "floor profile or release roots are invalid",
        )
    integer_values = (
        current.activation_epoch,
        current.active_floor_atoms,
        current.absolute_floor_atoms,
        current.unit_scale,
        successor.activation_epoch,
        successor.active_floor_atoms,
        successor.absolute_floor_atoms,
        successor.unit_scale,
        policy.minimum_activation_delay_epochs,
        policy.maximum_reduction_bps,
        current_epoch,
    )
    for value in integer_values:
        error = _floor_integer_error(value)
        if error is not None:
            return FloorDescentRejectV1(error, "floor inputs must be exact integers")
    if (
        policy.minimum_activation_delay_epochs == 0
        or policy.maximum_reduction_bps == 0
        or policy.maximum_reduction_bps >= BPS_SCALE
    ):
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.POLICY_INVALID,
            "floor descent requires a positive delay and a reduction below 10000 bps",
        )
    if current.activation_epoch > current_epoch:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.PROFILE_BINDING_MISMATCH,
            "the predecessor floor profile is not active at the current epoch",
        )
    if current.absolute_floor_atoms != ZDEX_ABSOLUTE_FLOOR_ATOMS:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.ABSOLUTE_FLOOR_CHANGED,
            "the predecessor must retain the selected one-atom absolute floor",
        )
    if current.unit_scale != ZDEX_UNIT_SCALE:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.UNIT_SCALE_CHANGED,
            "the predecessor must retain the selected E18 unit scale",
        )
    if current.active_floor_atoms < current.absolute_floor_atoms:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.BELOW_ABSOLUTE_FLOOR,
            "the predecessor floor is below the absolute atom floor",
        )
    if (
        successor.predecessor_profile_root != current.profile_root
        or successor.profile_root == current.profile_root
    ):
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.PROFILE_BINDING_MISMATCH,
            "successor must name the exact predecessor and a new profile root",
        )
    if successor.absolute_floor_atoms != current.absolute_floor_atoms:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.ABSOLUTE_FLOOR_CHANGED,
            "the absolute atom floor cannot change in a descent profile",
        )
    if successor.unit_scale != current.unit_scale:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.UNIT_SCALE_CHANGED,
            "decimal scale changes require a separate versioned migration",
        )
    if successor.active_floor_atoms >= current.active_floor_atoms:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.FLOOR_NOT_LOWER,
            "successor floor must be strictly lower",
        )
    if successor.active_floor_atoms < current.absolute_floor_atoms:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.BELOW_ABSOLUTE_FLOOR,
            "successor floor is below the absolute atom floor",
        )
    try:
        earliest_activation = _checked_add(
            current_epoch,
            policy.minimum_activation_delay_epochs,
        )
        retained_bps = BPS_SCALE - policy.maximum_reduction_bps
        minimum_floor_numerator = _checked_mul(
            current.active_floor_atoms,
            retained_bps,
        )
        minimum_floor = max(
            current.absolute_floor_atoms,
            _ceil_ratio(minimum_floor_numerator, BPS_SCALE),
        )
    except OverflowError:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.ARITHMETIC_OVERFLOW,
            "floor descent arithmetic exceeds 2^256 - 1",
        )
    if successor.activation_epoch < earliest_activation:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.ACTIVATION_TOO_EARLY,
            "successor activation does not satisfy the release delay",
        )
    if successor.active_floor_atoms < minimum_floor:
        return FloorDescentRejectV1(
            FloorDescentRejectCodeV1.REDUCTION_TOO_DEEP,
            "successor floor reduction exceeds the selected step cap",
        )
    return FloorDescentCandidateV1(
        current_profile_root=current.profile_root,
        successor_profile_root=successor.profile_root,
        release_root=release_root,
        current_floor_atoms=current.active_floor_atoms,
        successor_floor_atoms=successor.active_floor_atoms,
        minimum_permitted_successor_floor_atoms=minimum_floor,
        activation_epoch=successor.activation_epoch,
        activation_authorized=False,
    )
