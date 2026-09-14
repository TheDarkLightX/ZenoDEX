"""Pure single-pool CPMM plans for the existing SwapIntent wire semantics.

The isolated policy retains the entire rounded fee in pool reserves. Context
and returned plans are ordinary data. A consumer must independently bind
authentication, current state, asset/LP ownership, replay and its proof profile
before the existing publisher can commit a complete global successor. This
component neither publishes nor establishes that global projection.
"""

from dataclasses import dataclass, fields, replace
from enum import Enum
from typing import TypeAlias

from ..kernels.python.settlement_swap_runtime_v1 import (
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
    SettlementSwapExactInQuote,
    SettlementSwapExactOutQuote,
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from ..state.intents import IntentKind, SwapIntent, _require_owned_intent_fields
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus, canonical_pool_asset_id
from .global_settlement_types_v2 import MAX_ATOMS_V2, MAX_U64_V2


def _integer(value: object, name: str, maximum: int) -> None:
    if type(value) is not int:
        raise TypeError(f"{name} must be exact int")
    if not 0 <= value <= maximum:
        raise ValueError(f"{name} outside admitted range")


def _text(value: object, name: str, maximum: int = 512) -> None:
    if type(value) is not str or not value or len(value) > maximum:
        raise TypeError(f"{name} must be bounded nonempty exact str")


@dataclass(frozen=True, slots=True)
class SpotPoolSnapshotV2:
    """Complete immutable PoolState value; LP ownership tables stay external."""

    pool_id: str
    asset0: str
    asset1: str
    reserve0: int
    reserve1: int
    fee_bps: int
    lp_supply: int
    status: PoolStatus
    created_at: int
    curve_tag: str
    curve_params: str

    def __post_init__(self) -> None:
        for name in ("pool_id", "asset0", "asset1", "curve_tag"):
            _text(getattr(self, name), name)
        for name in ("asset0", "asset1"):
            if canonical_pool_asset_id(getattr(self, name)) != getattr(self, name):
                raise ValueError("pool asset must already be canonical")
        if self.asset0 >= self.asset1:
            raise ValueError("pool assets must be distinct and ordered")
        for name in ("reserve0", "reserve1"):
            _integer(getattr(self, name), name, DEX_POOL_RESERVE_MAX)
        _integer(self.fee_bps, "fee_bps", 10_000)
        _integer(self.lp_supply, "lp_supply", MAX_ATOMS_V2)
        _integer(self.created_at, "created_at", MAX_U64_V2)
        if type(self.status) is not PoolStatus:
            raise TypeError("pool status must be exact PoolStatus")
        if type(self.curve_params) is not str or len(self.curve_params) > 4096:
            raise TypeError("curve_params must be bounded exact str")


@dataclass(frozen=True, slots=True)
class SpotSwapContextV2:
    """Explicit acquired data; subject and timestamp are not authenticated here."""

    subject_id: str
    block_timestamp: int
    sender_input_atoms: int
    recipient_output_atoms: int

    def __post_init__(self) -> None:
        _text(self.subject_id, "subject_id")
        _integer(self.block_timestamp, "block_timestamp", MAX_U64_V2)
        _integer(self.sender_input_atoms, "sender_input_atoms", MAX_ATOMS_V2)
        _integer(self.recipient_output_atoms, "recipient_output_atoms", MAX_ATOMS_V2)


class SpotSwapRejectCodeV2(str, Enum):
    SUBJECT_MISMATCH = "SUBJECT_MISMATCH"
    EXPIRED = "EXPIRED"
    UNSUPPORTED_FIELDS = "UNSUPPORTED_FIELDS"
    INVALID_NONCE = "INVALID_NONCE"
    POOL_MISMATCH = "POOL_MISMATCH"
    ASSET_MISMATCH = "ASSET_MISMATCH"
    POOL_INACTIVE = "POOL_INACTIVE"
    UNSUPPORTED_CURVE = "UNSUPPORTED_CURVE"
    QUOTE_REJECTED = "QUOTE_REJECTED"
    SLIPPAGE_LIMIT = "SLIPPAGE_LIMIT"
    INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
    BALANCE_OVERFLOW = "BALANCE_OVERFLOW"


@dataclass(frozen=True, slots=True)
class SpotSwapRejectedV2:
    code: SpotSwapRejectCodeV2


@dataclass(frozen=True, slots=True)
class SpotSwapPlanV2:
    """One owned pool/account update, without global or publication authority."""

    context: SpotSwapContextV2
    intent: SwapIntent
    pre_pool: SpotPoolSnapshotV2
    post_pool: SpotPoolSnapshotV2
    amount_in_atoms: int
    amount_out_atoms: int
    fee_atoms: int
    post_sender_input_atoms: int
    post_recipient_output_atoms: int

    @property
    def sender(self) -> str:
        return self.intent.sender_pubkey

    @property
    def recipient(self) -> str:
        return self.intent.get_field("recipient", self.sender)

    @property
    def account_deltas(self) -> tuple[int, int]:
        """Sender/input then recipient/output, in the exact intent's assets."""
        return -self.amount_in_atoms, self.amount_out_atoms

    @property
    def pool_deltas(self) -> tuple[int, int]:
        """Pool asset0 then asset1; these are physical holdings, not liabilities."""
        return (self.post_pool.reserve0 - self.pre_pool.reserve0,
                self.post_pool.reserve1 - self.pre_pool.reserve1)


def _snapshot_pool(pool: PoolState | SpotPoolSnapshotV2) -> SpotPoolSnapshotV2:
    if type(pool) not in (PoolState, SpotPoolSnapshotV2):
        raise TypeError("pool must be exact PoolState or SpotPoolSnapshotV2")
    # A new legacy field must acquire an explicit representation here.
    if tuple(f.name for f in fields(PoolState)) != tuple(f.name for f in fields(SpotPoolSnapshotV2)):
        raise TypeError("complete pool field registry differs")
    return SpotPoolSnapshotV2(**{
        f.name: object.__getattribute__(pool, f.name) for f in fields(SpotPoolSnapshotV2)
    })


def _snapshot_swap_fields(value: object, kind: IntentKind) -> dict[str, str | int] | SpotSwapRejectedV2:
    # Exact outer ownership alone does not validate a forged object's backing.
    raw = object.__getattribute__(_require_owned_intent_fields(value), "_items")
    if type(raw) is not tuple:
        raise TypeError("intent field backing must be exact tuple")
    amounts = ("amount_in", "min_amount_out") if kind is IntentKind.SWAP_EXACT_IN else (
        "amount_out", "max_amount_in")
    supported = {"pool_id", "asset_in", "asset_out", "nonce", "recipient", *amounts}
    if len(raw) > len(supported):
        return SpotSwapRejectedV2(SpotSwapRejectCodeV2.UNSUPPORTED_FIELDS)
    captured: dict[str, str | int] = {}
    previous = ""
    for pair in raw:
        if type(pair) is not tuple or len(pair) != 2 or type(pair[0]) is not str:
            raise TypeError("intent field entry must be exact (str, value) tuple")
        key, item = pair
        if key <= previous:
            raise ValueError("intent fields must have unique, ordered keys")
        previous = key
        if key not in supported:
            return SpotSwapRejectedV2(SpotSwapRejectCodeV2.UNSUPPORTED_FIELDS)
        if type(item) not in (str, int):
            raise TypeError("swap fields must contain exact flat scalars")
        captured[key] = item
    return captured


def _snapshot_intent(intent: SwapIntent) -> SwapIntent | SpotSwapRejectedV2:
    if type(intent) is not SwapIntent:
        raise TypeError("intent must be exact SwapIntent")
    values = {f.name: object.__getattribute__(intent, f.name) for f in fields(SwapIntent)}
    # Validate types before the legacy constructor can format or traverse them.
    for name in ("module", "version", "intent_id", "sender_pubkey"):
        _text(values[name], name)
    _integer(values["deadline"], "deadline", MAX_U64_V2)
    if values["salt"] is not None:
        _text(values["salt"], "salt", 4096)
    if type(values["kind"]) is not IntentKind:
        raise TypeError("kind must be exact IntentKind")
    if values["kind"] not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        raise ValueError("unsupported swap kind")
    captured = _snapshot_swap_fields(values["fields"], values["kind"])
    if isinstance(captured, SpotSwapRejectedV2):
        return captured
    values["fields"] = captured
    return SwapIntent(**values)


def _intent_reject(context: SpotSwapContextV2, pool: SpotPoolSnapshotV2,
                   intent: SwapIntent) -> SpotSwapRejectCodeV2 | None:
    code = SpotSwapRejectCodeV2
    if context.subject_id != intent.sender_pubkey:
        return code.SUBJECT_MISMATCH
    if intent.deadline < context.block_timestamp:
        return code.EXPIRED
    nonce = intent.get_field("nonce")
    if type(nonce) is not int or not 1 <= nonce <= (1 << 32) - 1:
        return code.INVALID_NONCE
    if intent.get_field("pool_id") != pool.pool_id:
        return code.POOL_MISMATCH
    if (intent.get_field("asset_in"), intent.get_field("asset_out")) not in (
        (pool.asset0, pool.asset1), (pool.asset1, pool.asset0),
    ):
        return code.ASSET_MISMATCH
    return None


Quote: TypeAlias = SettlementSwapExactInQuote | SettlementSwapExactOutQuote


def _quote(pool: SpotPoolSnapshotV2, intent: SwapIntent) -> Quote:
    reserve_in, reserve_out = (pool.reserve0, pool.reserve1) if intent.get_field("asset_in") == pool.asset0 else (
        pool.reserve1, pool.reserve0)
    if intent.kind is IntentKind.SWAP_EXACT_IN:
        return quote_cpmm_swap_exact_in(reserve_in=reserve_in, reserve_out=reserve_out,
            amount_in=intent.get_field("amount_in"), fee_bps=pool.fee_bps, protocol_fee_share_bps=0)
    return quote_cpmm_swap_exact_out(reserve_in=reserve_in, reserve_out=reserve_out,
        amount_out=intent.get_field("amount_out"), fee_bps=pool.fee_bps, protocol_fee_share_bps=0,
        max_overdelivery_gap_bps=CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT)


def _quote_fits(quote: Quote) -> bool:
    """Reconcile physical deltas and the next input's resource domain."""
    return (
        0 < quote.amount_in <= DEX_SWAP_AMOUNT_MAX and 0 < quote.amount_out <= DEX_SWAP_AMOUNT_MAX
        and 0 <= quote.fee_paid < quote.amount_in and quote.protocol_fee_paid == 0
        and quote.lp_fee_paid == quote.fee_paid
        and quote.reserve_in_after == quote.reserve_in_before + quote.amount_in
        and quote.reserve_out_after == quote.reserve_out_before - quote.amount_out
        and 0 < quote.reserve_in_after <= DEX_POOL_RESERVE_MAX
        and 0 < quote.reserve_out_after <= DEX_POOL_RESERVE_MAX
        and quote.reserve_in_after * quote.reserve_out_after >= quote.reserve_in_before * quote.reserve_out_before
    )


def _amount_reject(context: SpotSwapContextV2, intent: SwapIntent, quote: Quote) -> SpotSwapRejectCodeV2 | None:
    code = SpotSwapRejectCodeV2
    if not _quote_fits(quote):
        return code.QUOTE_REJECTED
    if intent.kind is IntentKind.SWAP_EXACT_IN:
        if quote.amount_out < intent.get_field("min_amount_out"):
            return code.SLIPPAGE_LIMIT
    elif quote.amount_in > intent.get_field("max_amount_in"):
        return code.SLIPPAGE_LIMIT
    if context.sender_input_atoms < quote.amount_in:
        return code.INSUFFICIENT_BALANCE
    if context.recipient_output_atoms + quote.amount_out > MAX_ATOMS_V2:
        return code.BALANCE_OVERFLOW
    return None


def plan_spot_swap_v2(context: SpotSwapContextV2, pool: PoolState | SpotPoolSnapshotV2,
                      intent: SwapIntent) -> SpotSwapPlanV2 | SpotSwapRejectedV2:
    """Snapshot structural inputs, then reject without effects or return a plan.

    Structurally invalid or foreign objects raise TypeError/ValueError before
    execution. Economic rejections return a closed reason with no successor.
    The supplied block timestamp retains the existing deadline semantics.
    """
    if type(context) is not SpotSwapContextV2:
        raise TypeError("context must be exact SpotSwapContextV2")
    try:
        context = replace(context)
        pre = _snapshot_pool(pool)
        owned_intent = _snapshot_intent(intent)
    except AttributeError as exc:
        raise TypeError("structural input is missing required data") from exc
    if isinstance(owned_intent, SpotSwapRejectedV2):
        return owned_intent
    reason = _intent_reject(context, pre, owned_intent)
    if reason is not None:
        return SpotSwapRejectedV2(reason)
    if pre.status is not PoolStatus.ACTIVE:
        return SpotSwapRejectedV2(SpotSwapRejectCodeV2.POOL_INACTIVE)
    if pre.curve_tag != CURVE_TAG_CPMM or pre.curve_params:
        return SpotSwapRejectedV2(SpotSwapRejectCodeV2.UNSUPPORTED_CURVE)
    try:
        quote = _quote(pre, owned_intent)
    except (ValueError, ArithmeticError):
        return SpotSwapRejectedV2(SpotSwapRejectCodeV2.QUOTE_REJECTED)
    reason = _amount_reject(context, owned_intent, quote)
    if reason is not None:
        return SpotSwapRejectedV2(reason)
    reserves = (quote.reserve_in_after, quote.reserve_out_after) if owned_intent.get_field("asset_in") == pre.asset0 else (
        quote.reserve_out_after, quote.reserve_in_after)
    return SpotSwapPlanV2(context, owned_intent, pre, replace(pre, reserve0=reserves[0], reserve1=reserves[1]),
        quote.amount_in, quote.amount_out, quote.fee_paid,
        context.sender_input_atoms - quote.amount_in, context.recipient_output_atoms + quote.amount_out)
