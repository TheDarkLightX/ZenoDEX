"""
Protocol fee router (deterministic, integer-only) -- 4-way split with dust carry.

This is the **reference / authoritative** implementation of ZenoDEX protocol-fee
routing for the Rust runtime migration (see ``docs/runtime/``). It routes a
per-domain protocol fee into four buckets -- ``buyburn``, ``stakers``,
``reserve``, ``hosts`` -- carrying rounding dust forward so value is never
stranded across repeated splits.

This module is *distinct* from :mod:`src.core.fees`, which is the legacy 3-way
swap-fee accumulator (``buyback`` / ``treasury`` / ``rewards``). That module and
its Tau spec (``src/tau_specs/tokenomics_fee_split_32_v1.tau``) and ESSO kernel
(``src/kernels/dex/fee_split_dust_carry_*.yaml``) are intentionally left
**unchanged**. This module is the new canonical surface that the Rust crate
``zenodex-runtime-core::fee_router`` shadows for bit-exact conformance.

Design rules honored here (see the task "Hard Rules"):

* No floating point -- integer arithmetic only.
* No wall-clock / randomness / I/O -- this is a pure transition.
* The transition returns an explicit :class:`RouteResult` (accepted *or*
  rejected). It never silently falls back: every rejection carries a stable
  machine code that matches the Rust ``RejectedReason::code()``.

Conservation invariant (identical to the ESSO ``fee_split_dust_carry`` kernel,
generalized from 3 to 4 buckets)::

    amount + dust_in == buyburn + stakers + reserve + hosts + dust_out

When ``dust_in == 0`` this reduces to the task's literal statement
``amount == buyburn + stakers + reserve + hosts + dust``.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Union

from ..state.canonical import (
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    sha256_hex,
)

__all__ = [
    "BPS_DENOM",
    "MAX_FEE_AMOUNT",
    "Domain",
    "DOMAINS",
    "FeeSplitTable",
    "FeeReceipt",
    "FeeAccumulator",
    "RouteAccepted",
    "RouteRejected",
    "RouteResult",
    "canonical_split_table",
    "route_fee",
    "RECEIPT_DOMAIN_SEP_LABEL",
    "ACCUMULATOR_DOMAIN_SEP_LABEL",
    "RECEIPT_VERSION",
    "ACCUMULATOR_VERSION",
]

BPS_DENOM = 10_000

# Upper bound on a single fee amount and on each accumulator component.
#
# The Rust shadow computes ``(amount + dust) * bps`` in ``u128``. Bounding every
# value below 2**112 guarantees that product stays below 2**128 (2**112 * 2**14
# = 2**126 < 2**128), so the Rust side never overflows for in-range inputs and
# the two runtimes agree on the rejection boundary.
MAX_FEE_AMOUNT = (1 << 112) - 1

# Canonical domain identifiers (lowercase ASCII; used verbatim in the receipt
# hash pre-image and in golden traces).
Domain = str
DEX: Domain = "dex"
PERPS: Domain = "perps"
BORROW: Domain = "borrow"
REDEMPTION: Domain = "redemption"
DOMAINS: frozenset[str] = frozenset({DEX, PERPS, BORROW, REDEMPTION})

# Domain-separation labels for the canonical hashers (versioned independently).
RECEIPT_DOMAIN_SEP_LABEL = "fee_receipt"
ACCUMULATOR_DOMAIN_SEP_LABEL = "fee_accumulator"
RECEIPT_VERSION = 1
ACCUMULATOR_VERSION = 1

# --- Stable rejection codes (must match Rust RejectedReason::code()) ----------
REJ_NEGATIVE_AMOUNT = "negative_amount"
REJ_AMOUNT_TOO_LARGE = "amount_too_large"
REJ_SPLIT_COMPONENT_OUT_OF_RANGE = "split_component_out_of_range"
REJ_SPLIT_DOES_NOT_SUM_TO_10000 = "split_does_not_sum_to_10000"
REJ_UNKNOWN_DOMAIN = "unknown_domain"
REJ_DOMAIN_CONSTRAINT_VIOLATED = "domain_constraint_violated"
REJ_ARITHMETIC_OVERFLOW = "arithmetic_overflow"

# Domain-constraint sub-codes (stable; surfaced as the ``detail`` field).
DETAIL_BUYBURN_BELOW_FLOOR = "buyburn_below_floor"
DETAIL_STAKERS_BELOW_FLOOR = "stakers_below_floor"
DETAIL_REDEMPTION_BUYBURN_MUST_BE_ZERO = "redemption_buyburn_must_be_zero"
DETAIL_REDEMPTION_HOSTS_MUST_BE_ZERO = "redemption_hosts_must_be_zero"
DETAIL_REDEMPTION_RESERVE_BELOW_FLOOR = "redemption_reserve_below_floor"

# Hard safety floors (basis points). These are *invariants*, looser than the
# concrete MVP tables in ``canonical_split_table``.
BUYBURN_FLOOR_BPS = 5_000  # dex / perps
STAKERS_FLOOR_BPS = 5_000  # borrow
REDEMPTION_RESERVE_FLOOR_BPS = 2_000


def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


@dataclass(frozen=True)
class FeeSplitTable:
    """A 4-way basis-point split. Plain data: policy is validated in ``route_fee``."""

    buyburn_bps: int
    stakers_bps: int
    reserve_bps: int
    hosts_bps: int

    def __post_init__(self) -> None:
        for name, v in self._items():
            if not _is_plain_int(v):
                raise TypeError(f"{name} must be an int")

    def _items(self) -> tuple[tuple[str, int], ...]:
        return (
            ("buyburn_bps", self.buyburn_bps),
            ("stakers_bps", self.stakers_bps),
            ("reserve_bps", self.reserve_bps),
            ("hosts_bps", self.hosts_bps),
        )


@dataclass(frozen=True)
class FeeReceipt:
    """Receipt for a single routed fee. ``amount`` is the raw input fee."""

    source: Domain
    asset: str
    amount: int
    buyburn: int
    stakers: int
    reserve: int
    hosts: int
    dust: int

    def receipt_hash(self) -> str:
        payload = (
            domain_sep_bytes(RECEIPT_DOMAIN_SEP_LABEL, version=RECEIPT_VERSION)
            + b"SRC"
            + encode_bytes(self.source.encode("ascii"))
            + b"AST"
            + encode_bytes(self.asset.encode("utf-8"))
            + b"AMT"
            + encode_uvarint(self.amount)
            + b"BBN"
            + encode_uvarint(self.buyburn)
            + b"STK"
            + encode_uvarint(self.stakers)
            + b"RSV"
            + encode_uvarint(self.reserve)
            + b"HST"
            + encode_uvarint(self.hosts)
            + b"DST"
            + encode_uvarint(self.dust)
        )
        return sha256_hex(payload)


@dataclass(frozen=True)
class FeeAccumulator:
    """
    Carried fee-router state.

    * ``dust`` -- rounding remainder carried into the next split (fee units).
    * ``cum_*`` -- cumulative value routed to each bucket. ``cum_buyburn`` is the
      buyback-accrual figure (accrual only; burn execution is a later module).
    """

    dust: int = 0
    cum_buyburn: int = 0
    cum_stakers: int = 0
    cum_reserve: int = 0
    cum_hosts: int = 0

    def __post_init__(self) -> None:
        for name, v in (
            ("dust", self.dust),
            ("cum_buyburn", self.cum_buyburn),
            ("cum_stakers", self.cum_stakers),
            ("cum_reserve", self.cum_reserve),
            ("cum_hosts", self.cum_hosts),
        ):
            if not _is_plain_int(v):
                raise TypeError(f"{name} must be an int")
            if v < 0:
                raise ValueError(f"{name} must be non-negative")

    def state_root(self) -> str:
        payload = (
            domain_sep_bytes(ACCUMULATOR_DOMAIN_SEP_LABEL, version=ACCUMULATOR_VERSION)
            + b"DST"
            + encode_uvarint(self.dust)
            + b"CBB"
            + encode_uvarint(self.cum_buyburn)
            + b"CST"
            + encode_uvarint(self.cum_stakers)
            + b"CRS"
            + encode_uvarint(self.cum_reserve)
            + b"CHS"
            + encode_uvarint(self.cum_hosts)
        )
        return sha256_hex(payload)


@dataclass(frozen=True)
class RouteAccepted:
    receipt: FeeReceipt
    accumulator: FeeAccumulator


@dataclass(frozen=True)
class RouteRejected:
    reason: str
    detail: Union[str, None] = None


RouteResult = Union[RouteAccepted, RouteRejected]


# --- Canonical MVP split tables ----------------------------------------------
# Expressed in basis points. See docs/runtime/RUST_RUNTIME_MIGRATION_PLAN.md and
# the "Important Current Economics Context" in the migration task.
#
#   DEX/perps:   60 buyburn / 0 stakers / 20 reserve / 20 hosts
#   Borrow:       0 buyburn / 60 stakers / 20 reserve / 20 hosts
#   Redemption:   0 buyburn / 60 stakers / 40 reserve / 0 hosts
_CANONICAL_TABLES: dict[str, FeeSplitTable] = {
    DEX: FeeSplitTable(buyburn_bps=6_000, stakers_bps=0, reserve_bps=2_000, hosts_bps=2_000),
    PERPS: FeeSplitTable(buyburn_bps=6_000, stakers_bps=0, reserve_bps=2_000, hosts_bps=2_000),
    BORROW: FeeSplitTable(buyburn_bps=0, stakers_bps=6_000, reserve_bps=2_000, hosts_bps=2_000),
    REDEMPTION: FeeSplitTable(buyburn_bps=0, stakers_bps=6_000, reserve_bps=4_000, hosts_bps=0),
}


def canonical_split_table(source: Domain) -> FeeSplitTable:
    """Return the canonical MVP split table for ``source`` (raises on unknown)."""
    try:
        return _CANONICAL_TABLES[source]
    except KeyError as exc:
        raise ValueError(f"unknown fee domain: {source!r}") from exc


def _check_domain_constraints(
    source: Domain, table: FeeSplitTable
) -> Union[RouteRejected, None]:
    """Enforce the per-domain safety floors. Returns a rejection or ``None``."""
    if source in (DEX, PERPS):
        if table.buyburn_bps < BUYBURN_FLOOR_BPS:
            return RouteRejected(REJ_DOMAIN_CONSTRAINT_VIOLATED, DETAIL_BUYBURN_BELOW_FLOOR)
    elif source == BORROW:
        if table.stakers_bps < STAKERS_FLOOR_BPS:
            return RouteRejected(REJ_DOMAIN_CONSTRAINT_VIOLATED, DETAIL_STAKERS_BELOW_FLOOR)
    elif source == REDEMPTION:
        if table.buyburn_bps != 0:
            return RouteRejected(
                REJ_DOMAIN_CONSTRAINT_VIOLATED, DETAIL_REDEMPTION_BUYBURN_MUST_BE_ZERO
            )
        if table.hosts_bps != 0:
            return RouteRejected(
                REJ_DOMAIN_CONSTRAINT_VIOLATED, DETAIL_REDEMPTION_HOSTS_MUST_BE_ZERO
            )
        if table.reserve_bps < REDEMPTION_RESERVE_FLOOR_BPS:
            return RouteRejected(
                REJ_DOMAIN_CONSTRAINT_VIOLATED, DETAIL_REDEMPTION_RESERVE_BELOW_FLOOR
            )
    return None


def route_fee(
    *,
    source: Domain,
    asset: str,
    amount: int,
    split_table: FeeSplitTable,
    accumulator: FeeAccumulator,
) -> RouteResult:
    """
    Route ``amount`` of protocol fees (in ``asset``) for ``source`` through
    ``split_table``, carrying dust from / into ``accumulator``.

    Returns :class:`RouteAccepted` (receipt + new accumulator) on success, or
    :class:`RouteRejected` (stable code + optional detail) otherwise. On
    rejection the accumulator is left untouched by the caller.

    The validation order is fixed and mirrored exactly by the Rust shadow so the
    two runtimes reject identical inputs with identical codes.
    """
    if not isinstance(source, str):
        raise TypeError("source must be a str")
    if not isinstance(asset, str):
        raise TypeError("asset must be a str")
    if not isinstance(split_table, FeeSplitTable):
        raise TypeError("split_table must be a FeeSplitTable")
    if not isinstance(accumulator, FeeAccumulator):
        raise TypeError("accumulator must be a FeeAccumulator")
    if not _is_plain_int(amount):
        raise TypeError("amount must be an int")

    # 1) Amount range.
    if amount < 0:
        return RouteRejected(REJ_NEGATIVE_AMOUNT)
    if amount > MAX_FEE_AMOUNT:
        return RouteRejected(REJ_AMOUNT_TOO_LARGE)

    # 2) Split-component range.
    for _, v in split_table._items():
        if v < 0 or v > BPS_DENOM:
            return RouteRejected(REJ_SPLIT_COMPONENT_OUT_OF_RANGE)

    # 3) Split must sum to exactly 10000.
    if (
        split_table.buyburn_bps
        + split_table.stakers_bps
        + split_table.reserve_bps
        + split_table.hosts_bps
    ) != BPS_DENOM:
        return RouteRejected(REJ_SPLIT_DOES_NOT_SUM_TO_10000)

    # 4) Domain must be known.
    if source not in DOMAINS:
        return RouteRejected(REJ_UNKNOWN_DOMAIN)

    # 5) Domain safety floors.
    domain_rej = _check_domain_constraints(source, split_table)
    if domain_rej is not None:
        return domain_rej

    # 6) Deterministic floor split with dust carry.
    total = amount + accumulator.dust
    buyburn = (total * split_table.buyburn_bps) // BPS_DENOM
    stakers = (total * split_table.stakers_bps) // BPS_DENOM
    reserve = (total * split_table.reserve_bps) // BPS_DENOM
    hosts = (total * split_table.hosts_bps) // BPS_DENOM
    distributed = buyburn + stakers + reserve + hosts
    # Floor division guarantees distributed <= total; assert defends the invariant.
    if distributed > total:
        raise AssertionError("fee split over-distributed (unreachable)")
    dust_out = total - distributed

    # 7) Accumulate (defensive overflow guard keeps parity with the u128 shadow).
    new_acc = FeeAccumulator(
        dust=dust_out,
        cum_buyburn=accumulator.cum_buyburn + buyburn,
        cum_stakers=accumulator.cum_stakers + stakers,
        cum_reserve=accumulator.cum_reserve + reserve,
        cum_hosts=accumulator.cum_hosts + hosts,
    )
    for v in (new_acc.cum_buyburn, new_acc.cum_stakers, new_acc.cum_reserve, new_acc.cum_hosts):
        if v > MAX_FEE_AMOUNT:
            return RouteRejected(REJ_ARITHMETIC_OVERFLOW)

    receipt = FeeReceipt(
        source=source,
        asset=asset,
        amount=amount,
        buyburn=buyburn,
        stakers=stakers,
        reserve=reserve,
        hosts=hosts,
        dust=dust_out,
    )
    return RouteAccepted(receipt=receipt, accumulator=new_acc)


def _conservation_holds(amount: int, dust_in: int, receipt: FeeReceipt) -> bool:
    """amount + dust_in == buyburn + stakers + reserve + hosts + dust_out."""
    return amount + dust_in == (
        receipt.buyburn + receipt.stakers + receipt.reserve + receipt.hosts + receipt.dust
    )


def apply_step(
    accumulator: FeeAccumulator,
    *,
    source: Domain,
    asset: str,
    amount: int,
    split_table: FeeSplitTable,
) -> RouteResult:
    """Convenience wrapper used by the golden-trace tooling (positional accumulator)."""
    result = route_fee(
        source=source,
        asset=asset,
        amount=amount,
        split_table=split_table,
        accumulator=accumulator,
    )
    if isinstance(result, RouteAccepted):
        assert _conservation_holds(amount, accumulator.dust, result.receipt)
    return result


def with_dust(accumulator: FeeAccumulator, dust: int) -> FeeAccumulator:
    """Return a copy of ``accumulator`` with ``dust`` replaced (test helper)."""
    return replace(accumulator, dust=dust)
