"""
Protocol fee router (deterministic, integer-only) -- 4-way split with dust carry.

This is the Python reference implementation of ZenoDEX protocol-fee routing for
the Rust runtime migration (see ``docs/runtime/``). It routes a
per-domain protocol fee into four buckets -- ``buyburn``, ``stakers``,
``reserve``, ``hosts`` -- carrying rounding dust forward per ``(source, asset)``
stream so value is never stranded across repeated splits or mixed across token
units.

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

from dataclasses import dataclass
from typing import Any, Union

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
    "FeeAssetAmount",
    "FeeDustEntry",
    "FeeAccumulator",
    "FEE_ROUTER_SURFACE",
    "RouteAccepted",
    "RouteRejected",
    "RouteResult",
    "FeeRouterConservationError",
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
ACCUMULATOR_VERSION = 2
FEE_ROUTER_SURFACE = "fee_router"

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
class FeeAssetAmount:
    """Canonical amount for one asset in one accumulator bucket."""

    asset: str
    amount: int

    def __post_init__(self) -> None:
        if not isinstance(self.asset, str):
            raise TypeError("asset must be a str")
        if not _is_plain_int(self.amount):
            raise TypeError("amount must be an int")
        if self.amount < 0:
            raise ValueError("amount must be non-negative")


@dataclass(frozen=True)
class FeeDustEntry:
    """Per-bucket scaled remainders for one source/asset fee stream.

    Design by Contract:
    * Preconditions: all remainders are non-negative basis-point numerators.
    * Invariant: ``amount`` is the whole-token dust represented by the sum of
      bucket remainders divided by ``BPS_DENOM`` for entries produced by this
      module. Legacy scalar-only entries are accepted and deterministically
      expanded at route time using the active split table.
    """

    source: Domain
    asset: str
    amount: int
    buyburn_remainder: int = 0
    stakers_remainder: int = 0
    reserve_remainder: int = 0
    hosts_remainder: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.source, str):
            raise TypeError("source must be a str")
        if not isinstance(self.asset, str):
            raise TypeError("asset must be a str")
        for name, value in self._items():
            if not _is_plain_int(value):
                raise TypeError(f"{name} must be an int")
            if value < 0:
                raise ValueError(f"{name} must be non-negative")
        self._check_remainder_invariant()

    def _check_remainder_invariant(self) -> None:
        remainders = self.remainders()
        if remainders == (0, 0, 0, 0):
            return
        if any(remainder >= BPS_DENOM for remainder in remainders):
            raise ValueError("dust remainders must be below BPS_DENOM")
        if sum(remainders) != self.amount * BPS_DENOM:
            raise ValueError("dust amount must equal scaled remainder sum")

    def _items(self) -> tuple[tuple[str, int], ...]:
        return (
            ("amount", self.amount),
            ("buyburn_remainder", self.buyburn_remainder),
            ("stakers_remainder", self.stakers_remainder),
            ("reserve_remainder", self.reserve_remainder),
            ("hosts_remainder", self.hosts_remainder),
        )

    def remainders(self) -> tuple[int, int, int, int]:
        return (
            self.buyburn_remainder,
            self.stakers_remainder,
            self.reserve_remainder,
            self.hosts_remainder,
        )


def _canonical_asset_amounts(entries: tuple[FeeAssetAmount, ...]) -> tuple[FeeAssetAmount, ...]:
    if any(not isinstance(e, FeeAssetAmount) for e in entries):
        raise TypeError("bucket entries must be FeeAssetAmount")
    filtered = tuple(e for e in entries if e.amount != 0)
    ordered = tuple(sorted(filtered, key=lambda e: e.asset))
    for prev, cur in zip(ordered, ordered[1:]):
        if prev.asset == cur.asset:
            raise ValueError(f"duplicate asset accumulator entry: {cur.asset!r}")
    return ordered


def _canonical_dust_entries(entries: tuple[FeeDustEntry, ...]) -> tuple[FeeDustEntry, ...]:
    if any(not isinstance(e, FeeDustEntry) for e in entries):
        raise TypeError("dust entries must be FeeDustEntry")
    filtered = tuple(e for e in entries if e.amount != 0)
    ordered = tuple(sorted(filtered, key=lambda e: (e.source, e.asset)))
    for prev, cur in zip(ordered, ordered[1:]):
        if (prev.source, prev.asset) == (cur.source, cur.asset):
            raise ValueError(
                f"duplicate dust accumulator entry: {(cur.source, cur.asset)!r}"
            )
    return ordered


def _asset_amount(entries: tuple[FeeAssetAmount, ...], asset: str) -> int:
    for entry in entries:
        if entry.asset == asset:
            return entry.amount
    return 0


def _dust_entry(
    entries: tuple[FeeDustEntry, ...], source: Domain, asset: str
) -> Union[FeeDustEntry, None]:
    for entry in entries:
        if entry.source == source and entry.asset == asset:
            return entry
    return None


def _dust_amount(entries: tuple[FeeDustEntry, ...], source: Domain, asset: str) -> int:
    entry = _dust_entry(entries, source, asset)
    if entry is None:
        return 0
    return entry.amount


def _legacy_remainders(amount: int, table: FeeSplitTable) -> tuple[int, int, int, int]:
    return (
        amount * table.buyburn_bps,
        amount * table.stakers_bps,
        amount * table.reserve_bps,
        amount * table.hosts_bps,
    )


def _entry_remainders(
    entry: Union[FeeDustEntry, None], table: FeeSplitTable
) -> tuple[int, int, int, int]:
    if entry is None:
        return (0, 0, 0, 0)
    if entry.remainders() == (0, 0, 0, 0) and entry.amount != 0:
        return _legacy_remainders(entry.amount, table)
    return entry.remainders()


def _dust_from_remainders(remainders: tuple[int, int, int, int]) -> int:
    remainder_sum = sum(remainders)
    if remainder_sum % BPS_DENOM != 0:
        raise AssertionError("fee split produced fractional aggregate dust")
    return remainder_sum // BPS_DENOM


def _set_asset_amount(
    entries: tuple[FeeAssetAmount, ...], asset: str, amount: int
) -> tuple[FeeAssetAmount, ...]:
    rest = tuple(e for e in entries if e.asset != asset)
    if amount == 0:
        return rest
    return _canonical_asset_amounts(rest + (FeeAssetAmount(asset=asset, amount=amount),))


def _set_dust_entry(
    entries: tuple[FeeDustEntry, ...],
    source: Domain,
    asset: str,
    amount: int,
    remainders: tuple[int, int, int, int],
) -> tuple[FeeDustEntry, ...]:
    rest = tuple(e for e in entries if not (e.source == source and e.asset == asset))
    if amount == 0:
        return rest
    return _canonical_dust_entries(
        rest
        + (
            FeeDustEntry(
                source=source,
                asset=asset,
                amount=amount,
                buyburn_remainder=remainders[0],
                stakers_remainder=remainders[1],
                reserve_remainder=remainders[2],
                hosts_remainder=remainders[3],
            ),
        )
    )


def _encode_asset_amounts(entries: tuple[FeeAssetAmount, ...]) -> bytes:
    payload = encode_uvarint(len(entries))
    for entry in entries:
        payload += b"AST" + encode_bytes(entry.asset.encode("utf-8"))
        payload += b"AMT" + encode_uvarint(entry.amount)
    return payload


def _encode_dust_entries(entries: tuple[FeeDustEntry, ...]) -> bytes:
    payload = encode_uvarint(len(entries))
    for entry in entries:
        payload += b"SRC" + encode_bytes(entry.source.encode("ascii"))
        payload += b"AST" + encode_bytes(entry.asset.encode("utf-8"))
        payload += b"AMT" + encode_uvarint(entry.amount)
        payload += b"BBR" + encode_uvarint(entry.buyburn_remainder)
        payload += b"STR" + encode_uvarint(entry.stakers_remainder)
        payload += b"RSR" + encode_uvarint(entry.reserve_remainder)
        payload += b"HSR" + encode_uvarint(entry.hosts_remainder)
    return payload


@dataclass(frozen=True)
class FeeAccumulator:
    """
    Carried fee-router state.

    ``dust_by_stream`` is keyed by ``(source, asset)`` so a remainder from one
    token or policy stream can never be consumed by another. The cumulative
    buckets are keyed by ``asset`` because bucket balances in different token
    units are not addable.
    """

    dust_by_stream: tuple[FeeDustEntry, ...] = ()
    cum_buyburn: tuple[FeeAssetAmount, ...] = ()
    cum_stakers: tuple[FeeAssetAmount, ...] = ()
    cum_reserve: tuple[FeeAssetAmount, ...] = ()
    cum_hosts: tuple[FeeAssetAmount, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.dust_by_stream, tuple):
            raise TypeError("dust_by_stream must be a tuple")
        if not isinstance(self.cum_buyburn, tuple):
            raise TypeError("cum_buyburn must be a tuple")
        if not isinstance(self.cum_stakers, tuple):
            raise TypeError("cum_stakers must be a tuple")
        if not isinstance(self.cum_reserve, tuple):
            raise TypeError("cum_reserve must be a tuple")
        if not isinstance(self.cum_hosts, tuple):
            raise TypeError("cum_hosts must be a tuple")

        object.__setattr__(
            self, "dust_by_stream", _canonical_dust_entries(self.dust_by_stream)
        )
        object.__setattr__(self, "cum_buyburn", _canonical_asset_amounts(self.cum_buyburn))
        object.__setattr__(self, "cum_stakers", _canonical_asset_amounts(self.cum_stakers))
        object.__setattr__(self, "cum_reserve", _canonical_asset_amounts(self.cum_reserve))
        object.__setattr__(self, "cum_hosts", _canonical_asset_amounts(self.cum_hosts))

    def dust_for(self, source: Domain, asset: str) -> int:
        return _dust_amount(self.dust_by_stream, source, asset)

    def bucket_total(self, bucket: str, asset: str) -> int:
        return _asset_amount(getattr(self, bucket), asset)

    def with_dust(
        self,
        source: Domain,
        asset: str,
        amount: int,
        remainders: tuple[int, int, int, int] = (0, 0, 0, 0),
    ) -> "FeeAccumulator":
        return FeeAccumulator(
            dust_by_stream=_set_dust_entry(
                self.dust_by_stream, source, asset, amount, remainders
            ),
            cum_buyburn=self.cum_buyburn,
            cum_stakers=self.cum_stakers,
            cum_reserve=self.cum_reserve,
            cum_hosts=self.cum_hosts,
        )

    def with_bucket_amount(self, bucket: str, asset: str, amount: int) -> "FeeAccumulator":
        return FeeAccumulator(
            dust_by_stream=self.dust_by_stream,
            cum_buyburn=(
                _set_asset_amount(self.cum_buyburn, asset, amount)
                if bucket == "cum_buyburn"
                else self.cum_buyburn
            ),
            cum_stakers=(
                _set_asset_amount(self.cum_stakers, asset, amount)
                if bucket == "cum_stakers"
                else self.cum_stakers
            ),
            cum_reserve=(
                _set_asset_amount(self.cum_reserve, asset, amount)
                if bucket == "cum_reserve"
                else self.cum_reserve
            ),
            cum_hosts=(
                _set_asset_amount(self.cum_hosts, asset, amount)
                if bucket == "cum_hosts"
                else self.cum_hosts
            ),
        )

    def state_root(self) -> str:
        payload = (
            domain_sep_bytes(ACCUMULATOR_DOMAIN_SEP_LABEL, version=ACCUMULATOR_VERSION)
            + b"DST"
            + _encode_dust_entries(self.dust_by_stream)
            + b"CBB"
            + _encode_asset_amounts(self.cum_buyburn)
            + b"CST"
            + _encode_asset_amounts(self.cum_stakers)
            + b"CRS"
            + _encode_asset_amounts(self.cum_reserve)
            + b"CHS"
            + _encode_asset_amounts(self.cum_hosts)
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


def _reject_reason_str(rejected: RouteRejected) -> str:
    if rejected.detail is None:
        return rejected.reason
    return f"{rejected.reason}:{rejected.detail}"


def _accumulator_json(accumulator: FeeAccumulator) -> dict[str, list[dict[str, Any]]]:
    return {
        "dust_by_stream": [
            {
                "source": e.source,
                "asset": e.asset,
                "amount": e.amount,
                "buyburn_remainder": e.buyburn_remainder,
                "stakers_remainder": e.stakers_remainder,
                "reserve_remainder": e.reserve_remainder,
                "hosts_remainder": e.hosts_remainder,
            }
            for e in accumulator.dust_by_stream
        ],
        "cum_buyburn": [
            {"asset": e.asset, "amount": e.amount} for e in accumulator.cum_buyburn
        ],
        "cum_stakers": [
            {"asset": e.asset, "amount": e.amount} for e in accumulator.cum_stakers
        ],
        "cum_reserve": [
            {"asset": e.asset, "amount": e.amount} for e in accumulator.cum_reserve
        ],
        "cum_hosts": [
            {"asset": e.asset, "amount": e.amount} for e in accumulator.cum_hosts
        ],
    }


def _accumulator_from_json(doc: dict[str, Any]) -> FeeAccumulator:
    return FeeAccumulator(
        dust_by_stream=tuple(
            FeeDustEntry(
                str(e["source"]),
                str(e["asset"]),
                int(e["amount"]),
                int(e.get("buyburn_remainder", 0)),
                int(e.get("stakers_remainder", 0)),
                int(e.get("reserve_remainder", 0)),
                int(e.get("hosts_remainder", 0)),
            )
            for e in doc.get("dust_by_stream", [])
        ),
        cum_buyburn=tuple(
            FeeAssetAmount(str(e["asset"]), int(e["amount"]))
            for e in doc.get("cum_buyburn", [])
        ),
        cum_stakers=tuple(
            FeeAssetAmount(str(e["asset"]), int(e["amount"]))
            for e in doc.get("cum_stakers", [])
        ),
        cum_reserve=tuple(
            FeeAssetAmount(str(e["asset"]), int(e["amount"]))
            for e in doc.get("cum_reserve", [])
        ),
        cum_hosts=tuple(
            FeeAssetAmount(str(e["asset"]), int(e["amount"]))
            for e in doc.get("cum_hosts", [])
        ),
    )


def _split_table_json(table: FeeSplitTable) -> dict[str, int]:
    return {
        "buyburn_bps": table.buyburn_bps,
        "stakers_bps": table.stakers_bps,
        "reserve_bps": table.reserve_bps,
        "hosts_bps": table.hosts_bps,
    }


def _tx_json(source: Domain, asset: str, amount: int, split_table: FeeSplitTable) -> dict[str, Any]:
    return {
        "kind": "route_fee",
        "source": source,
        "asset": asset,
        "amount": amount,
        "split_table": _split_table_json(split_table),
    }


def _receipt_json(receipt: FeeReceipt) -> dict[str, str]:
    return {
        "source": receipt.source,
        "asset": receipt.asset,
        "amount": str(receipt.amount),
        "buyburn": str(receipt.buyburn),
        "stakers": str(receipt.stakers),
        "reserve": str(receipt.reserve),
        "hosts": str(receipt.hosts),
        "dust": str(receipt.dust),
    }


def _accumulator_doc_strings(accumulator: FeeAccumulator) -> dict[str, list[dict[str, str]]]:
    return {
        "dust_by_stream": [
            {
                "source": e.source,
                "asset": e.asset,
                "amount": str(e.amount),
                "buyburn_remainder": str(e.buyburn_remainder),
                "stakers_remainder": str(e.stakers_remainder),
                "reserve_remainder": str(e.reserve_remainder),
                "hosts_remainder": str(e.hosts_remainder),
            }
            for e in accumulator.dust_by_stream
        ],
        "cum_buyburn": [
            {"asset": e.asset, "amount": str(e.amount)} for e in accumulator.cum_buyburn
        ],
        "cum_stakers": [
            {"asset": e.asset, "amount": str(e.amount)} for e in accumulator.cum_stakers
        ],
        "cum_reserve": [
            {"asset": e.asset, "amount": str(e.amount)} for e in accumulator.cum_reserve
        ],
        "cum_hosts": [
            {"asset": e.asset, "amount": str(e.amount)} for e in accumulator.cum_hosts
        ],
    }


def _result_to_authority_doc(pre_accumulator: FeeAccumulator, result: RouteResult) -> dict[str, Any]:
    pre_root = pre_accumulator.state_root()
    if isinstance(result, RouteAccepted):
        return {
            "version": 1,
            "kernel": FEE_ROUTER_SURFACE,
            "accept": True,
            "reject_reason": None,
            "receipt_hash": result.receipt.receipt_hash(),
            "receipt": _receipt_json(result.receipt),
            "pre_state_root": pre_root,
            "post_state_root": result.accumulator.state_root(),
            "post_accumulator": _accumulator_doc_strings(result.accumulator),
        }
    return {
        "version": 1,
        "kernel": FEE_ROUTER_SURFACE,
        "accept": False,
        "reject_reason": _reject_reason_str(result),
        "receipt_hash": None,
        "receipt": None,
        "pre_state_root": pre_root,
        "post_state_root": pre_root,
        "post_accumulator": _accumulator_doc_strings(pre_accumulator),
    }


def _authority_doc_to_result(doc: dict[str, Any]) -> RouteResult:
    if bool(doc.get("accept")):
        receipt_doc = doc.get("receipt")
        accumulator_doc = doc.get("post_accumulator")
        if not isinstance(receipt_doc, dict) or not isinstance(accumulator_doc, dict):
            raise ValueError("accepted fee_router authority doc missing receipt or accumulator")
        receipt = FeeReceipt(
            source=str(receipt_doc["source"]),
            asset=str(receipt_doc["asset"]),
            amount=int(receipt_doc["amount"]),
            buyburn=int(receipt_doc["buyburn"]),
            stakers=int(receipt_doc["stakers"]),
            reserve=int(receipt_doc["reserve"]),
            hosts=int(receipt_doc["hosts"]),
            dust=int(receipt_doc["dust"]),
        )
        return RouteAccepted(receipt=receipt, accumulator=_accumulator_from_json(accumulator_doc))
    reason = doc.get("reject_reason")
    if not isinstance(reason, str):
        raise ValueError("rejected fee_router authority doc missing reason")
    if ":" in reason:
        code, detail = reason.split(":", 1)
        return RouteRejected(code, detail)
    return RouteRejected(reason)


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


class FeeRouterConservationError(RuntimeError):
    """Fail-closed marker: an accepted fee split did not conserve value.

    Raised when ``amount + dust_in != buyburn + stakers + reserve + hosts + dust_out``.
    The split is conservation-exact by construction for every valid input (see
    :func:`_conservation_holds`), so a violation indicates routing/accumulator
    corruption and must hard-reject — never silently commit. Encoded as an explicit
    raise rather than a bare ``assert`` (which ``python -O`` strips, failing open).
    """


def _route_fee_python(
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

    # 6) Deterministic per-bucket remainder split. Each bucket carries only its
    # own scaled fractional entitlement, so small-fee granularity cannot move
    # reserve/host/staker value into a dominant bucket.
    prev_remainders = _entry_remainders(
        _dust_entry(accumulator.dust_by_stream, source, asset), split_table
    )
    buyburn_num = amount * split_table.buyburn_bps + prev_remainders[0]
    stakers_num = amount * split_table.stakers_bps + prev_remainders[1]
    reserve_num = amount * split_table.reserve_bps + prev_remainders[2]
    hosts_num = amount * split_table.hosts_bps + prev_remainders[3]
    buyburn, buyburn_rem = divmod(buyburn_num, BPS_DENOM)
    stakers, stakers_rem = divmod(stakers_num, BPS_DENOM)
    reserve, reserve_rem = divmod(reserve_num, BPS_DENOM)
    hosts, hosts_rem = divmod(hosts_num, BPS_DENOM)
    dust_remainders = (buyburn_rem, stakers_rem, reserve_rem, hosts_rem)
    dust_out = _dust_from_remainders(dust_remainders)

    # 7) Accumulate (defensive overflow guard keeps parity with the u128 shadow).
    new_buyburn = accumulator.bucket_total("cum_buyburn", asset) + buyburn
    new_stakers = accumulator.bucket_total("cum_stakers", asset) + stakers
    new_reserve = accumulator.bucket_total("cum_reserve", asset) + reserve
    new_hosts = accumulator.bucket_total("cum_hosts", asset) + hosts
    for v in (new_buyburn, new_stakers, new_reserve, new_hosts):
        if v > MAX_FEE_AMOUNT:
            return RouteRejected(REJ_ARITHMETIC_OVERFLOW)
    new_acc = (
        accumulator.with_dust(source, asset, dust_out, dust_remainders)
        .with_bucket_amount("cum_buyburn", asset, new_buyburn)
        .with_bucket_amount("cum_stakers", asset, new_stakers)
        .with_bucket_amount("cum_reserve", asset, new_reserve)
        .with_bucket_amount("cum_hosts", asset, new_hosts)
    )

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
    # Catastrophic invariant, enforced fail-closed on the authority path (not just
    # the apply_step wrapper, and not via a `-O`-stripped assert): the accepted
    # split must conserve value against the carried-in dust.
    if not _conservation_holds(amount, accumulator.dust_for(source, asset), receipt):
        raise FeeRouterConservationError(
            f"fee split conservation violated: source={source!r} asset={asset!r} amount={amount}"
        )
    return RouteAccepted(receipt=receipt, accumulator=new_acc)


def route_fee(
    *,
    source: Domain,
    asset: str,
    amount: int,
    split_table: FeeSplitTable,
    accumulator: FeeAccumulator,
) -> RouteResult:
    """
    Route ``amount`` of protocol fees through the active runtime authority
    policy, carrying dust from / into ``accumulator``.

    Python remains the default authority. A deployment profile can promote this
    surface to Rust authority with Python shadow checking.
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

    from src.runtime.authority import AuthorityMode, active_mode, decide
    from src.runtime.rust_invoker import fee_route

    mode = active_mode(FEE_ROUTER_SURFACE)
    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return _route_fee_python(
            source=source,
            asset=asset,
            amount=amount,
            split_table=split_table,
            accumulator=accumulator,
        )

    def python_doc() -> dict[str, Any]:
        return _result_to_authority_doc(
            accumulator,
            _route_fee_python(
                source=source,
                asset=asset,
                amount=amount,
                split_table=split_table,
                accumulator=accumulator,
            ),
        )

    def rust_doc() -> dict[str, Any]:
        return fee_route(
            accumulator=_accumulator_json(accumulator),
            tx=_tx_json(source, asset, amount, split_table),
        )

    decision = decide(
        FEE_ROUTER_SURFACE,
        mode,
        python_fn=python_doc,
        rust_fn=rust_doc,
    )
    return _authority_doc_to_result(decision.result)


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
    if isinstance(result, RouteAccepted) and not _conservation_holds(
        amount, accumulator.dust_for(source, asset), result.receipt
    ):
        # Fail closed (and `-O`-safe): a bare `assert` here would be stripped under
        # `python -O`, silently disabling this conservation guard in optimized runs.
        raise FeeRouterConservationError(
            f"fee split conservation violated (apply_step): source={source!r} asset={asset!r}"
        )
    return result


def with_dust(
    accumulator: FeeAccumulator, dust: int, *, source: Domain = DEX, asset: str = "zUSD"
) -> FeeAccumulator:
    """Return a copy of ``accumulator`` with one stream's dust replaced."""
    return accumulator.with_dust(source, asset, dust)
