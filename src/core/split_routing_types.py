"""Split-routing data contracts and canonical route keys."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence, Tuple

from ..state.balances import Amount


def _positive_int(value: object, *, name: str) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must be positive")
    out = int(value)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _int_not_bool(value: object, *, name: str) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return int(value)


@dataclass(frozen=True)
class SplitTwoPoolsQuote:
    pool0_id: str
    pool1_id: str
    amount_in_total: Amount
    amount_out_total: Amount
    amount_in_0: Amount
    amount_out_0: Amount
    amount_in_1: Amount
    amount_out_1: Amount


@dataclass(frozen=True)
class SplitLegQuote:
    pool_id: str
    amount_in: Amount
    amount_out: Amount

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        _positive_int(self.amount_in, name="amount_in")
        _positive_int(self.amount_out, name="amount_out")


@dataclass(frozen=True)
class SplitManyPoolsQuote:
    amount_in_total: Amount
    amount_out_total: Amount
    legs: Tuple[SplitLegQuote, ...]

    def __post_init__(self) -> None:
        amount_in_total = _positive_int(self.amount_in_total, name="amount_in_total")
        amount_out_total = _positive_int(self.amount_out_total, name="amount_out_total")
        if not self.legs:
            raise ValueError("split quote must contain at least one leg")
        seen: set[str] = set()
        total_in = 0
        total_out = 0
        for leg in self.legs:
            if leg.pool_id in seen:
                raise ValueError("split quote must not repeat pool_id")
            seen.add(leg.pool_id)
            total_in += int(leg.amount_in)
            total_out += int(leg.amount_out)
        if total_in != amount_in_total:
            raise ValueError("amount_in_total must equal sum of leg inputs")
        if total_out != amount_out_total:
            raise ValueError("amount_out_total must equal sum of leg outputs")


@dataclass(frozen=True)
class SplitLegExactOutQuote:
    pool_id: str
    amount_out: Amount
    amount_in: Amount

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        _positive_int(self.amount_out, name="amount_out")
        _positive_int(self.amount_in, name="amount_in")


@dataclass(frozen=True)
class SplitManyPoolsExactOutQuote:
    amount_out_total: Amount
    amount_in_total: Amount
    legs: Tuple[SplitLegExactOutQuote, ...]

    def __post_init__(self) -> None:
        amount_out_total = _positive_int(self.amount_out_total, name="amount_out_total")
        amount_in_total = _positive_int(self.amount_in_total, name="amount_in_total")
        if not self.legs:
            raise ValueError("split quote must contain at least one leg")
        seen: set[str] = set()
        total_out = 0
        total_in = 0
        for leg in self.legs:
            if leg.pool_id in seen:
                raise ValueError("split quote must not repeat pool_id")
            seen.add(leg.pool_id)
            total_out += int(leg.amount_out)
            total_in += int(leg.amount_in)
        if total_out != amount_out_total:
            raise ValueError("amount_out_total must equal sum of leg outputs")
        if total_in != amount_in_total:
            raise ValueError("amount_in_total must equal sum of leg inputs")


@dataclass(frozen=True)
class ExactOutCapacityGuard:
    amount_out_total: Amount
    max_legs: int
    top_caps: Tuple[Tuple[str, Amount], ...]
    capacity_upper_bound: Amount

    def __post_init__(self) -> None:
        _positive_int(self.amount_out_total, name="amount_out_total")
        max_legs = _positive_int(self.max_legs, name="max_legs")
        if len(self.top_caps) > max_legs:
            raise ValueError("top_caps must not exceed max_legs")
        seen: set[str] = set()
        total = 0
        for pool_id, cap in self.top_caps:
            if not pool_id:
                raise ValueError("top_caps pool_id must be non-empty")
            if pool_id in seen:
                raise ValueError("top_caps must not repeat pool_id")
            cap_i = _positive_int(cap, name="top_caps capacities")
            seen.add(pool_id)
            total += cap_i
        if total != _int_not_bool(self.capacity_upper_bound, name="capacity_upper_bound"):
            raise ValueError("capacity_upper_bound must equal sum of top_caps")

    @property
    def feasible(self) -> bool:
        return int(self.capacity_upper_bound) >= int(self.amount_out_total)


@dataclass(frozen=True, order=True)
class ExactOutRouteCanonicalKey:
    amount_in_total: Amount
    leg_count: int
    legs_lex: Tuple[Tuple[str, Amount], ...]

    def __post_init__(self) -> None:
        _positive_int(self.amount_in_total, name="amount_in_total")
        leg_count = _positive_int(self.leg_count, name="leg_count")
        if len(self.legs_lex) != leg_count:
            raise ValueError("leg_count must equal len(legs_lex)")
        if tuple(sorted(self.legs_lex, key=lambda item: item[0])) != self.legs_lex:
            raise ValueError("legs_lex must be sorted by pool_id")
        seen: set[str] = set()
        for pool_id, amount_out in self.legs_lex:
            if not pool_id:
                raise ValueError("legs_lex pool_id must be non-empty")
            if pool_id in seen:
                raise ValueError("legs_lex must not repeat pool_id")
            _positive_int(amount_out, name="legs_lex amounts")
            seen.add(pool_id)


def exact_out_route_canonical_key_for_legs(
    *,
    amount_in_total: Amount,
    legs: Sequence[Tuple[str, Amount]],
) -> ExactOutRouteCanonicalKey:
    legs_lex = tuple(sorted(((str(pool_id), amount_out) for pool_id, amount_out in legs), key=lambda item: item[0]))
    return ExactOutRouteCanonicalKey(
        amount_in_total=amount_in_total,
        leg_count=len(legs_lex),
        legs_lex=legs_lex,
    )


def exact_out_route_canonical_key(quote: SplitManyPoolsExactOutQuote) -> ExactOutRouteCanonicalKey:
    return exact_out_route_canonical_key_for_legs(
        amount_in_total=int(quote.amount_in_total),
        legs=tuple((leg.pool_id, int(leg.amount_out)) for leg in quote.legs),
    )
