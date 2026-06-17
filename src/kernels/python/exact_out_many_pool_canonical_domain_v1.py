from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ...core.domain_limits import is_strict_int
from ...state.pools import PoolState

DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES = 20_000


def _require_positive_int(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _require_u64(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise ValueError(f"{name} out of range")
    out = int(value)
    if out < 0 or out > 0xFFFFFFFFFFFFFFFF:
        raise ValueError(f"{name} out of range")
    return out


@dataclass(frozen=True)
class ExactOutManyPoolFeasiblePoolRow:
    pool_id: str
    cap_out: int
    probe_amount_out: int
    probe_amount_in: int
    scaled_unit_cost_u64: int

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        cap_out = _require_positive_int(self.cap_out, name="cap_out")
        probe_amount_out = _require_positive_int(self.probe_amount_out, name="probe_amount_out")
        _require_positive_int(self.probe_amount_in, name="probe_amount_in")
        if probe_amount_out > cap_out:
            raise ValueError("probe_amount_out must not exceed cap_out")
        _require_u64(self.scaled_unit_cost_u64, name="scaled_unit_cost_u64")


@dataclass(frozen=True)
class ExactOutManyPoolCandidateLeg:
    pool_id: str
    amount_out: int
    amount_in: int

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        _require_positive_int(self.amount_out, name="amount_out")
        _require_positive_int(self.amount_in, name="amount_in")


@dataclass(frozen=True)
class ExactOutManyPoolCandidateQuote:
    amount_out_total: int
    amount_in_total: int
    legs: tuple[ExactOutManyPoolCandidateLeg, ...]

    def __post_init__(self) -> None:
        amount_out_total = _require_positive_int(self.amount_out_total, name="amount_out_total")
        amount_in_total = _require_positive_int(self.amount_in_total, name="amount_in_total")
        if not self.legs:
            raise ValueError("legs must be non-empty")
        seen: set[str] = set()
        total_out = 0
        total_in = 0
        for leg in self.legs:
            if leg.pool_id in seen:
                raise ValueError("legs must not repeat pool_id")
            seen.add(leg.pool_id)
            total_out += int(leg.amount_out)
            total_in += int(leg.amount_in)
        if total_out != amount_out_total:
            raise ValueError("amount_out_total must equal sum of leg outputs")
        if total_in != amount_in_total:
            raise ValueError("amount_in_total must equal sum of leg inputs")


@dataclass(frozen=True, order=True)
class ExactOutManyPoolCanonicalKey:
    amount_in_total: int
    leg_count: int
    legs_lex: tuple[tuple[str, int], ...]

    def __post_init__(self) -> None:
        _require_positive_int(self.amount_in_total, name="amount_in_total")
        leg_count = _require_positive_int(self.leg_count, name="leg_count")
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
            _require_positive_int(amount_out, name="legs_lex amounts")
            seen.add(pool_id)


@dataclass(frozen=True)
class ExactOutManyPoolSelectedDomain:
    selected_pool_ids: tuple[str, ...]
    candidates: tuple[ExactOutManyPoolCandidateQuote, ...]
    canonical_quote: ExactOutManyPoolCandidateQuote

    def __post_init__(self) -> None:
        if not self.selected_pool_ids:
            raise ValueError("selected_pool_ids must be non-empty")
        if tuple(sorted(self.selected_pool_ids)) != self.selected_pool_ids:
            raise ValueError("selected_pool_ids must be sorted")
        if not self.candidates:
            raise ValueError("candidates must be non-empty")


def pool_reserves_for_exact_out(pool: PoolState, *, asset_in: str, asset_out: str) -> tuple[int, int] | None:
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def feasible_exact_out_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
) -> list[tuple[PoolState, int, int]]:
    from ...core.amm_dispatch import swap_exact_out_for_pool

    feasible: list[tuple[PoolState, int, int]] = []
    target_out = _require_positive_int(amount_out_total, name="amount_out_total")
    for pool in pools:
        reserves = pool_reserves_for_exact_out(pool, asset_in=asset_in, asset_out=asset_out)
        if reserves is None:
            continue
        _reserve_in, reserve_out = reserves
        cap = int(reserve_out) - 1
        if cap <= 0:
            continue
        out_i = min(int(target_out), int(cap))
        try:
            in_i, _ = swap_exact_out_for_pool(
                pool,
                reserve_in=int(reserves[0]),
                reserve_out=int(reserves[1]),
                amount_out=int(out_i),
            )
        except ValueError:
            continue
        feasible.append((pool, int(cap), int(in_i)))
    return feasible


def rank_exact_out_feasible_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
) -> tuple[ExactOutManyPoolFeasiblePoolRow, ...]:
    target_out = _require_positive_int(amount_out_total, name="amount_out_total")
    feasible = feasible_exact_out_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=target_out,
    )
    if not feasible:
        raise ValueError("no feasible pools for exact-out split")

    rows = [
        ExactOutManyPoolFeasiblePoolRow(
            pool_id=pool.pool_id,
            cap_out=int(cap),
            probe_amount_out=int(min(int(target_out), int(cap))),
            probe_amount_in=int(in_i),
            scaled_unit_cost_u64=int((int(in_i) * 1_000_000) // max(1, int(min(int(target_out), int(cap))))),
        )
        for pool, cap, in_i in feasible
    ]
    return tuple(
        sorted(
            rows,
            key=lambda row: (int(row.scaled_unit_cost_u64), int(row.probe_amount_in), row.pool_id),
        )
    )


def select_many_pool_audit_candidates(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_candidate_pools: int,
) -> tuple[PoolState, ...]:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    rows = rank_exact_out_feasible_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
    )
    pools_by_id = {pool.pool_id: pool for pool in pools}

    candidates: list[PoolState] = []
    caps: dict[str, int] = {}
    for row in rows:
        if row.pool_id in caps:
            continue
        pool = pools_by_id[row.pool_id]
        candidates.append(pool)
        caps[row.pool_id] = int(row.cap_out)
        if len(candidates) >= max_candidate_pools_i:
            break
        top_caps = sorted(caps.values(), reverse=True)
        if sum(top_caps[: min(max_legs_i, len(top_caps))]) >= amount_out_total_i and len(candidates) >= min(
            max_legs_i, len(rows)
        ):
            break

    if not candidates:
        raise ValueError("no feasible candidates for exact-out split")
    return tuple(sorted(candidates, key=lambda pool: pool.pool_id))


def exact_out_many_pool_canonical_key_for_legs(
    *,
    amount_in_total: int,
    legs: Sequence[tuple[str, int]],
) -> ExactOutManyPoolCanonicalKey:
    legs_lex = tuple(sorted(((str(pool_id), amount_out) for pool_id, amount_out in legs), key=lambda item: item[0]))
    return ExactOutManyPoolCanonicalKey(
        amount_in_total=amount_in_total,
        leg_count=len(legs_lex),
        legs_lex=legs_lex,
    )


def exact_out_many_pool_canonical_key(
    quote: ExactOutManyPoolCandidateQuote,
) -> ExactOutManyPoolCanonicalKey:
    return exact_out_many_pool_canonical_key_for_legs(
        amount_in_total=int(quote.amount_in_total),
        legs=tuple((leg.pool_id, int(leg.amount_out)) for leg in quote.legs),
    )


def select_exact_out_many_pool_canonical_quote(
    quotes: Sequence[ExactOutManyPoolCandidateQuote],
) -> ExactOutManyPoolCandidateQuote:
    if not quotes:
        raise ValueError("quotes must be non-empty")
    return min(quotes, key=exact_out_many_pool_canonical_key)


def build_exact_out_many_pool_selected_domain(
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_enumerated_candidates: int = DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES,
) -> ExactOutManyPoolSelectedDomain:
    target_out = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    if not selected_pools:
        raise ValueError("selected_pools must be non-empty")

    pools_by_id = {pool.pool_id: pool for pool in selected_pools}
    pool_ids = tuple(sorted(pools_by_id.keys()))
    if len(pool_ids) != len(selected_pools):
        raise ValueError("selected_pools must not repeat pool_id")

    max_out: dict[str, int] = {}
    reserves_by_id: dict[str, tuple[int, int]] = {}
    for pool_id in pool_ids:
        reserves = pool_reserves_for_exact_out(pools_by_id[pool_id], asset_in=asset_in, asset_out=asset_out)
        if reserves is None:
            continue
        reserves_by_id[pool_id] = (int(reserves[0]), int(reserves[1]))
        max_out[pool_id] = max(0, int(reserves[1]) - 1)

    from ...core.amm_dispatch import swap_exact_out_for_pool

    quote_cache: dict[tuple[str, int], int | None] = {}

    def quote_in(pool_id: str, amount_out: int) -> int | None:
        if int(amount_out) < 0:
            return None
        if int(amount_out) == 0:
            return 0
        if int(amount_out) > int(max_out.get(pool_id, 0)):
            return None
        key = (pool_id, int(amount_out))
        if key in quote_cache:
            return quote_cache[key]
        reserves = reserves_by_id.get(pool_id)
        if reserves is None:
            quote_cache[key] = None
            return None
        try:
            amount_in, _ = swap_exact_out_for_pool(
                pools_by_id[pool_id],
                reserve_in=int(reserves[0]),
                reserve_out=int(reserves[1]),
                amount_out=int(amount_out),
            )
        except ValueError:
            quote_cache[key] = None
            return None
        quote_cache[key] = int(amount_in)
        return int(amount_in)

    candidate_quotes: list[ExactOutManyPoolCandidateQuote] = []
    # Cache the "best possible capacity from this suffix" bound used by every
    # recursive branch. Recomputing it in-place is observationally identical but
    # turns the pruning guard into repeated sort work on the hot path.
    suffix_capacity_sums: list[tuple[int, ...]] = []
    for start_index in range(len(pool_ids) + 1):
        sorted_caps = sorted(
            (int(max_out.get(pool_id, 0)) for pool_id in pool_ids[start_index:]),
            reverse=True,
        )
        prefix_sums = [0]
        for cap in sorted_caps:
            prefix_sums.append(prefix_sums[-1] + int(cap))
        suffix_capacity_sums.append(tuple(prefix_sums))

    def remaining_capacity(start_index: int, slots: int) -> int:
        if int(slots) <= 0:
            return 0
        prefix_sums = suffix_capacity_sums[min(int(start_index), len(pool_ids))]
        capped_slots = min(int(slots), len(prefix_sums) - 1)
        return int(prefix_sums[capped_slots])

    def recurse(
        start_index: int,
        remaining_out: int,
        legs_left: int,
        partial: list[tuple[str, int, int]],
        partial_amount_in_total: int,
    ) -> None:
        if len(candidate_quotes) > max_enumerated_candidates_i:
            raise ValueError("many-pool exact-out selected domain exceeded max_enumerated_candidates")
        if int(remaining_out) == 0:
            candidate_quotes.append(
                ExactOutManyPoolCandidateQuote(
                    amount_out_total=int(target_out),
                    amount_in_total=int(partial_amount_in_total),
                    legs=tuple(
                        ExactOutManyPoolCandidateLeg(
                            pool_id=pool_id,
                            amount_out=int(amount_out),
                            amount_in=int(amount_in),
                        )
                        for pool_id, amount_out, amount_in in partial
                    ),
                )
            )
            return
        if int(legs_left) <= 0 or start_index >= len(pool_ids):
            return
        if remaining_capacity(start_index, int(legs_left)) < int(remaining_out):
            return

        for idx in range(start_index, len(pool_ids)):
            pool_id = pool_ids[idx]
            cap = min(int(max_out.get(pool_id, 0)), int(remaining_out))
            if cap <= 0:
                continue
            future_max = remaining_capacity(idx + 1, int(legs_left) - 1)
            min_amount_out = int(remaining_out) if int(legs_left) == 1 else max(1, int(remaining_out) - int(future_max))
            for amount_out in range(int(min_amount_out), int(cap) + 1):
                amount_in = quote_in(pool_id, int(amount_out))
                if amount_in is None:
                    continue
                partial.append((pool_id, int(amount_out), int(amount_in)))
                recurse(
                    idx + 1,
                    int(remaining_out) - int(amount_out),
                    int(legs_left) - 1,
                    partial,
                    int(partial_amount_in_total) + int(amount_in),
                )
                partial.pop()

    recurse(0, int(target_out), max_legs_i, [], 0)
    if not candidate_quotes:
        raise ValueError("no feasible exact-out candidates in bounded selected domain")
    if len(candidate_quotes) > max_enumerated_candidates_i:
        raise ValueError("many-pool exact-out selected domain exceeded max_enumerated_candidates")

    return ExactOutManyPoolSelectedDomain(
        selected_pool_ids=pool_ids,
        candidates=tuple(candidate_quotes),
        canonical_quote=select_exact_out_many_pool_canonical_quote(candidate_quotes),
    )
