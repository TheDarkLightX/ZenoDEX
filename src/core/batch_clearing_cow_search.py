"""CoW pair candidate partitioning and selection for batch clearing."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from typing import Callable, Dict, List, Tuple

from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .domain_limits import is_strict_int
from .neutral_tiebreak import tiebreak_token


@dataclass(frozen=True)
class _CowCandidateExactIn:
    intent: Intent
    amount_in: int
    min_amount_out: int
    sender: PubKey
    recipient: PubKey
    asset_in: AssetId
    asset_out: AssetId


@dataclass(frozen=True)
class _CowCandidateFields:
    amount_in: int
    min_amount_out: int
    sender: PubKey
    recipient: PubKey
    asset_in: AssetId
    asset_out: AssetId


@dataclass(frozen=True)
class _CowPartition:
    side_01: List[_CowCandidateExactIn]
    side_10: List[_CowCandidateExactIn]
    remaining: List[Intent]


@dataclass(frozen=True)
class _CowSelectionContext:
    balances: BalanceTable
    asset0: AssetId
    asset1: AssetId
    seed: bytes | None = None


@dataclass(frozen=True)
class _CowSearchState:
    side01_index: int
    used_side10_indices: set[int]
    debits_asset0: Dict[PubKey, int]
    debits_asset1: Dict[PubKey, int]
    pairs: List["_CowPair"]


@dataclass(frozen=True)
class _CowBruteforceContext:
    side_01: List[_CowCandidateExactIn]
    side_10: List[_CowCandidateExactIn]
    bal0: Dict[PubKey, int]
    bal1: Dict[PubKey, int]


@dataclass(frozen=True)
class _CowPairAttempt:
    side10_index: int
    x: _CowCandidateExactIn
    y: _CowCandidateExactIn
    cur_deb0: int
    cur_deb1: int


_CowPair = tuple[_CowCandidateExactIn, _CowCandidateExactIn]
_CowPairSelectionKey = tuple[int, int, Tuple[Tuple[str, str], ...]]
_COW_BRUTE_FORCE_CAP = 8
_COW_COUPLED_EXACT_DP_CAP = 14


def _partition_cow_candidates(
    swap_intents: List[Intent],
    pool_state: PoolState,
    *,
    seed: bytes | None = None,
) -> _CowPartition:
    side_01: List[_CowCandidateExactIn] = []
    side_10: List[_CowCandidateExactIn] = []
    remaining: List[Intent] = []

    for intent in swap_intents:
        candidate = _candidate_from_intent(intent, pool_state)
        if candidate is None:
            remaining.append(intent)
        elif candidate.asset_in == pool_state.asset0:
            side_01.append(candidate)
        else:
            side_10.append(candidate)

    side_01.sort(key=lambda c: tiebreak_token(c.intent.intent_id, seed))
    side_10.sort(key=lambda c: tiebreak_token(c.intent.intent_id, seed))
    return _CowPartition(side_01=side_01, side_10=side_10, remaining=remaining)


def _select_cow_pairs(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    if len(side_01) + len(side_10) <= _COW_BRUTE_FORCE_CAP:
        return _select_cow_pairs_bruteforce(
            side_01,
            side_10,
            context=context,
        )
    if _assignment_balance_safe(side_01, side_10, context=context):
        return _select_cow_pairs_assignment(side_01, side_10, context=context)
    if len(side_01) + len(side_10) <= _COW_COUPLED_EXACT_DP_CAP:
        return _select_cow_pairs_capacity_dp(side_01, side_10, context=context)
    return _select_cow_pairs_greedy(side_01, side_10, context=context)


def _candidate_from_intent(intent: Intent, pool_state: PoolState) -> _CowCandidateExactIn | None:
    if not _is_cow_exact_in_for_pool(intent, pool_state):
        return None
    fields = _read_cow_candidate_fields(intent)
    if fields is None:
        return None
    return _candidate_for_pool_direction(intent, fields, pool_state)


def _is_cow_exact_in_for_pool(intent: Intent, pool_state: PoolState) -> bool:
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return False
    return intent.get_field("pool_id") == pool_state.pool_id


def _read_cow_candidate_fields(intent: Intent) -> _CowCandidateFields | None:
    assets = _read_cow_assets(intent)
    if assets is None:
        return None
    amounts = _read_cow_amounts(intent)
    if amounts is None:
        return None
    recipient = _read_cow_recipient(intent)
    if recipient is None:
        return None
    asset_in, asset_out = assets
    amount_in, min_amount_out = amounts
    return _CowCandidateFields(
        amount_in=amount_in,
        min_amount_out=min_amount_out,
        sender=intent.sender_pubkey,
        recipient=recipient,
        asset_in=asset_in,
        asset_out=asset_out,
    )


def _read_cow_assets(intent: Intent) -> tuple[AssetId, AssetId] | None:
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str):
        return None
    if not isinstance(asset_out, str):
        return None
    return asset_in, asset_out


def _read_cow_amounts(intent: Intent) -> tuple[int, int] | None:
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not _is_positive_int(amount_in):
        return None
    if not _is_nonnegative_int(min_out):
        return None
    return int(amount_in), int(min_out)


def _read_cow_recipient(intent: Intent) -> PubKey | None:
    recipient = intent.get_field("recipient", intent.sender_pubkey)
    if not isinstance(recipient, str):
        return None
    if not recipient:
        return None
    return recipient


def _is_positive_int(value: object) -> bool:
    return is_strict_int(value) and int(value) > 0


def _is_nonnegative_int(value: object) -> bool:
    return is_strict_int(value) and int(value) >= 0


def _candidate_for_pool_direction(
    intent: Intent,
    fields: _CowCandidateFields,
    pool_state: PoolState,
) -> _CowCandidateExactIn | None:
    if fields.asset_in == pool_state.asset0 and fields.asset_out == pool_state.asset1:
        return _cow_candidate_exact_in(intent, fields, pool_state.asset0, pool_state.asset1)
    if fields.asset_in == pool_state.asset1 and fields.asset_out == pool_state.asset0:
        return _cow_candidate_exact_in(intent, fields, pool_state.asset1, pool_state.asset0)
    return None


def _cow_candidate_exact_in(
    intent: Intent,
    fields: _CowCandidateFields,
    asset_in: AssetId,
    asset_out: AssetId,
) -> _CowCandidateExactIn:
    return _CowCandidateExactIn(
        intent=intent,
        amount_in=fields.amount_in,
        min_amount_out=fields.min_amount_out,
        sender=fields.sender,
        recipient=fields.recipient,
        asset_in=asset_in,
        asset_out=asset_out,
    )


def _select_cow_pairs_bruteforce(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    best_pairs: List[_CowPair] = []
    best_key: _CowPairSelectionKey | None = None
    bal0 = _sender_asset_balances(side_01, context.balances, context.asset0)
    bal1 = _sender_asset_balances(side_10, context.balances, context.asset1)
    brute_context = _CowBruteforceContext(side_01=side_01, side_10=side_10, bal0=bal0, bal1=bal1)

    def rec(state: _CowSearchState) -> None:
        nonlocal best_pairs, best_key
        if state.side01_index >= len(side_01):
            key = _cow_pair_selection_key(state.pairs, seed=context.seed)
            if _is_better_cow_pair_key(key, best_key):
                best_key = key
                best_pairs = list(state.pairs)
            return

        rec(_skip_side01_candidate(state))
        _try_pair_side01_candidate(
            state,
            context=brute_context,
            rec=rec,
        )

    rec(_CowSearchState(0, set(), {}, {}, []))
    return best_pairs


def _select_cow_pairs_greedy(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    best_pairs: List[_CowPair] = []
    side_01_sorted = sorted(
        side_01,
        key=lambda c: (-c.min_amount_out, tiebreak_token(c.intent.intent_id, context.seed)),
    )
    side_10_pool = list(side_10)
    deb0: Dict[PubKey, int] = defaultdict(int)
    deb1: Dict[PubKey, int] = defaultdict(int)

    for x in side_01_sorted:
        if deb0[x.sender] + x.amount_in > int(context.balances.get(x.sender, context.asset0)):
            continue
        best_j, best_y = _best_greedy_counterparty(
            x,
            side_10_pool=side_10_pool,
            debits_asset1=deb1,
            context=context,
        )
        if best_j is None or best_y is None:
            continue
        deb0[x.sender] += x.amount_in
        deb1[best_y.sender] += best_y.amount_in
        best_pairs.append((x, best_y))
        side_10_pool.pop(best_j)

    return best_pairs


def _select_cow_pairs_capacity_dp(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    """Exact bounded DP for CoW matching with per-sender capacity coupling.

    State is the processed left prefix, used right-side mask, and aggregate
    debits per sender/asset. This preserves the brute-force objective while
    avoiding permutation-style repeated exploration on the coupled fallback
    surface.
    """
    if not side_01 or not side_10:
        return []
    senders0 = tuple(sorted({candidate.sender for candidate in side_01}))
    senders1 = tuple(sorted({candidate.sender for candidate in side_10}))
    sender0_index = {sender: idx for idx, sender in enumerate(senders0)}
    sender1_index = {sender: idx for idx, sender in enumerate(senders1)}
    caps0 = tuple(int(context.balances.get(sender, context.asset0)) for sender in senders0)
    caps1 = tuple(int(context.balances.get(sender, context.asset1)) for sender in senders1)

    def _pairs_from_indices(index_pairs: tuple[tuple[int, int], ...]) -> List[_CowPair]:
        return [(side_01[i], side_10[j]) for i, j in index_pairs]

    def _is_better_index_pairs(
        candidate: tuple[tuple[int, int], ...],
        best: tuple[tuple[int, int], ...],
    ) -> bool:
        return _is_better_cow_pair_key(
            _cow_pair_selection_key(_pairs_from_indices(candidate), seed=context.seed),
            _cow_pair_selection_key(_pairs_from_indices(best), seed=context.seed),
        )

    @lru_cache(maxsize=None)
    def rec(
        side01_index: int,
        used_side10_mask: int,
        debits0: tuple[int, ...],
        debits1: tuple[int, ...],
    ) -> tuple[tuple[int, int], ...]:
        if side01_index >= len(side_01):
            return ()

        best = rec(side01_index + 1, used_side10_mask, debits0, debits1)
        x = side_01[side01_index]
        x_sender_index = sender0_index[x.sender]
        next_x_debit = int(debits0[x_sender_index]) + int(x.amount_in)
        if next_x_debit > int(caps0[x_sender_index]):
            return best

        for side10_index, y in enumerate(side_10):
            if used_side10_mask & (1 << side10_index):
                continue
            if not _pair_feasible(x, y):
                continue
            y_sender_index = sender1_index[y.sender]
            next_y_debit = int(debits1[y_sender_index]) + int(y.amount_in)
            if next_y_debit > int(caps1[y_sender_index]):
                continue
            next_debits0 = list(debits0)
            next_debits1 = list(debits1)
            next_debits0[x_sender_index] = next_x_debit
            next_debits1[y_sender_index] = next_y_debit
            candidate = (
                (side01_index, side10_index),
                *rec(
                    side01_index + 1,
                    used_side10_mask | (1 << side10_index),
                    tuple(next_debits0),
                    tuple(next_debits1),
                ),
            )
            if _is_better_index_pairs(candidate, best):
                best = candidate
        return best

    index_pairs = rec(0, 0, tuple(0 for _ in senders0), tuple(0 for _ in senders1))
    return _pairs_from_indices(index_pairs)


def _assignment_balance_safe(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> bool:
    """Return True when candidate matching cannot violate aggregate balances.

    The CoW pair graph is a pure bipartite matching problem only when selecting
    every candidate from a sender would still fit that sender's balance. If a
    sender is capacity-coupled across multiple intents, the problem includes a
    knapsack-style side constraint and must stay on the fail-closed greedy path.
    """
    debits_asset0: Dict[PubKey, int] = defaultdict(int)
    debits_asset1: Dict[PubKey, int] = defaultdict(int)
    for candidate in side_01:
        debits_asset0[candidate.sender] += int(candidate.amount_in)
    for candidate in side_10:
        debits_asset1[candidate.sender] += int(candidate.amount_in)
    for sender, amount in debits_asset0.items():
        if amount > int(context.balances.get(sender, context.asset0)):
            return False
    for sender, amount in debits_asset1.items():
        if amount > int(context.balances.get(sender, context.asset1)):
            return False
    return True


def _select_cow_pairs_assignment(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    """Exact maximum-weight bipartite matching for uncoupled CoW candidates.

    The objective preserves the production priority of maximizing netted volume
    first and surplus second. The final mixed-radix layer exactly encodes the
    canonical lexicographic pair-id tie used by the small brute-force oracle.
    """
    if not side_01 or not side_10:
        return []

    n_left = len(side_01)
    n_right = len(side_10)
    size = n_left + n_right
    pair_ranks = _cow_pair_rank_map(side_01, side_10, seed=context.seed)
    pair_tie_values = _cow_pair_lex_tie_values(pair_ranks, max_pairs=min(n_left, n_right))
    max_tie_bonus = sum(sorted(pair_tie_values.values(), reverse=True)[: min(n_left, n_right)])
    max_total_volume = sum(int(candidate.amount_in) for candidate in side_01)
    max_total_volume += sum(int(candidate.amount_in) for candidate in side_10)
    tie_scale = max_tie_bonus + 1
    volume_scale = (max_total_volume + 1) * tie_scale
    max_edge_score = max(1, max_total_volume * volume_scale + max_total_volume * tie_scale + max_tie_bonus)
    impossible_cost = max_edge_score * (size + 1)

    costs = [[0 for _ in range(size)] for _ in range(size)]
    for i, x in enumerate(side_01):
        for j, y in enumerate(side_10):
            if not _pair_feasible(x, y):
                costs[i][j] = impossible_cost
                continue
            volume = int(x.amount_in + y.amount_in)
            surplus = int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out)
            tie_bonus = pair_tie_values[(i, j)]
            score = volume * volume_scale + surplus * tie_scale + tie_bonus
            costs[i][j] = -score

    assignment = _hungarian_min_assignment(costs)
    pairs: List[_CowPair] = []
    for i, j in enumerate(assignment[:n_left]):
        if 0 <= j < n_right and costs[i][j] < 0:
            pairs.append((side_01[i], side_10[j]))
    return pairs


def _cow_pair_rank_map(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    seed: bytes | None,
) -> Dict[tuple[int, int], int]:
    ranked_pairs = sorted(
        ((tiebreak_token(x.intent.intent_id, seed), tiebreak_token(y.intent.intent_id, seed), i, j)
         for i, x in enumerate(side_01)
         for j, y in enumerate(side_10))
    )
    return {(i, j): rank for rank, (_x_token, _y_token, i, j) in enumerate(ranked_pairs)}


def _cow_pair_lex_tie_values(
    pair_ranks: Dict[tuple[int, int], int],
    *,
    max_pairs: int,
) -> Dict[tuple[int, int], int]:
    """Return additive bonuses that exactly preserve sorted pair-id lex order.

    A base of ``max_pairs + 1`` makes one earlier-ranked edge dominate every
    possible combination of later-ranked edges in a matching. That turns the
    additive Hungarian score into the same final tie relation used by
    ``_cow_pair_selection_key`` after volume and surplus are fixed.
    """
    if not pair_ranks:
        return {}
    base = max(2, int(max_pairs) + 1)
    edge_count = len(pair_ranks)
    return {
        pair: base ** (edge_count - int(rank) - 1)
        for pair, rank in pair_ranks.items()
    }


def _hungarian_min_assignment(costs: List[List[int]]) -> List[int]:
    """Return a minimum-cost column assignment for each row of a square matrix."""
    n = len(costs)
    if n == 0:
        return []
    if any(len(row) != n for row in costs):
        raise ValueError("hungarian costs must be square")
    max_abs_cost = max(abs(int(value)) for row in costs for value in row)
    unreachable = max_abs_cost * (n + 1) + 1

    u = [0] * (n + 1)
    v = [0] * (n + 1)
    p = [0] * (n + 1)
    way = [0] * (n + 1)
    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [0] + [unreachable] * n
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = unreachable
            j1 = 0
            for j in range(1, n + 1):
                if used[j]:
                    continue
                cur = costs[i0 - 1][j - 1] - u[i0] - v[j]
                if cur < minv[j]:
                    minv[j] = cur
                    way[j] = j0
                if minv[j] < delta:
                    delta = minv[j]
                    j1 = j
            for j in range(0, n + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break

    assignment = [-1] * n
    for j in range(1, n + 1):
        if p[j] != 0:
            assignment[p[j] - 1] = j - 1
    return assignment


def _try_pair_side01_candidate(
    state: _CowSearchState,
    *,
    context: _CowBruteforceContext,
    rec: Callable[[_CowSearchState], None],
) -> None:
    for j, _y in enumerate(context.side_10):
        attempt = _pair_attempt_for_side10_index(state, context, j)
        if attempt is not None:
            rec(_paired_search_state(state, attempt))


def _pair_attempt_for_side10_index(
    state: _CowSearchState,
    context: _CowBruteforceContext,
    side10_index: int,
) -> _CowPairAttempt | None:
    x = context.side_01[state.side01_index]
    cur_deb0 = int(state.debits_asset0.get(x.sender, 0))
    if cur_deb0 + x.amount_in > int(context.bal0.get(x.sender, 0)):
        return None
    if side10_index in state.used_side10_indices:
        return None
    y = context.side_10[side10_index]
    if not _pair_feasible(x, y):
        return None
    cur_deb1 = int(state.debits_asset1.get(y.sender, 0))
    if cur_deb1 + y.amount_in > int(context.bal1.get(y.sender, 0)):
        return None
    return _CowPairAttempt(
        side10_index=side10_index,
        x=x,
        y=y,
        cur_deb0=cur_deb0,
        cur_deb1=cur_deb1,
    )


def _paired_search_state(
    state: _CowSearchState,
    attempt: _CowPairAttempt,
) -> _CowSearchState:
    used_side10_indices = set(state.used_side10_indices)
    debits_asset0 = dict(state.debits_asset0)
    debits_asset1 = dict(state.debits_asset1)
    used_side10_indices.add(attempt.side10_index)
    debits_asset0[attempt.x.sender] = attempt.cur_deb0 + attempt.x.amount_in
    debits_asset1[attempt.y.sender] = attempt.cur_deb1 + attempt.y.amount_in
    return _CowSearchState(
        side01_index=int(state.side01_index) + 1,
        used_side10_indices=used_side10_indices,
        debits_asset0=debits_asset0,
        debits_asset1=debits_asset1,
        pairs=[*state.pairs, (attempt.x, attempt.y)],
    )


def _best_greedy_counterparty(
    x: _CowCandidateExactIn,
    *,
    side_10_pool: List[_CowCandidateExactIn],
    debits_asset1: Dict[PubKey, int],
    context: _CowSelectionContext,
) -> tuple[int | None, _CowCandidateExactIn | None]:
    best_j: int | None = None
    best_y: _CowCandidateExactIn | None = None
    for j, y in enumerate(side_10_pool):
        if not _pair_feasible(x, y):
            continue
        if debits_asset1[y.sender] + y.amount_in > int(context.balances.get(y.sender, context.asset1)):
            continue
        candidate_key = (y.amount_in, tiebreak_token(y.intent.intent_id, context.seed))
        if _is_better_greedy_counterparty(candidate_key, best_y, context.seed):
            best_j, best_y = j, y
    return best_j, best_y


def _is_better_greedy_counterparty(
    candidate_key: tuple[int, Tuple[str, str]],
    best_y: _CowCandidateExactIn | None,
    seed: bytes | None,
) -> bool:
    if best_y is None:
        return True
    best_key = (best_y.amount_in, tiebreak_token(best_y.intent.intent_id, seed))
    return candidate_key < best_key


def _cow_pair_selection_key(pairs: List[_CowPair], *, seed: bytes | None = None) -> _CowPairSelectionKey:
    volume = sum(int(x.amount_in + y.amount_in) for x, y in pairs)
    surplus = sum(int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out) for x, y in pairs)
    pair_ids = tuple(sorted(
        (tiebreak_token(x.intent.intent_id, seed), tiebreak_token(y.intent.intent_id, seed))
        for x, y in pairs
    ))
    return int(volume), int(surplus), pair_ids


def _is_better_cow_pair_key(
    candidate: _CowPairSelectionKey,
    best: _CowPairSelectionKey | None,
) -> bool:
    if best is None:
        return True
    cand_volume, cand_surplus, cand_pair_ids = candidate
    best_volume, best_surplus, best_pair_ids = best
    if cand_volume != best_volume:
        return cand_volume > best_volume
    if cand_surplus != best_surplus:
        return cand_surplus > best_surplus
    return cand_pair_ids < best_pair_ids


def _pair_feasible(x: _CowCandidateExactIn, y: _CowCandidateExactIn) -> bool:
    return y.amount_in >= x.min_amount_out and x.amount_in >= y.min_amount_out


def _sender_asset_balances(
    candidates: List[_CowCandidateExactIn],
    balances: BalanceTable,
    asset: AssetId,
) -> Dict[PubKey, int]:
    return {candidate.sender: int(balances.get(candidate.sender, asset)) for candidate in candidates}


def _skip_side01_candidate(state: _CowSearchState) -> _CowSearchState:
    return _CowSearchState(
        side01_index=int(state.side01_index) + 1,
        used_side10_indices=state.used_side10_indices,
        debits_asset0=state.debits_asset0,
        debits_asset1=state.debits_asset1,
        pairs=state.pairs,
    )
