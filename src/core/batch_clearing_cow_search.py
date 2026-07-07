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


@dataclass(frozen=True)
class _CowComponent:
    side_01: List[_CowCandidateExactIn]
    side_10: List[_CowCandidateExactIn]


@dataclass(frozen=True)
class _CowSenderSlot:
    candidates: List[_CowCandidateExactIn]


@dataclass
class _CowFlowEdge:
    to: int
    rev: int
    cap: int
    cost: int


@dataclass(frozen=True)
class _CowComponentStatus:
    status: str
    raw_side_01_count: int
    raw_side_10_count: int
    pruned_side_01_count: int
    pruned_side_10_count: int
    raw_state_estimate: int
    pruned_state_estimate: int
    selected_pair_count: int
    selected_netted_volume: int
    selected_pair_intent_ids: Tuple[Tuple[str, str], ...]
    deferred_reason: str | None = None


@dataclass(frozen=True)
class _CowSelectionDiagnostics:
    pairs: List["_CowPair"]
    component_statuses: Tuple[_CowComponentStatus, ...]


_CowPair = tuple[_CowCandidateExactIn, _CowCandidateExactIn]
_CowPairSelectionKey = tuple[int, int, Tuple[Tuple[str, str], ...]]
_COW_BRUTE_FORCE_CAP = 8
_COW_COUPLED_EXACT_DP_CAP = 14
_COW_COUPLED_EXACT_DP_STATE_CAP = 65_536
_COW_ATOMIC_BMATCHING_EDGE_CAP = 512
_COW_ATOMIC_BMATCHING_FLOW_CAP = 512


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
    return _select_cow_pairs_with_status(side_01, side_10, context=context).pairs


def _select_cow_pairs_with_status(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> _CowSelectionDiagnostics:
    raw_side_01_count = len(side_01)
    raw_side_10_count = len(side_10)
    raw_state_estimate = _cow_capacity_dp_state_estimate(side_01, side_10)
    side_01, side_10 = _filter_individually_fundable_cow_candidates(
        side_01,
        side_10,
        context=context,
    )
    pruned_side_01_count = len(side_01)
    pruned_side_10_count = len(side_10)
    pruned_state_estimate = _cow_capacity_dp_state_estimate(side_01, side_10)

    def diagnostics(
        pairs: List[_CowPair],
        status: str,
        *,
        deferred_reason: str | None = None,
    ) -> _CowSelectionDiagnostics:
        if status.startswith("exact_") and (
            pruned_side_01_count != raw_side_01_count or pruned_side_10_count != raw_side_10_count
        ):
            status = "exact_after_prune_" + status.removeprefix("exact_")
        return _CowSelectionDiagnostics(
            pairs=pairs,
            component_statuses=(
                _cow_component_status(
                    status=status,
                    raw_side_01_count=raw_side_01_count,
                    raw_side_10_count=raw_side_10_count,
                    pruned_side_01_count=pruned_side_01_count,
                    pruned_side_10_count=pruned_side_10_count,
                    raw_state_estimate=raw_state_estimate,
                    pruned_state_estimate=pruned_state_estimate,
                    pairs=pairs,
                    deferred_reason=deferred_reason,
                    seed=context.seed,
                ),
            ),
        )

    if not side_01 or not side_10:
        return diagnostics([], "exact_no_counterparty", deferred_reason="no_opposite_side_candidate")
    if len(side_01) + len(side_10) <= _COW_BRUTE_FORCE_CAP:
        return diagnostics(
            _select_cow_pairs_bruteforce(
                side_01,
                side_10,
                context=context,
            ),
            "exact_bruteforce",
        )
    if _assignment_balance_safe(side_01, side_10, context=context):
        return diagnostics(
            _select_cow_pairs_assignment(side_01, side_10, context=context),
            "exact_assignment",
        )
    if pruned_state_estimate <= _COW_COUPLED_EXACT_DP_STATE_CAP:
        return diagnostics(
            _select_cow_pairs_capacity_dp(side_01, side_10, context=context),
            "exact_capacity_dp",
        )
    return _select_cow_pairs_large_coupled_defer_with_status(
        side_01,
        side_10,
        context=context,
    )


def _cow_component_status(
    *,
    status: str,
    raw_side_01_count: int,
    raw_side_10_count: int,
    pruned_side_01_count: int,
    pruned_side_10_count: int,
    raw_state_estimate: int,
    pruned_state_estimate: int,
    pairs: List[_CowPair],
    seed: bytes | None,
    deferred_reason: str | None = None,
) -> _CowComponentStatus:
    return _CowComponentStatus(
        status=status,
        raw_side_01_count=int(raw_side_01_count),
        raw_side_10_count=int(raw_side_10_count),
        pruned_side_01_count=int(pruned_side_01_count),
        pruned_side_10_count=int(pruned_side_10_count),
        raw_state_estimate=int(raw_state_estimate),
        pruned_state_estimate=int(pruned_state_estimate),
        selected_pair_count=len(pairs),
        selected_netted_volume=int(_cow_pair_selection_key(pairs, seed=seed)[0]),
        selected_pair_intent_ids=_selected_pair_intent_ids_from_pairs(pairs),
        deferred_reason=deferred_reason,
    )


def _selected_pair_intent_ids_from_pairs(
    pairs: List[_CowPair],
) -> Tuple[Tuple[str, str], ...]:
    return tuple(
        sorted(
            (
                x.intent.intent_id,
                y.intent.intent_id,
            )
            for x, y in pairs
        )
    )


def _filter_individually_fundable_cow_candidates(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> tuple[List[_CowCandidateExactIn], List[_CowCandidateExactIn]]:
    def is_fundable(candidate: _CowCandidateExactIn, asset: AssetId) -> bool:
        balance = int(context.balances.get(candidate.sender, asset))
        return int(candidate.amount_in) <= balance

    return (
        [candidate for candidate in side_01 if is_fundable(candidate, context.asset0)],
        [candidate for candidate in side_10 if is_fundable(candidate, context.asset1)],
    )


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


def _select_cow_pairs_large_coupled_defer(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    """Solve independent safe components and defer only large coupled components.

    This branch is reached only when the uncoupled Hungarian certificate is
    inapplicable and the exact coupled-capacity DP cap has been exceeded.
    A conservative conflict graph lets independent small components still use
    exact local solving while large coupled components stay on the normal
    batch-clearing path.
    """
    return _select_cow_pairs_large_coupled_defer_with_status(side_01, side_10, context=context).pairs


def _select_cow_pairs_large_coupled_defer_with_status(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> _CowSelectionDiagnostics:
    out: List[_CowPair] = []
    statuses: List[_CowComponentStatus] = []
    for component in _cow_conflict_components(side_01, side_10, context=context):
        result = _select_cow_component_pairs_with_status(component, context=context)
        out.extend(result.pairs)
        statuses.extend(result.component_statuses)
    return _CowSelectionDiagnostics(pairs=out, component_statuses=tuple(statuses))


def _cow_conflict_components(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowComponent]:
    node_count = len(side_01) + len(side_10)
    parent = list(range(node_count))

    def find(node: int) -> int:
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    def union(left: int, right: int) -> None:
        left_root = find(left)
        right_root = find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    for i, x in enumerate(side_01):
        for j, y in enumerate(side_10):
            if _pair_feasible(x, y):
                union(i, len(side_01) + j)

    _union_capacity_constrained_senders(
        side_01,
        asset=context.asset0,
        balances=context.balances,
        index_offset=0,
        union=union,
    )
    _union_capacity_constrained_senders(
        side_10,
        asset=context.asset1,
        balances=context.balances,
        index_offset=len(side_01),
        union=union,
    )

    grouped: Dict[int, tuple[List[_CowCandidateExactIn], List[_CowCandidateExactIn]]] = {}
    for index, candidate in enumerate(side_01):
        root = find(index)
        grouped.setdefault(root, ([], []))[0].append(candidate)
    for index, candidate in enumerate(side_10):
        root = find(len(side_01) + index)
        grouped.setdefault(root, ([], []))[1].append(candidate)

    return [
        _CowComponent(side_01=left, side_10=right)
        for left, right in grouped.values()
    ]


def _union_capacity_constrained_senders(
    candidates: List[_CowCandidateExactIn],
    *,
    asset: AssetId,
    balances: BalanceTable,
    index_offset: int,
    union: Callable[[int, int], None],
) -> None:
    by_sender: Dict[PubKey, List[int]] = defaultdict(list)
    demand_by_sender: Dict[PubKey, int] = defaultdict(int)
    for index, candidate in enumerate(candidates):
        by_sender[candidate.sender].append(index_offset + index)
        demand_by_sender[candidate.sender] += int(candidate.amount_in)

    for sender, indices in by_sender.items():
        if len(indices) <= 1:
            continue
        if demand_by_sender[sender] <= int(balances.get(sender, asset)):
            continue
        first = indices[0]
        for index in indices[1:]:
            union(first, index)


def _select_cow_component_pairs(
    component: _CowComponent,
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    return _select_cow_component_pairs_with_status(component, context=context).pairs


def _select_cow_component_pairs_with_status(
    component: _CowComponent,
    *,
    context: _CowSelectionContext,
) -> _CowSelectionDiagnostics:
    state_estimate = _cow_capacity_dp_state_estimate(component.side_01, component.side_10)

    def diagnostics(
        pairs: List[_CowPair],
        status: str,
        *,
        deferred_reason: str | None = None,
    ) -> _CowSelectionDiagnostics:
        return _CowSelectionDiagnostics(
            pairs=pairs,
            component_statuses=(
                _cow_component_status(
                    status=status,
                    raw_side_01_count=len(component.side_01),
                    raw_side_10_count=len(component.side_10),
                    pruned_side_01_count=len(component.side_01),
                    pruned_side_10_count=len(component.side_10),
                    raw_state_estimate=state_estimate,
                    pruned_state_estimate=state_estimate,
                    pairs=pairs,
                    deferred_reason=deferred_reason,
                    seed=context.seed,
                ),
            ),
        )

    if not component.side_01 or not component.side_10:
        return diagnostics([], "exact_no_counterparty", deferred_reason="no_opposite_side_candidate")
    if _assignment_balance_safe(component.side_01, component.side_10, context=context):
        return diagnostics(
            _select_cow_pairs_assignment(component.side_01, component.side_10, context=context),
            "exact_assignment",
        )
    if state_estimate <= _COW_COUPLED_EXACT_DP_STATE_CAP:
        return diagnostics(
            _select_cow_pairs_capacity_dp(component.side_01, component.side_10, context=context),
            "exact_capacity_dp",
        )
    bmatching_pairs = _select_cow_pairs_atomic_bmatching(component, context=context)
    if bmatching_pairs is not None:
        return diagnostics(bmatching_pairs, "exact_atomic_bmatching")
    slot_pairs = _select_cow_pairs_sender_slot_quotient(component, context=context)
    if slot_pairs is not None:
        return diagnostics(slot_pairs, "exact_sender_slot_quotient")
    star_pairs = _select_cow_pairs_single_choice_star(component, context=context)
    if star_pairs is not None:
        return diagnostics(star_pairs, "exact_single_choice_star")
    return diagnostics([], "deferred", deferred_reason="state_cap_exceeded_no_exact_quotient")


def _select_cow_pairs_sender_slot_quotient(
    component: _CowComponent,
    *,
    context: _CowSelectionContext,
) -> List[_CowPair] | None:
    left_slots = _cow_sender_slots(
        component.side_01,
        asset=context.asset0,
        balances=context.balances,
    )
    right_slots = _cow_sender_slots(
        component.side_10,
        asset=context.asset1,
        balances=context.balances,
    )
    if left_slots is None or right_slots is None:
        return None
    return _select_cow_slot_pairs(
        component.side_01,
        component.side_10,
        left_slots,
        right_slots,
        context=context,
    )


def _select_cow_pairs_atomic_bmatching(
    component: _CowComponent,
    *,
    context: _CowSelectionContext,
) -> List[_CowPair] | None:
    left_caps = _uniform_sender_row_caps(
        component.side_01,
        asset=context.asset0,
        balances=context.balances,
    )
    right_caps = _uniform_sender_row_caps(
        component.side_10,
        asset=context.asset1,
        balances=context.balances,
    )
    if left_caps is None or right_caps is None:
        return None
    max_pairs = min(
        len(component.side_01),
        len(component.side_10),
        sum(left_caps.values()),
        sum(right_caps.values()),
    )
    if max_pairs <= 0:
        return []
    if max_pairs > _COW_ATOMIC_BMATCHING_FLOW_CAP:
        return None
    if len(component.side_01) * len(component.side_10) > _COW_ATOMIC_BMATCHING_EDGE_CAP:
        return None

    feasible_edges = [
        (i, j)
        for i, x in enumerate(component.side_01)
        for j, y in enumerate(component.side_10)
        if _pair_feasible(x, y)
    ]
    if not feasible_edges:
        return []
    if len(feasible_edges) > _COW_ATOMIC_BMATCHING_EDGE_CAP:
        return None

    return _select_cow_pairs_atomic_bmatching_flow(
        component.side_01,
        component.side_10,
        left_caps=left_caps,
        right_caps=right_caps,
        feasible_edges=feasible_edges,
        max_pairs=max_pairs,
        context=context,
    )


def _uniform_sender_row_caps(
    candidates: List[_CowCandidateExactIn],
    *,
    asset: AssetId,
    balances: BalanceTable,
) -> Dict[PubKey, int] | None:
    by_sender: Dict[PubKey, List[_CowCandidateExactIn]] = defaultdict(list)
    for candidate in candidates:
        by_sender[candidate.sender].append(candidate)

    caps: Dict[PubKey, int] = {}
    for sender, group in by_sender.items():
        amounts = {int(candidate.amount_in) for candidate in group}
        if len(amounts) != 1:
            return None
        amount = amounts.pop()
        if amount <= 0:
            return None
        caps[sender] = int(balances.get(sender, asset)) // amount
    return caps


def _select_cow_pairs_atomic_bmatching_flow(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    left_caps: Dict[PubKey, int],
    right_caps: Dict[PubKey, int],
    feasible_edges: List[tuple[int, int]],
    max_pairs: int,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    left_senders = tuple(sorted(left_caps))
    right_senders = tuple(sorted(right_caps))
    source = 0
    left_sender_offset = 1
    left_row_offset = left_sender_offset + len(left_senders)
    right_row_offset = left_row_offset + len(side_01)
    right_sender_offset = right_row_offset + len(side_10)
    sink = right_sender_offset + len(right_senders)
    graph: List[List[_CowFlowEdge]] = [[] for _ in range(sink + 1)]

    def add_edge(src: int, dst: int, cap: int, cost: int) -> _CowFlowEdge:
        forward = _CowFlowEdge(to=dst, rev=len(graph[dst]), cap=int(cap), cost=int(cost))
        reverse = _CowFlowEdge(to=src, rev=len(graph[src]), cap=0, cost=-int(cost))
        graph[src].append(forward)
        graph[dst].append(reverse)
        return forward

    left_sender_index = {sender: index for index, sender in enumerate(left_senders)}
    right_sender_index = {sender: index for index, sender in enumerate(right_senders)}
    for sender, index in left_sender_index.items():
        add_edge(source, left_sender_offset + index, min(int(left_caps[sender]), max_pairs), 0)
    for sender, index in right_sender_index.items():
        add_edge(right_sender_offset + index, sink, min(int(right_caps[sender]), max_pairs), 0)
    for row_index, candidate in enumerate(side_01):
        sender_node = left_sender_offset + left_sender_index[candidate.sender]
        add_edge(sender_node, left_row_offset + row_index, 1, 0)
    for row_index, candidate in enumerate(side_10):
        sender_node = right_sender_offset + right_sender_index[candidate.sender]
        add_edge(right_row_offset + row_index, sender_node, 1, 0)

    pair_ranks = _cow_pair_rank_map(side_01, side_10, seed=context.seed)
    pair_tie_values = _cow_pair_lex_tie_values(pair_ranks, max_pairs=max_pairs)
    max_tie_bonus = sum(sorted(pair_tie_values.values(), reverse=True)[:max_pairs])
    max_total_volume = sum(int(candidate.amount_in) for candidate in side_01)
    max_total_volume += sum(int(candidate.amount_in) for candidate in side_10)
    tie_scale = max_tie_bonus + 1
    volume_scale = (max_total_volume + 1) * tie_scale

    pair_edges: List[tuple[int, int, _CowFlowEdge]] = []
    for left_index, right_index in feasible_edges:
        x = side_01[left_index]
        y = side_10[right_index]
        volume = int(x.amount_in + y.amount_in)
        surplus = int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out)
        score = (
            volume * volume_scale
            + surplus * tie_scale
            + int(pair_tie_values[(left_index, right_index)])
        )
        edge = add_edge(left_row_offset + left_index, right_row_offset + right_index, 1, score)
        pair_edges.append((left_index, right_index, edge))

    _augment_positive_score_flow(graph, source, sink, max_pairs=max_pairs)
    return [
        (side_01[left_index], side_10[right_index])
        for left_index, right_index, edge in pair_edges
        if edge.cap == 0
    ]


def _augment_positive_score_flow(
    graph: List[List[_CowFlowEdge]],
    source: int,
    sink: int,
    *,
    max_pairs: int,
) -> None:
    for _ in range(max_pairs):
        parent = _best_positive_score_path(graph, source, sink)
        if parent is None:
            return
        node = sink
        while node != source:
            prev_node, edge_index = parent[node]
            edge = graph[prev_node][edge_index]
            edge.cap -= 1
            graph[node][edge.rev].cap += 1
            node = prev_node


def _best_positive_score_path(
    graph: List[List[_CowFlowEdge]],
    source: int,
    sink: int,
) -> Dict[int, tuple[int, int]] | None:
    node_count = len(graph)
    dist: List[int | None] = [None] * node_count
    parent: Dict[int, tuple[int, int]] = {}
    dist[source] = 0
    for _ in range(node_count - 1):
        changed = False
        for node, edges in enumerate(graph):
            if dist[node] is None:
                continue
            base = int(dist[node])
            for edge_index, edge in enumerate(edges):
                if edge.cap <= 0:
                    continue
                candidate = base + int(edge.cost)
                if dist[edge.to] is None or candidate > int(dist[edge.to]):
                    dist[edge.to] = candidate
                    parent[edge.to] = (node, edge_index)
                    changed = True
        if not changed:
            break
    if dist[sink] is None or int(dist[sink]) <= 0:
        return None
    return parent


def _cow_sender_slots(
    candidates: List[_CowCandidateExactIn],
    *,
    asset: AssetId,
    balances: BalanceTable,
) -> List[_CowSenderSlot] | None:
    by_sender: Dict[PubKey, List[_CowCandidateExactIn]] = defaultdict(list)
    for candidate in candidates:
        by_sender[candidate.sender].append(candidate)

    slots: List[_CowSenderSlot] = []
    for sender, group in by_sender.items():
        if len(group) == 1:
            slots.append(_CowSenderSlot(candidates=list(group)))
            continue
        cap = int(balances.get(sender, asset))
        total = sum(int(candidate.amount_in) for candidate in group)
        if total <= cap:
            slots.extend(_CowSenderSlot(candidates=[candidate]) for candidate in group)
            continue
        if _is_single_choice_sender_group(group, cap):
            slots.append(_CowSenderSlot(candidates=list(group)))
            continue
        return None
    return slots


def _is_single_choice_sender_group(
    candidates: List[_CowCandidateExactIn],
    cap: int,
) -> bool:
    if len(candidates) < 2:
        return False
    amounts = sorted(int(candidate.amount_in) for candidate in candidates)
    return amounts[0] + amounts[1] > int(cap)


def _select_cow_slot_pairs(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    left_slots: List[_CowSenderSlot],
    right_slots: List[_CowSenderSlot],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    if not left_slots or not right_slots:
        return []

    left_index = {id(candidate): index for index, candidate in enumerate(side_01)}
    right_index = {id(candidate): index for index, candidate in enumerate(side_10)}
    pair_ranks = _cow_pair_rank_map(side_01, side_10, seed=context.seed)
    max_pairs = min(len(left_slots), len(right_slots))
    pair_tie_values = _cow_pair_lex_tie_values(pair_ranks, max_pairs=max_pairs)
    max_tie_bonus = sum(sorted(pair_tie_values.values(), reverse=True)[:max_pairs])
    max_total_volume = sum(int(candidate.amount_in) for candidate in side_01)
    max_total_volume += sum(int(candidate.amount_in) for candidate in side_10)
    tie_scale = max_tie_bonus + 1
    volume_scale = (max_total_volume + 1) * tie_scale
    max_edge_score = max(1, max_total_volume * volume_scale + max_total_volume * tie_scale + max_tie_bonus)
    impossible_cost = max_edge_score * (len(left_slots) + len(right_slots) + 1)

    size = len(left_slots) + len(right_slots)
    costs = [[0 for _ in range(size)] for _ in range(size)]
    slot_pairs: Dict[tuple[int, int], _CowPair] = {}
    for i, left_slot in enumerate(left_slots):
        for j, right_slot in enumerate(right_slots):
            pair, score = _best_cow_slot_edge(
                left_slot,
                right_slot,
                left_index=left_index,
                right_index=right_index,
                pair_tie_values=pair_tie_values,
                volume_scale=volume_scale,
                tie_scale=tie_scale,
                context=context,
            )
            if pair is None or score is None:
                costs[i][j] = impossible_cost
                continue
            costs[i][j] = -int(score)
            slot_pairs[(i, j)] = pair

    assignment = _hungarian_min_assignment(costs)
    pairs: List[_CowPair] = []
    for i, j in enumerate(assignment[:len(left_slots)]):
        if 0 <= j < len(right_slots) and costs[i][j] < 0:
            pairs.append(slot_pairs[(i, j)])
    return pairs


def _best_cow_slot_edge(
    left_slot: _CowSenderSlot,
    right_slot: _CowSenderSlot,
    *,
    left_index: Dict[int, int],
    right_index: Dict[int, int],
    pair_tie_values: Dict[tuple[int, int], int],
    volume_scale: int,
    tie_scale: int,
    context: _CowSelectionContext,
) -> tuple[_CowPair | None, int | None]:
    best_pair: _CowPair | None = None
    best_score: int | None = None
    for x in left_slot.candidates:
        if int(x.amount_in) > int(context.balances.get(x.sender, context.asset0)):
            continue
        for y in right_slot.candidates:
            if int(y.amount_in) > int(context.balances.get(y.sender, context.asset1)):
                continue
            if not _pair_feasible(x, y):
                continue
            pair_index = (left_index[id(x)], right_index[id(y)])
            volume = int(x.amount_in + y.amount_in)
            surplus = int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out)
            tie_bonus = int(pair_tie_values[pair_index])
            score = volume * volume_scale + surplus * tie_scale + tie_bonus
            if best_score is None or score > best_score:
                best_pair = (x, y)
                best_score = score
    return best_pair, best_score


def _select_cow_pairs_single_choice_star(
    component: _CowComponent,
    *,
    context: _CowSelectionContext,
) -> List[_CowPair] | None:
    if _is_single_choice_star(component.side_01, asset=context.asset0, balances=context.balances):
        return _best_single_cow_pair(component, context=context)
    if _is_single_choice_star(component.side_10, asset=context.asset1, balances=context.balances):
        return _best_single_cow_pair(component, context=context)
    return None


def _is_single_choice_star(
    candidates: List[_CowCandidateExactIn],
    *,
    asset: AssetId,
    balances: BalanceTable,
) -> bool:
    if len(candidates) < 2:
        return False
    sender = candidates[0].sender
    if any(candidate.sender != sender for candidate in candidates):
        return False
    cap = int(balances.get(sender, asset))
    smallest = sorted(int(candidate.amount_in) for candidate in candidates)[:2]
    return len(smallest) == 2 and smallest[0] + smallest[1] > cap


def _best_single_cow_pair(
    component: _CowComponent,
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    best_pair: _CowPair | None = None
    best_key: _CowPairSelectionKey | None = None
    for x in component.side_01:
        if int(x.amount_in) > int(context.balances.get(x.sender, context.asset0)):
            continue
        for y in component.side_10:
            if int(y.amount_in) > int(context.balances.get(y.sender, context.asset1)):
                continue
            if not _pair_feasible(x, y):
                continue
            pair = (x, y)
            key = _cow_pair_selection_key([pair], seed=context.seed)
            if _is_better_cow_pair_key(key, best_key):
                best_key = key
                best_pair = pair
    return [] if best_pair is None else [best_pair]


def _select_cow_pairs_capacity_dp(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    """Exact bounded DP for CoW matching with per-sender capacity coupling."""
    if len(side_10) <= len(side_01):
        return _select_cow_pairs_capacity_dp_left_prefix(side_01, side_10, context=context)
    return _select_cow_pairs_capacity_dp_right_prefix(side_01, side_10, context=context)


def _cow_capacity_dp_state_estimate(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
) -> int:
    """Conservative orientation-aware lower estimate for exact DP state count."""
    masked_len = min(len(side_01), len(side_10))
    processed_len = max(len(side_01), len(side_10))
    return (processed_len + 1) * (1 << masked_len)


def _select_cow_pairs_capacity_dp_left_prefix(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    """Exact DP with a processed left prefix and used-right mask."""
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


def _select_cow_pairs_capacity_dp_right_prefix(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    """Exact DP with a processed right prefix and used-left mask.

    This is the same objective and feasibility relation as the left-prefix DP,
    but it masks the smaller side when the left side is smaller. That turns
    large one-sided multi-choice components from a count-cap defer into an exact
    state-gated solve.
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
        side10_index: int,
        used_side01_mask: int,
        debits0: tuple[int, ...],
        debits1: tuple[int, ...],
    ) -> tuple[tuple[int, int], ...]:
        if side10_index >= len(side_10):
            return ()

        best = rec(side10_index + 1, used_side01_mask, debits0, debits1)
        y = side_10[side10_index]
        y_sender_index = sender1_index[y.sender]
        next_y_debit = int(debits1[y_sender_index]) + int(y.amount_in)
        if next_y_debit > int(caps1[y_sender_index]):
            return best

        for side01_index, x in enumerate(side_01):
            if used_side01_mask & (1 << side01_index):
                continue
            if not _pair_feasible(x, y):
                continue
            x_sender_index = sender0_index[x.sender]
            next_x_debit = int(debits0[x_sender_index]) + int(x.amount_in)
            if next_x_debit > int(caps0[x_sender_index]):
                continue
            next_debits0 = list(debits0)
            next_debits1 = list(debits1)
            next_debits0[x_sender_index] = next_x_debit
            next_debits1[y_sender_index] = next_y_debit
            candidate = (
                (side01_index, side10_index),
                *rec(
                    side10_index + 1,
                    used_side01_mask | (1 << side01_index),
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

    The CoW pair graph is an ordinary bipartite matching problem only when
    selecting every candidate from a sender would still fit that sender's
    balance. If a sender is capacity-coupled across multiple intents, the
    problem includes a knapsack-style side constraint and must stay on exact DP
    or fail-closed defer.
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
