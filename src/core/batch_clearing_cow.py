"""CoW-style pair netting helper for batch clearing."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, List, Tuple

from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState
from .settlement import Fill, FillAction


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
class _CowPartition:
    side_01: List[_CowCandidateExactIn]
    side_10: List[_CowCandidateExactIn]
    remaining: List[Intent]


@dataclass(frozen=True)
class _CowSelectionContext:
    balances: BalanceTable
    asset0: AssetId
    asset1: AssetId


@dataclass(frozen=True)
class _CowMaterializeRequest:
    best_pairs: List["_CowPair"]
    partition: _CowPartition
    swap_intents: List[Intent]
    balances: BalanceTable


@dataclass(frozen=True)
class _CowSearchState:
    side01_index: int
    used_side10_indices: set[int]
    debits_asset0: Dict[PubKey, int]
    debits_asset1: Dict[PubKey, int]
    pairs: List["_CowPair"]


_CowPair = tuple[_CowCandidateExactIn, _CowCandidateExactIn]
_CowPairSelectionKey = tuple[int, int, Tuple[Tuple[str, str], ...]]


def _cow_pair_selection_key(pairs: List[_CowPair]) -> _CowPairSelectionKey:
    volume = sum(int(x.amount_in + y.amount_in) for x, y in pairs)
    surplus = sum(int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out) for x, y in pairs)
    pair_ids = tuple(sorted((x.intent.intent_id, y.intent.intent_id) for x, y in pairs))
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


def _candidate_from_intent(intent: Intent, pool_state: PoolState) -> _CowCandidateExactIn | None:
    a0 = pool_state.asset0
    a1 = pool_state.asset1
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return None

    pool_id = intent.get_field("pool_id")
    if pool_id != pool_state.pool_id:
        return None

    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None
    if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
        return None

    sender = intent.sender_pubkey
    recipient = intent.get_field("recipient", sender)
    if not isinstance(recipient, str) or not recipient:
        return None

    if asset_in == a0 and asset_out == a1:
        return _CowCandidateExactIn(
            intent=intent,
            amount_in=int(amount_in),
            min_amount_out=int(min_out),
            sender=sender,
            recipient=recipient,
            asset_in=a0,
            asset_out=a1,
        )
    if asset_in == a1 and asset_out == a0:
        return _CowCandidateExactIn(
            intent=intent,
            amount_in=int(amount_in),
            min_amount_out=int(min_out),
            sender=sender,
            recipient=recipient,
            asset_in=a1,
            asset_out=a0,
        )
    return None


def _partition_cow_candidates(
    swap_intents: List[Intent],
    pool_state: PoolState,
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

    side_01.sort(key=lambda c: c.intent.intent_id)
    side_10.sort(key=lambda c: c.intent.intent_id)
    return _CowPartition(side_01=side_01, side_10=side_10, remaining=remaining)


def _pair_feasible(x: _CowCandidateExactIn, y: _CowCandidateExactIn) -> bool:
    return y.amount_in >= x.min_amount_out and x.amount_in >= y.min_amount_out


def _sender_asset_balances(
    candidates: List[_CowCandidateExactIn],
    balances: BalanceTable,
    asset: AssetId,
) -> Dict[PubKey, int]:
    return {candidate.sender: int(balances.get(candidate.sender, asset)) for candidate in candidates}


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

    def rec(state: _CowSearchState) -> None:
        nonlocal best_pairs, best_key
        if state.side01_index >= len(side_01):
            key = _cow_pair_selection_key(state.pairs)
            if _is_better_cow_pair_key(key, best_key):
                best_key = key
                best_pairs = list(state.pairs)
            return

        rec(_skip_side01_candidate(state))

        x = side_01[state.side01_index]
        cur_deb0 = int(state.debits_asset0.get(x.sender, 0))
        if cur_deb0 + x.amount_in > int(bal0.get(x.sender, 0)):
            return

        for j, y in enumerate(side_10):
            if j in state.used_side10_indices:
                continue
            if not _pair_feasible(x, y):
                continue
            cur_deb1 = int(state.debits_asset1.get(y.sender, 0))
            if cur_deb1 + y.amount_in > int(bal1.get(y.sender, 0)):
                continue

            used_j2 = set(state.used_side10_indices)
            deb0_2 = dict(state.debits_asset0)
            deb1_2 = dict(state.debits_asset1)
            used_j2.add(j)
            deb0_2[x.sender] = cur_deb0 + x.amount_in
            deb1_2[y.sender] = cur_deb1 + y.amount_in
            rec(
                _CowSearchState(
                    side01_index=int(state.side01_index) + 1,
                    used_side10_indices=used_j2,
                    debits_asset0=deb0_2,
                    debits_asset1=deb1_2,
                    pairs=[*state.pairs, (x, y)],
                )
            )

    rec(_CowSearchState(0, set(), {}, {}, []))
    return best_pairs


def _skip_side01_candidate(state: _CowSearchState) -> _CowSearchState:
    return _CowSearchState(
        side01_index=int(state.side01_index) + 1,
        used_side10_indices=state.used_side10_indices,
        debits_asset0=state.debits_asset0,
        debits_asset1=state.debits_asset1,
        pairs=state.pairs,
    )


def _select_cow_pairs_greedy(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    best_pairs: List[_CowPair] = []
    side_01_sorted = sorted(side_01, key=lambda c: (-c.min_amount_out, c.intent.intent_id))
    side_10_pool = list(side_10)
    deb0: Dict[PubKey, int] = defaultdict(int)
    deb1: Dict[PubKey, int] = defaultdict(int)

    for x in side_01_sorted:
        if deb0[x.sender] + x.amount_in > int(context.balances.get(x.sender, context.asset0)):
            continue
        best_j: int | None = None
        best_y: _CowCandidateExactIn | None = None
        for j, y in enumerate(side_10_pool):
            if not _pair_feasible(x, y):
                continue
            if deb1[y.sender] + y.amount_in > int(context.balances.get(y.sender, context.asset1)):
                continue
            if best_y is None or (y.amount_in, y.intent.intent_id) < (best_y.amount_in, best_y.intent.intent_id):
                best_j, best_y = j, y
        if best_j is None or best_y is None:
            continue
        deb0[x.sender] += x.amount_in
        deb1[best_y.sender] += best_y.amount_in
        best_pairs.append((x, best_y))
        side_10_pool.pop(best_j)

    return best_pairs


def _select_cow_pairs(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    context: _CowSelectionContext,
) -> List[_CowPair]:
    brute_cap = 8
    if len(side_01) + len(side_10) <= brute_cap:
        return _select_cow_pairs_bruteforce(
            side_01,
            side_10,
            context=context,
        )
    return _select_cow_pairs_greedy(side_01, side_10, context=context)


def _cow_pair_transfer_maps(
    best_pairs: List[_CowPair],
) -> tuple[Dict[Tuple[PubKey, AssetId], int], Dict[Tuple[PubKey, AssetId], int]]:
    debit_by_sender_asset: Dict[Tuple[PubKey, AssetId], int] = defaultdict(int)
    credit_by_recipient_asset: Dict[Tuple[PubKey, AssetId], int] = defaultdict(int)
    for x, y in best_pairs:
        # x receives y.amount_in of asset1; y receives x.amount_in of asset0.
        debit_by_sender_asset[(x.sender, x.asset_in)] += int(x.amount_in)
        debit_by_sender_asset[(y.sender, y.asset_in)] += int(y.amount_in)
        credit_by_recipient_asset[(x.recipient, x.asset_out)] += int(y.amount_in)
        credit_by_recipient_asset[(y.recipient, y.asset_out)] += int(x.amount_in)
    return debit_by_sender_asset, credit_by_recipient_asset


def _cow_pair_fills(best_pairs: List[_CowPair]) -> List[Fill]:
    fills: List[Fill] = []
    for x, y in best_pairs:
        fills.append(_cow_fill(candidate=x, amount_out=int(y.amount_in)))
        fills.append(_cow_fill(candidate=y, amount_out=int(x.amount_in)))
    fills.sort(key=lambda f: f.intent_id)
    return fills


def _cow_fill(candidate: _CowCandidateExactIn, *, amount_out: int) -> Fill:
    return Fill(
        intent_id=candidate.intent.intent_id,
        action=FillAction.FILL,
        reason="COW_NETTED",
        amount_in_filled=int(candidate.amount_in),
        amount_out_filled=int(amount_out),
        fee_paid=0,
    )


def _unmatched_cow_intents(
    partition: _CowPartition,
    matched_ids: set[str],
) -> List[Intent]:
    remaining_out = list(partition.remaining)
    remaining_out.extend([candidate.intent for candidate in partition.side_01 if candidate.intent.intent_id not in matched_ids])
    remaining_out.extend([candidate.intent for candidate in partition.side_10 if candidate.intent.intent_id not in matched_ids])
    remaining_out.sort(key=lambda intent: intent.intent_id)
    return remaining_out


def _materialize_cow_pairs(request: _CowMaterializeRequest) -> tuple[List[Fill], List[Intent]]:
    matched_ids = {candidate.intent.intent_id for pair in request.best_pairs for candidate in pair}
    debit_by_sender_asset, credit_by_recipient_asset = _cow_pair_transfer_maps(request.best_pairs)
    for (sender, asset), amount in debit_by_sender_asset.items():
        if request.balances.get(sender, asset) < amount:
            # Fail closed: fall back to no netting and leave the balances snapshot untouched.
            swap_intents_sorted = sorted(list(request.swap_intents), key=lambda intent: intent.intent_id)
            return [], swap_intents_sorted

    for (sender, asset), amount in debit_by_sender_asset.items():
        request.balances.subtract(sender, asset, int(amount))
    for (recipient, asset), amount in credit_by_recipient_asset.items():
        request.balances.add(recipient, asset, int(amount))

    return _cow_pair_fills(request.best_pairs), _unmatched_cow_intents(request.partition, matched_ids)


def _cow_pair_netting_exact_in_v1(
    swap_intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
) -> tuple[List[Fill], List[Intent]]:
    """Try to net opposite-direction exact-in swaps directly between users.

    A pair (a: asset0->asset1, b: asset1->asset0) is matchable if:
    - b.amount_in >= a.min_amount_out
    - a.amount_in >= b.min_amount_out
    - aggregate per-sender debits are feasible on the pre-netting balances snapshot

    Outputs for a matched pair:
    - a.amount_out_filled = b.amount_in
    - b.amount_out_filled = a.amount_in
    - fee_paid = 0, reason = "COW_NETTED"

    This is an experimental, certificate-friendly primitive; it is not intended
    to be AB-optimal globally.
    """
    asset0 = pool_state.asset0
    asset1 = pool_state.asset1
    partition = _partition_cow_candidates(swap_intents, pool_state)
    context = _CowSelectionContext(balances=balances, asset0=asset0, asset1=asset1)
    best_pairs = _select_cow_pairs(partition.side_01, partition.side_10, context=context)
    return _materialize_cow_pairs(
        _CowMaterializeRequest(
            best_pairs=best_pairs,
            partition=partition,
            swap_intents=swap_intents,
            balances=balances,
        )
    )
