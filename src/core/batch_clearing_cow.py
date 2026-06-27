"""CoW-style pair netting helper for batch clearing."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, List, Tuple

from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent
from ..state.pools import PoolState
from .batch_clearing_cow_search import (
    _CowCandidateExactIn,
    _CowPair,
    _CowPartition,
    _CowSelectionContext,
    _partition_cow_candidates,
    _select_cow_pairs,
)
from .neutral_tiebreak import tiebreak_token
from .settlement import Fill, FillAction


@dataclass(frozen=True)
class _CowMaterializeRequest:
    best_pairs: List["_CowPair"]
    partition: _CowPartition
    swap_intents: List[Intent]
    balances: BalanceTable
    seed: bytes | None = None


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


def _cow_pair_fills(best_pairs: List[_CowPair], *, seed: bytes | None = None) -> List[Fill]:
    fills: List[Fill] = []
    for x, y in best_pairs:
        fills.append(_cow_fill(candidate=x, amount_out=int(y.amount_in)))
        fills.append(_cow_fill(candidate=y, amount_out=int(x.amount_in)))
    fills.sort(key=lambda f: tiebreak_token(f.intent_id, seed))
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
    *,
    seed: bytes | None = None,
) -> List[Intent]:
    remaining_out = list(partition.remaining)
    remaining_out.extend([candidate.intent for candidate in partition.side_01 if candidate.intent.intent_id not in matched_ids])
    remaining_out.extend([candidate.intent for candidate in partition.side_10 if candidate.intent.intent_id not in matched_ids])
    remaining_out.sort(key=lambda intent: tiebreak_token(intent.intent_id, seed))
    return remaining_out


def _materialize_cow_pairs(request: _CowMaterializeRequest) -> tuple[List[Fill], List[Intent]]:
    matched_ids = {candidate.intent.intent_id for pair in request.best_pairs for candidate in pair}
    debit_by_sender_asset, credit_by_recipient_asset = _cow_pair_transfer_maps(request.best_pairs)
    for (sender, asset), amount in debit_by_sender_asset.items():
        if request.balances.get(sender, asset) < amount:
            # Fail closed: fall back to no netting and leave the balances snapshot untouched.
            swap_intents_sorted = sorted(list(request.swap_intents), key=lambda intent: tiebreak_token(intent.intent_id, request.seed))
            return [], swap_intents_sorted

    for (sender, asset), amount in debit_by_sender_asset.items():
        request.balances.subtract(sender, asset, int(amount))
    for (recipient, asset), amount in credit_by_recipient_asset.items():
        request.balances.add(recipient, asset, int(amount))

    return (
        _cow_pair_fills(request.best_pairs, seed=request.seed),
        _unmatched_cow_intents(request.partition, matched_ids, seed=request.seed),
    )


def _cow_pair_netting_exact_in_v1(
    swap_intents: List[Intent],
    *,
    pool_state: PoolState,
    balances: BalanceTable,
    swap_tiebreak_seed: bytes | None = None,
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
    partition = _partition_cow_candidates(swap_intents, pool_state, seed=swap_tiebreak_seed)
    context = _CowSelectionContext(balances=balances, asset0=asset0, asset1=asset1, seed=swap_tiebreak_seed)
    best_pairs = _select_cow_pairs(partition.side_01, partition.side_10, context=context)
    return _materialize_cow_pairs(
        _CowMaterializeRequest(
            best_pairs=best_pairs,
            partition=partition,
            swap_intents=swap_intents,
            balances=balances,
            seed=swap_tiebreak_seed,
        )
    )
