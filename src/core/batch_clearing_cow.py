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


_CowPair = tuple[_CowCandidateExactIn, _CowCandidateExactIn]


def _partition_cow_candidates(
    swap_intents: List[Intent],
    pool_state: PoolState,
) -> tuple[List[_CowCandidateExactIn], List[_CowCandidateExactIn], List[Intent]]:
    a0 = pool_state.asset0
    a1 = pool_state.asset1
    side_01: List[_CowCandidateExactIn] = []
    side_10: List[_CowCandidateExactIn] = []
    remaining: List[Intent] = []

    for intent in swap_intents:
        if intent.kind != IntentKind.SWAP_EXACT_IN:
            remaining.append(intent)
            continue
        asset_in = intent.get_field("asset_in")
        asset_out = intent.get_field("asset_out")
        amount_in = intent.get_field("amount_in")
        min_out = intent.get_field("min_amount_out", 0)
        if not isinstance(asset_in, str) or not isinstance(asset_out, str):
            remaining.append(intent)
            continue
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
            remaining.append(intent)
            continue
        if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
            remaining.append(intent)
            continue

        sender = intent.sender_pubkey
        recipient = intent.get_field("recipient", sender)
        if not isinstance(recipient, str) or not recipient:
            remaining.append(intent)
            continue

        if asset_in == a0 and asset_out == a1:
            side_01.append(
                _CowCandidateExactIn(
                    intent=intent,
                    amount_in=int(amount_in),
                    min_amount_out=int(min_out),
                    sender=sender,
                    recipient=recipient,
                    asset_in=a0,
                    asset_out=a1,
                )
            )
        elif asset_in == a1 and asset_out == a0:
            side_10.append(
                _CowCandidateExactIn(
                    intent=intent,
                    amount_in=int(amount_in),
                    min_amount_out=int(min_out),
                    sender=sender,
                    recipient=recipient,
                    asset_in=a1,
                    asset_out=a0,
                )
            )
        else:
            remaining.append(intent)

    side_01.sort(key=lambda c: c.intent.intent_id)
    side_10.sort(key=lambda c: c.intent.intent_id)
    return side_01, side_10, remaining


def _pair_feasible(x: _CowCandidateExactIn, y: _CowCandidateExactIn) -> bool:
    return y.amount_in >= x.min_amount_out and x.amount_in >= y.min_amount_out


def _select_cow_pairs_bruteforce(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    balances: BalanceTable,
    asset0: AssetId,
    asset1: AssetId,
) -> List[_CowPair]:
    best_pairs: List[_CowPair] = []
    best_key: tuple[int, int, Tuple[Tuple[str, str], ...]] | None = None
    bal0: Dict[PubKey, int] = {}
    bal1: Dict[PubKey, int] = {}
    for candidate in side_01:
        bal0[candidate.sender] = int(balances.get(candidate.sender, asset0))
    for candidate in side_10:
        bal1[candidate.sender] = int(balances.get(candidate.sender, asset1))

    def rec(
        i: int,
        used_j: set[int],
        deb0: Dict[PubKey, int],
        deb1: Dict[PubKey, int],
        acc: List[_CowPair],
    ) -> None:
        nonlocal best_pairs, best_key
        if i >= len(side_01):
            volume = sum(int(x.amount_in + y.amount_in) for x, y in acc)
            surplus = sum(int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out) for x, y in acc)
            pair_ids = tuple(sorted((x.intent.intent_id, y.intent.intent_id) for x, y in acc))
            key = (volume, surplus, pair_ids)
            if best_key is None or key > best_key:
                best_key = key
                best_pairs = list(acc)
            return

        # Option: leave side_01[i] unmatched.
        rec(i + 1, used_j, deb0, deb1, acc)

        x = side_01[i]
        cur_deb0 = int(deb0.get(x.sender, 0))
        if cur_deb0 + x.amount_in > int(bal0.get(x.sender, 0)):
            return

        for j, y in enumerate(side_10):
            if j in used_j:
                continue
            if not _pair_feasible(x, y):
                continue
            cur_deb1 = int(deb1.get(y.sender, 0))
            if cur_deb1 + y.amount_in > int(bal1.get(y.sender, 0)):
                continue

            used_j2 = set(used_j)
            used_j2.add(j)
            deb0_2 = dict(deb0)
            deb1_2 = dict(deb1)
            deb0_2[x.sender] = cur_deb0 + x.amount_in
            deb1_2[y.sender] = cur_deb1 + y.amount_in
            acc.append((x, y))
            rec(i + 1, used_j2, deb0_2, deb1_2, acc)
            acc.pop()

    rec(0, set(), {}, {}, [])
    return best_pairs


def _select_cow_pairs_greedy(
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    *,
    balances: BalanceTable,
    asset0: AssetId,
    asset1: AssetId,
) -> List[_CowPair]:
    best_pairs: List[_CowPair] = []
    side_01_sorted = sorted(side_01, key=lambda c: (-c.min_amount_out, c.intent.intent_id))
    side_10_pool = list(side_10)
    deb0: Dict[PubKey, int] = defaultdict(int)
    deb1: Dict[PubKey, int] = defaultdict(int)

    for x in side_01_sorted:
        if deb0[x.sender] + x.amount_in > int(balances.get(x.sender, asset0)):
            continue
        best_j: int | None = None
        best_y: _CowCandidateExactIn | None = None
        for j, y in enumerate(side_10_pool):
            if not _pair_feasible(x, y):
                continue
            if deb1[y.sender] + y.amount_in > int(balances.get(y.sender, asset1)):
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
    balances: BalanceTable,
    asset0: AssetId,
    asset1: AssetId,
) -> List[_CowPair]:
    brute_cap = 8
    if len(side_01) + len(side_10) <= brute_cap:
        return _select_cow_pairs_bruteforce(
            side_01,
            side_10,
            balances=balances,
            asset0=asset0,
            asset1=asset1,
        )
    return _select_cow_pairs_greedy(side_01, side_10, balances=balances, asset0=asset0, asset1=asset1)


def _materialize_cow_pairs(
    best_pairs: List[_CowPair],
    *,
    side_01: List[_CowCandidateExactIn],
    side_10: List[_CowCandidateExactIn],
    remaining: List[Intent],
    swap_intents: List[Intent],
    balances: BalanceTable,
) -> tuple[List[Fill], List[Intent]]:
    matched_ids = {candidate.intent.intent_id for pair in best_pairs for candidate in pair}

    # Apply to balances snapshot atomically: subtract all debits, then add all credits.
    debit_by_sender_asset: Dict[Tuple[PubKey, AssetId], int] = defaultdict(int)
    credit_by_recipient_asset: Dict[Tuple[PubKey, AssetId], int] = defaultdict(int)
    for x, y in best_pairs:
        # x receives y.amount_in of asset1; y receives x.amount_in of asset0.
        debit_by_sender_asset[(x.sender, x.asset_in)] += int(x.amount_in)
        debit_by_sender_asset[(y.sender, y.asset_in)] += int(y.amount_in)
        credit_by_recipient_asset[(x.recipient, x.asset_out)] += int(y.amount_in)
        credit_by_recipient_asset[(y.recipient, y.asset_out)] += int(x.amount_in)

    for (sender, asset), amount in debit_by_sender_asset.items():
        if balances.get(sender, asset) < amount:
            # Fail closed: fall back to no netting and leave the balances snapshot untouched.
            swap_intents_sorted = sorted(list(swap_intents), key=lambda intent: intent.intent_id)
            return [], swap_intents_sorted

    for (sender, asset), amount in debit_by_sender_asset.items():
        balances.subtract(sender, asset, int(amount))
    for (recipient, asset), amount in credit_by_recipient_asset.items():
        balances.add(recipient, asset, int(amount))

    fills: List[Fill] = []
    for x, y in best_pairs:
        fills.append(
            Fill(
                intent_id=x.intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=int(x.amount_in),
                amount_out_filled=int(y.amount_in),
                fee_paid=0,
            )
        )
        fills.append(
            Fill(
                intent_id=y.intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=int(y.amount_in),
                amount_out_filled=int(x.amount_in),
                fee_paid=0,
            )
        )

    fills.sort(key=lambda f: f.intent_id)
    remaining_out = list(remaining)
    remaining_out.extend([candidate.intent for candidate in side_01 if candidate.intent.intent_id not in matched_ids])
    remaining_out.extend([candidate.intent for candidate in side_10 if candidate.intent.intent_id not in matched_ids])
    remaining_out.sort(key=lambda intent: intent.intent_id)
    return fills, remaining_out


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
    side_01, side_10, remaining = _partition_cow_candidates(swap_intents, pool_state)
    best_pairs = _select_cow_pairs(side_01, side_10, balances=balances, asset0=asset0, asset1=asset1)
    return _materialize_cow_pairs(
        best_pairs,
        side_01=side_01,
        side_10=side_10,
        remaining=remaining,
        swap_intents=swap_intents,
        balances=balances,
    )
