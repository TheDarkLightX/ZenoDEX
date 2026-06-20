"""Production-engine substrate-independence (Tau-failure game day, part 2).

`substrate_independence.py` (v1) proved the SIMPLIFIED core (`cpmm.swap` +
`compute_state_root`) is substrate-independent *given a canonical order*. This
module proves the stronger, production-grade property for the real batch
settlement engine `src.core.batch_clearing.compute_settlement`:

    the settlement is a pure function of the intent SET + pre-state, and is
    INVARIANT to the order a substrate delivers the intents in — because the
    engine canonically orders internally.

Therefore any non-Tau orderer (local, CometBFT, shared sequencer, or an
adversarial shuffler) that delivers the **same intent set against the same
pre-state** yields the BYTE-IDENTICAL settlement a Tau checkpoint would — the
substrate's role here is order-only. (This is an in-process property over a fixed
intent set; substrate *liveness/inclusion* — which intents enter the batch at all
— is a separate concern, as is a live multi-batch trajectory.) So ZenoDEX
settlement survives Tau changing its rules or failing to launch: the orderer
cannot change *what* settles from a given batch, only (at most) inclusion.

Honest scope: this is the "run the production engine off-Tau" half of the game
day, demonstrated as order-invariance at the top-level `compute_settlement`
entry. Remaining game-day pieces (see README): a multi-batch trajectory carrying
state across batches on a live non-Tau sequencer, and byte-identical RISC0
receipt replay.

Imports only `src.core` / `src.state` — never `src.integration` (the Tau shell).
"""

from __future__ import annotations

import hashlib
import json
from typing import Dict, Sequence

from src.core.batch_clearing import (
    _SWAP_ORDERING_GREEDY_AB_REFINED,
    apply_settlement_pure,
    compute_settlement,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState
from src.state.state_root import compute_state_root


def settlement_digest(settlement) -> str:
    """Canonical, order-independent digest of a Settlement's fills.

    The fills fully determine the state transition; we sort them so the digest
    depends on the settlement *content*, not on the fill-list order.
    """
    rows = sorted(
        (
            f.intent_id,
            f.action.name,
            f.reason or "",
            int(f.amount_in_filled or 0),
            int(f.amount_out_filled or 0),
            int(f.fee_paid or 0),
        )
        for f in settlement.fills
    )
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode("utf-8")).hexdigest()


def filled_count(settlement) -> int:
    return sum(1 for f in settlement.fills if f.action.name == "FILL")


class Substrate:
    """An ordering substrate. Its ONLY job is to deliver the batch's intents in
    *some* order; the production engine settles them. Validity must not depend on
    which concrete substrate is used."""

    name = "abstract"

    def order(self, intents: Sequence[Intent]) -> list[Intent]:
        raise NotImplementedError


class TauCheckpointSubstrate(Substrate):
    """The reference substrate (what ZenoDEX uses today): Tau provides the order."""

    name = "tau-checkpoint"

    def order(self, intents: Sequence[Intent]) -> list[Intent]:
        return list(intents)


class LocalSequencerSubstrate(Substrate):
    """A non-Tau local sequencer that happens to deliver in a different order."""

    name = "local-sequencer (non-Tau)"

    def order(self, intents: Sequence[Intent]) -> list[Intent]:
        return list(reversed(intents))


class AdversarialShuffleSubstrate(Substrate):
    """A hostile non-Tau sequencer that reorders intents trying to gain advantage.
    The point: it CANNOT change the settlement — the engine canonicalizes — so
    reordering buys nothing. (Grinding the *identity* tie-break is the separate
    concern handled by experiments/neutral_tiebreak_v1/.)"""

    name = "adversarial-shuffle (non-Tau)"

    def __init__(self, perm: Sequence[int]):
        self._perm = list(perm)

    def order(self, intents: Sequence[Intent]) -> list[Intent]:
        items = list(intents)
        if sorted(self._perm) != list(range(len(items))):
            raise ValueError("perm must be a permutation of range(len(intents))")
        return [items[i] for i in self._perm]


def settle_via(
    substrate: Substrate,
    intents: Sequence[Intent],
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp_balances: LPTable | None = None,
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
):
    """Settle a batch under `substrate`'s delivery order via the production engine."""
    return compute_settlement(
        substrate.order(intents),
        pools,
        balances,
        lp_balances,
        swap_ordering=swap_ordering,
    )


def trajectory_roots(
    substrate: Substrate,
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    batches: Sequence[Sequence[Intent]],
    *,
    lp_balances: LPTable | None = None,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
) -> list[str]:
    """Run a SEQUENCE of batches through the production engine under `substrate`'s
    delivery order, carrying state across batches with the pure apply, and return
    the ZenoDEX state root after each batch.

    This is the "run the production engine over a multi-batch trajectory off-Tau"
    demonstration: a non-Tau substrate that delivers each batch in any order yields
    the byte-identical root *sequence* a Tau checkpoint would — because every batch
    settles order-independently and the apply is a pure deterministic function.
    """
    cur_balances = balances
    cur_pools = pools
    cur_lp = lp_balances if lp_balances is not None else LPTable()
    roots: list[str] = []
    for batch in batches:
        settlement = compute_settlement(
            substrate.order(batch), cur_pools, cur_balances, cur_lp, swap_ordering=swap_ordering
        )
        cur_balances, cur_pools, cur_lp = apply_settlement_pure(
            settlement, cur_balances, cur_pools, cur_lp
        )
        roots.append(
            compute_state_root(
                balances=cur_balances, pools=cur_pools, lp_balances=cur_lp, nonces=NonceTable()
            )
        )
    return roots
