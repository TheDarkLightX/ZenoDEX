"""DST slice 2: Elle/Knossos-style operation-history checker (resilience gap #3).

The other named piece of gap #3. Today's chaos tests assert *per-scenario expected
values*. A history-checker instead records the **operation history** of a settlement
trajectory — each batch's pre/post state-root and per-asset total supply — and checks
the WHOLE history for consistency **anomalies** it shouldn't ever exhibit, catching
violations a scripted assert would miss:

  1. **Chaining** — each step must start exactly where the previous ended
     (`post_root[i] == pre_root[i+1]`, and likewise carried per-asset supplies).
  2. **Conservation** — a swap *moves* value, never creates/destroys it: per-asset
     total supply (all balances + all pool reserves) is invariant across each step.
  3. **Replay-determinism** — re-running the batches from the genuine initial state
     reproduces every recorded post-root (a tampered/non-replayable history fails).

Built on the REAL settlement trajectory machinery (`compute_settlement` +
`apply_settlement_pure` + `compute_state_root`), same as the substrate-independence
work. Honest scope: this checks the *settlement* operation history; it is not a full
linearizability oracle over a concurrent client log, and it does not virtualize IO
(that is DST slice 1 / the remaining IO-virtualization piece).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Sequence

from src.core.batch_clearing import (
    _SWAP_ORDERING_GREEDY_AB_REFINED,
    apply_settlement_pure,
    compute_settlement,
)
from src.core.dex import DexState
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus
from src.state.state_root import compute_state_root

_A0 = "0x" + "0a" * 32
_A1 = "0x" + "0b" * 32
_POOL = "0x" + "0c" * 32
_PKS = ["0x" + h * 48 for h in ("a1", "b2", "c3", "d4")]
_ASSETS = (_A0, _A1)


def total_supply(state: DexState, asset: str) -> int:
    """Total of an asset across ALL holders: every balance + every pool reserve."""
    s = sum(state.balances.get_balances_for_asset(asset).values())
    for pool in state.pools.values():
        if pool.asset0 == asset:
            s += int(pool.reserve0)
        if pool.asset1 == asset:
            s += int(pool.reserve1)
    return int(s)


def _root(state: DexState) -> str:
    return compute_state_root(
        balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=NonceTable()
    )


@dataclass(frozen=True)
class Record:
    pre_root: str
    post_root: str
    pre_supplies: Dict[str, int]
    post_supplies: Dict[str, int]


def run_history(
    initial: DexState,
    batches: Sequence[Sequence[Intent]],
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
) -> List[Record]:
    """Settle a sequence of batches, carrying state, and record the operation history."""
    records: List[Record] = []
    state = initial
    for batch in batches:
        pre_root = _root(state)
        pre_supplies = {a: total_supply(state, a) for a in _ASSETS}
        settlement = compute_settlement(
            list(batch), state.pools, state.balances, state.lp_balances, swap_ordering=swap_ordering
        )
        nb, np_, nl = apply_settlement_pure(settlement, state.balances, state.pools, state.lp_balances)
        state = DexState(balances=nb, pools=np_, lp_balances=nl)
        records.append(
            Record(
                pre_root=pre_root,
                post_root=_root(state),
                pre_supplies=pre_supplies,
                post_supplies={a: total_supply(state, a) for a in _ASSETS},
            )
        )
    return records


def check_history(records: Sequence[Record], assets: Sequence[str] = _ASSETS) -> List[str]:
    """Return the list of consistency anomalies in a recorded history (empty = clean)."""
    anomalies: List[str] = []
    for i, r in enumerate(records):
        for a in assets:  # per-step conservation
            if r.pre_supplies.get(a) != r.post_supplies.get(a):
                anomalies.append(f"conservation@{i}:asset={a[:6]}:pre={r.pre_supplies.get(a)}!=post={r.post_supplies.get(a)}")
    for i in range(len(records) - 1):  # chaining
        if records[i].post_root != records[i + 1].pre_root:
            anomalies.append(f"chain_root@{i}->{i+1}")
        for a in assets:
            if records[i].post_supplies.get(a) != records[i + 1].pre_supplies.get(a):
                anomalies.append(f"chain_supply@{i}->{i+1}:asset={a[:6]}")
    return anomalies


def replay_matches(
    initial: DexState,
    batches: Sequence[Sequence[Intent]],
    records: Sequence[Record],
    *,
    swap_ordering: str = _SWAP_ORDERING_GREEDY_AB_REFINED,
) -> bool:
    """Replay-determinism: re-running from the genuine initial state must reproduce
    every recorded post-root."""
    replayed = run_history(initial, batches, swap_ordering=swap_ordering)
    return [r.post_root for r in replayed] == [r.post_root for r in records]


# --- builders -----------------------------------------------------------------

def demo_initial() -> DexState:
    b = BalanceTable()
    for pk in _PKS:
        b.set(pk, _A0, 100_000_000)
        b.set(pk, _A1, 100_000_000)
    pools = {
        _POOL: PoolState(
            pool_id=_POOL, asset0=_A0, asset1=_A1, reserve0=10_000_000, reserve1=10_000_000,
            fee_bps=30, lp_supply=10_000_000, status=PoolStatus.ACTIVE, created_at=0,
        )
    }
    return DexState(balances=b, pools=pools, lp_balances=LPTable())


def _swap(label: str, pk: str, amt: int, direction: int) -> Intent:
    import hashlib
    ai, ao = (_A0, _A1) if direction == 0 else (_A1, _A0)
    return Intent(
        module="TauSwap", version="0.1",
        intent_id="0x" + hashlib.sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey=pk, kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
        fields={"pool_id": _POOL, "asset_in": ai, "asset_out": ao, "amount_in": amt, "min_amount_out": 0},
    )


def demo_batches() -> List[List[Intent]]:
    return [
        [_swap(f"b{r}-{i}", pk, 4000 + 500 * i, (i + r) % 2) for i, pk in enumerate(_PKS)]
        for r in range(3)
    ]
