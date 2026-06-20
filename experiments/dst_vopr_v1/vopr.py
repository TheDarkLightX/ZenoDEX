"""DST slice 3: VOPR-style deterministic simulation core (resilience gap #3).

Composes slice 1 (snapshot crash-consistency) + slice 2 (operation history) into one
**seed-reproducible** deterministic simulation that virtualizes the IO ZenoLedger
OWNS — logical clock (step index), disk (snapshot persist/recover), and crash timing
(seed-driven) — and injects crashes + disk corruption between settlements. Network /
consensus is Tau's, so it is deliberately NOT virtualized.

Every run is a pure function of the seed (the FoundationDB/TigerBeetle-VOPR property),
so any failure reproduces exactly. The harness asserts, across every seeded run:

  * **fail-closed recovery** — a crash that reads a torn/corrupted newest on-disk
    snapshot NEVER adopts it; it falls back to the previous durable checkpoint. The
    recovered state-root is ALWAYS a previously-COMMITTED root, never a corrupt one.
  * **determinism** — `simulate(seed)` returns an identical op-log + final root every
    time.

It also supports a planted bug (`verify_commitment=False`) that trusts the disk
blindly; under corruption that adopts a non-committed root, which the same invariant
**catches and reproduces** — demonstrating the checker is live (not vacuous).

Built on the REAL engine + snapshot (`compute_settlement` / `apply_settlement_pure` /
`dex_snapshot` / `compute_state_root`).
"""

from __future__ import annotations

import hashlib
import json
import random
from dataclasses import dataclass, field
from typing import List

from src.core.batch_clearing import (
    _SWAP_ORDERING_GREEDY_AB_REFINED,
    apply_settlement_pure,
    compute_settlement,
)
from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.state.balances import BalanceTable
from src.state.canonical import domain_sep_bytes
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus
from src.state.state_root import compute_state_root

_A0 = "0x" + "0a" * 32
_A1 = "0x" + "0b" * 32
_POOL = "0x" + "0c" * 32
_PKS = ["0x" + h * 48 for h in ("a1", "b2", "c3", "d4")]


def _root(state: DexState) -> str:
    return compute_state_root(
        balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=NonceTable()
    )


def _initial() -> DexState:
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


@dataclass(frozen=True)
class Checkpoint:
    commitment: bytes
    payload: bytes
    version: int
    root: str


def _persist(state: DexState) -> Checkpoint:
    snap = snapshot_from_state(state)
    return Checkpoint(snap.commitment_bytes(), snap.canonical_bytes(), snap.version, _root(state))


def _state_from(cp: Checkpoint) -> DexState:
    return state_from_snapshot(json.loads(cp.payload.decode("utf-8")))


def _commit_over(disk: bytes, version: int) -> bytes:
    return hashlib.sha256(domain_sep_bytes("dex_snapshot", version=version) + disk).digest()


def _random_batch(rng: random.Random) -> List[Intent]:
    out: List[Intent] = []
    for pk in _PKS:
        if rng.random() < 0.5:
            d = rng.randint(0, 1)
            ai, ao = (_A0, _A1) if d == 0 else (_A1, _A0)
            label = f"{pk[:6]}-{rng.randint(0, 10**9)}"
            out.append(Intent(
                module="TauSwap", version="0.1",
                intent_id="0x" + hashlib.sha256(label.encode("utf-8")).hexdigest(),
                sender_pubkey=pk, kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
                fields={"pool_id": _POOL, "asset_in": ai, "asset_out": ao,
                        "amount_in": rng.randint(1000, 9000), "min_amount_out": 0},
            ))
    return out


def _corrupt(rng: random.Random, payload: bytes) -> bytes:
    if rng.random() < 0.5 and len(payload) > 1:  # torn write
        return payload[: rng.randint(0, len(payload) - 1)]
    b = bytearray(payload)  # byte change
    pos = rng.randint(0, len(b) - 1)
    b[pos] = (b[pos] + 1 + rng.randint(0, 254)) & 0xFF
    return bytes(b)


@dataclass
class SimResult:
    seed: int
    op_log: List[str] = field(default_factory=list)
    final_root: str = ""
    crashes: int = 0
    fallbacks: int = 0
    anomalies: List[str] = field(default_factory=list)


def simulate(seed: int, *, steps: int = 40, verify_commitment: bool = True) -> SimResult:
    """Deterministic seeded run. `verify_commitment=False` is a planted bug (trusts
    the disk blindly) used to prove the invariant catches a real corruption."""
    rng = random.Random(seed)
    state = _initial()
    committed: List[Checkpoint] = [_persist(state)]  # genesis is durable
    res = SimResult(seed=seed)

    for _ in range(steps):
        op = rng.random()
        if op < 0.55:  # settle a random batch
            batch = _random_batch(rng)
            if not batch:
                res.op_log.append("settle:empty")
                continue
            s = compute_settlement(batch, state.pools, state.balances, state.lp_balances,
                                   swap_ordering=_SWAP_ORDERING_GREEDY_AB_REFINED)
            nb, np_, nl = apply_settlement_pure(s, state.balances, state.pools, state.lp_balances)
            state = DexState(balances=nb, pools=np_, lp_balances=nl)
            res.op_log.append(f"settle:{len(batch)}")
        elif op < 0.8:  # checkpoint to disk
            committed.append(_persist(state))
            res.op_log.append("checkpoint")
        else:  # crash + recover
            res.crashes += 1
            newest = committed[-1]
            durable_fallback = committed[-2] if len(committed) >= 2 else committed[-1]
            disk = newest.payload
            corrupted = len(committed) >= 2 and rng.random() < 0.5  # only the newest write is at risk
            if corrupted:
                disk = _corrupt(rng, newest.payload)
            ok = _commit_over(disk, newest.version) == newest.commitment
            if verify_commitment and not ok:
                state = _state_from(durable_fallback)  # fail-closed: previous durable checkpoint
                recovered_root = durable_fallback.root
                res.fallbacks += 1
                res.op_log.append("crash:fallback")
            else:
                try:  # adopt the disk (verified, OR blindly under the planted bug)
                    state = state_from_snapshot(json.loads(disk.decode("utf-8")))
                    recovered_root = _root(state)
                    res.op_log.append("crash:adopt_disk")
                except Exception:
                    recovered_root = "<unparseable-disk>"
                    res.op_log.append("crash:adopt_unparseable")
            # INVARIANT: a crash must recover a previously-COMMITTED root, never a corrupt one.
            if recovered_root not in {c.root for c in committed}:
                res.anomalies.append(f"adopted_noncommitted_root(corrupted={corrupted})")
                break  # VOPR: stop at the first invariant violation; the seed reproduces it

    try:
        res.final_root = _root(state)
    except Exception:
        res.final_root = "<corrupt-state>"  # the planted-bug path may leave state corrupt
    return res
