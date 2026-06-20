"""Tau substrate-independence conformance harness (prototype, isolated).

Roadmap resilience gap #0 (`internal/ZENOLEDGER_RESILIENCE_HARDENING_2026-06-18.md`,
§Substrate independence): turn "ZenoDEX could detach from Tau" into a *tested*
property. This v1 proves the **validity** half of the Tau-failure game day using
the REAL ZenoDEX core primitives:

  settlement validity is a pure deterministic function of
  (pre_state, canonically-ordered batch) and carries NO substrate identity.

Therefore any ordering substrate (local sequencer, CometBFT, shared sequencer,
validity rollup, Tau checkpoint) yields the **byte-identical** validity commitment
as long as it provides the canonical order — so ZenoDEX's validity layer is
portable and survives Tau changing its rules or failing to launch. (A full game
day additionally runs the production settlement engine on a real non-Tau
sequencer and replays proof receipts — see README.)

Uses the real `cpmm.swap_exact_in` + `compute_state_root`; imports nothing from
`src.integration` (the Tau shell). Isolated: not wired into any runtime.
"""

from __future__ import annotations

import dataclasses
from dataclasses import dataclass
from typing import Sequence

from src.core.cpmm import swap_exact_in
from src.core.liquidity import create_pool
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState
from src.state.state_root import compute_state_root


@dataclass(frozen=True)
class Swap:
    """An ordered settlement intent (asset0->asset1 if direction==0, else reverse)."""
    trader: str
    direction: int
    amount_in: int


def canonical_order(swaps: Sequence[Swap]) -> list[Swap]:
    """Deterministic, substrate-independent total order.

    A total key over participant-visible fields (amount, direction, trader id).
    This is the property that makes settlement portable: every substrate that
    applies *this* order computes the same result. (The grinding-resistance of
    the trader-id tie-break is the separate concern handled by
    `experiments/neutral_tiebreak_v1/`.)
    """
    return sorted(swaps, key=lambda s: (int(s.amount_in), int(s.direction), str(s.trader)))


def _apply(pool: PoolState, swap: Swap) -> PoolState:
    """Apply one swap to the pool via the REAL CPMM math (pure)."""
    if swap.direction == 0:
        _out, (r0, r1) = swap_exact_in(pool.reserve0, pool.reserve1, swap.amount_in, pool.fee_bps)
    elif swap.direction == 1:
        _out, (r1, r0) = swap_exact_in(pool.reserve1, pool.reserve0, swap.amount_in, pool.fee_bps)
    else:
        raise ValueError("direction must be 0 or 1")
    return dataclasses.replace(pool, reserve0=r0, reserve1=r1)


def settle_root(pool: PoolState, ordered: Sequence[Swap]) -> str:
    """Settle an ordered batch and return the REAL ZenoDEX state root.

    Pure function of (pool, ordered): no clock, no network, no Tau, no randomness.
    """
    for swap in ordered:
        pool = _apply(pool, swap)
    return compute_state_root(
        balances=BalanceTable(), pools={pool.pool_id: pool},
        lp_balances=LPTable(), nonces=NonceTable(),
    )


class Substrate:
    """An ordering substrate. Its ONLY job is to provide the batch order; the core
    settles it. Validity must not depend on which concrete substrate is used."""

    name = "abstract"

    def provide_order(self, swaps: Sequence[Swap]) -> list[Swap]:
        raise NotImplementedError


class LocalSequencerSubstrate(Substrate):
    name = "local-sequencer"

    def provide_order(self, swaps: Sequence[Swap]) -> list[Swap]:
        return canonical_order(swaps)


class TauCheckpointSubstrate(Substrate):
    name = "tau-checkpoint"

    def provide_order(self, swaps: Sequence[Swap]) -> list[Swap]:
        return canonical_order(swaps)


class NaiveSubmissionSubstrate(Substrate):
    """A NON-canonical substrate that settles in raw submission order. Included to
    show the requirement is real: portability holds *given canonical ordering*,
    which is exactly why a deterministic/canonical tie-break is load-bearing."""

    name = "naive-submission-order"

    def provide_order(self, swaps: Sequence[Swap]) -> list[Swap]:
        return list(swaps)


def settle_via(substrate: Substrate, pool: PoolState, swaps: Sequence[Swap]) -> str:
    return settle_root(pool, substrate.provide_order(swaps))


def demo_pool() -> PoolState:
    asset0 = "0x" + "0a" * 32
    asset1 = "0x" + "0b" * 32
    creator = "0x" + "11" * 48
    _pool_id, pool, _lp = create_pool(asset0, asset1, 1_000_000, 1_000_000, 30, creator)
    return pool
