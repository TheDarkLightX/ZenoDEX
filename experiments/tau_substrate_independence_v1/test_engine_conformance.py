"""Tests: the production settlement engine is substrate-order-independent.

Run: PYTHONPATH=. pytest experiments/tau_substrate_independence_v1/test_engine_conformance.py
"""

from __future__ import annotations

import hashlib
import random

import pytest

from engine_conformance import (
    AdversarialShuffleSubstrate,
    LocalSequencerSubstrate,
    TauCheckpointSubstrate,
    filled_count,
    settle_via,
    settlement_digest,
    trajectory_roots,
)
from src.core.batch_clearing import (
    _SWAP_ORDERING_GREEDY_AB_REFINED,
    _SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

ORDERINGS = [_SWAP_ORDERING_GREEDY_AB_REFINED, _SWAP_ORDERING_OPTIMAL_AB_BOUNDED]


def _pools():
    return {
        "p": PoolState(
            pool_id="p", asset0="A", asset1="B", reserve0=1_000_000, reserve1=1_000_000,
            fee_bps=30, lp_supply=1_000_000, status=PoolStatus.ACTIVE, created_at=0,
        )
    }


def _swap(label, sender, amt, ai="A", ao="B"):
    return Intent(
        module="TauSwap", version="0.1",
        intent_id="0x" + hashlib.sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey=sender, kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
        fields={"pool_id": "p", "asset_in": ai, "asset_out": ao,
                "amount_in": amt, "min_amount_out": 0},
    )


def _balances():
    b = BalanceTable()
    for s in ("alice", "bob", "carol", "dave", "erin", "frank"):
        b.set(s, "A", 1_000_000)
        b.set(s, "B", 1_000_000)
    return b


def _intents():
    return [
        _swap("i1", "alice", 5000),
        _swap("i2", "bob", 5000, ai="B", ao="A"),
        _swap("i3", "carol", 3000),
        _swap("i4", "dave", 7000, ai="B", ao="A"),
        _swap("i5", "erin", 5000),
        _swap("i6", "frank", 4000, ai="B", ao="A"),
    ]


def _digest(substrate, swap_ordering):
    return settlement_digest(
        settle_via(substrate, _intents(), _pools(), _balances(), LPTable(), swap_ordering=swap_ordering)
    )


def test_non_tau_substrates_match_tau_checkpoint():
    # Running the production engine under a non-Tau sequencer (local, or even an
    # adversarial shuffler) yields the BYTE-IDENTICAL settlement it would under Tau.
    n = len(_intents())
    perm = random.Random(13).sample(range(n), n)
    for so in ORDERINGS:
        tau = _digest(TauCheckpointSubstrate(), so)
        assert _digest(LocalSequencerSubstrate(), so) == tau
        assert _digest(AdversarialShuffleSubstrate(perm), so) == tau


def test_settlement_is_nonvacuous():
    # The invariance must be over a real, non-empty settlement (not vacuously equal).
    s = settle_via(TauCheckpointSubstrate(), _intents(), _pools(), _balances(), LPTable())
    assert filled_count(s) >= 2


def test_many_delivery_orders_are_invariant():
    n = len(_intents())
    rng = random.Random(99)
    for so in ORDERINGS:
        base = _digest(TauCheckpointSubstrate(), so)
        for _ in range(30):
            perm = rng.sample(range(n), n)
            assert _digest(AdversarialShuffleSubstrate(perm), so) == base


def test_adversarial_perm_must_be_valid():
    with pytest.raises(ValueError):
        AdversarialShuffleSubstrate([0, 0, 0, 0, 0, 0]).order(_intents())


def test_module_imports_no_tau_shell():
    # The validity layer this exercises must not depend on the Tau shell. Scan only
    # import statements (the docstring mentions src.integration on purpose).
    import inspect

    import engine_conformance

    for line in inspect.getsource(engine_conformance).splitlines():
        stripped = line.strip()
        if stripped.startswith(("import ", "from ")):
            assert "src.integration" not in stripped, f"Tau-shell import found: {line!r}"


# Valid canonical identities so the REAL compute_state_root accepts the carried
# state (48-byte hex pubkeys, 32-byte hex assets).
_TRAJ_ASSET0 = "0x" + "0a" * 32
_TRAJ_ASSET1 = "0x" + "0b" * 32
_TRAJ_POOL_ID = "0x" + "0c" * 32
_TRAJ_PKS = ["0x" + h * 48 for h in ("a1", "b2", "c3", "d4")]


def _traj_pools():
    return {
        _TRAJ_POOL_ID: PoolState(
            pool_id=_TRAJ_POOL_ID, asset0=_TRAJ_ASSET0, asset1=_TRAJ_ASSET1,
            reserve0=10_000_000, reserve1=10_000_000, fee_bps=30,
            lp_supply=10_000_000, status=PoolStatus.ACTIVE, created_at=0,
        )
    }


def _traj_balances():
    b = BalanceTable()
    for pk in _TRAJ_PKS:
        b.set(pk, _TRAJ_ASSET0, 100_000_000)
        b.set(pk, _TRAJ_ASSET1, 100_000_000)
    return b


def _traj_swap(label, pk, amt, direction):
    ai, ao = (_TRAJ_ASSET0, _TRAJ_ASSET1) if direction == 0 else (_TRAJ_ASSET1, _TRAJ_ASSET0)
    return Intent(
        module="TauSwap", version="0.1",
        intent_id="0x" + hashlib.sha256(label.encode("utf-8")).hexdigest(),
        sender_pubkey=pk, kind=IntentKind.SWAP_EXACT_IN, deadline=999999999,
        fields={"pool_id": _TRAJ_POOL_ID, "asset_in": ai, "asset_out": ao,
                "amount_in": amt, "min_amount_out": 0},
    )


def _traj_batches():
    # 3 batches, 4 mixed-direction swaps each; same senders across batches so the
    # carried state actually evolves between batches.
    return [
        [_traj_swap(f"b{r}-{i}", pk, 4000 + 500 * i, (i + r) % 2) for i, pk in enumerate(_TRAJ_PKS)]
        for r in range(3)
    ]


def test_multi_batch_trajectory_is_substrate_independent():
    # Run the SAME batch sequence through the production engine under a Tau
    # checkpoint vs non-Tau sequencers that reorder each batch. The per-batch
    # REAL state-root SEQUENCE must be byte-identical -> the full multi-batch
    # settlement trajectory is substrate-independent (the orderer cannot change it).
    batches = _traj_batches()
    tau = trajectory_roots(TauCheckpointSubstrate(), _traj_pools(), _traj_balances(), batches)
    local = trajectory_roots(LocalSequencerSubstrate(), _traj_pools(), _traj_balances(), batches)
    adv = trajectory_roots(AdversarialShuffleSubstrate([3, 1, 0, 2]), _traj_pools(), _traj_balances(), batches)
    assert tau == local == adv
    assert len(tau) == len(batches)
    assert len(set(tau)) >= 2  # non-vacuous: state actually evolves across the trajectory
