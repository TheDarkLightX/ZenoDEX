"""Independent **semantic invariants** for the balance-accounting kernel.

Run against the Python authority alone (not a Python/Rust diff) so a bug present
identically in both runtimes is still caught. The headline properties are
**supply conservation** (transfers never change a per-asset total) and **only
the named keys change** (an op touches only the (account, asset) pairs it
references) — the balance-kernel form of the fee-router asset-scoping lesson.

See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import random
from collections import defaultdict

from src.core.balance_kernel import (
    MAX_BALANCE,
    BalanceAccepted,
    BalanceRejected,
    BalanceState,
    credit,
    transfer,
)

ACCTS = ["0x" + f"{tag:02x}" * 48 for tag in (0xA0, 0xB0, 0xC0)]
ASSETS = ["0x" + f"{tag:02x}" * 32 for tag in (0xAA, 0xBB)]


def _balances(state: BalanceState) -> dict:
    return {(e.pubkey, e.asset): e.amount for e in state.entries}


def _random_ops(seed: int, n: int = 250):
    rng = random.Random(seed)
    ops = []
    for _ in range(n):
        if rng.random() < 0.45:
            ops.append(("credit", None, rng.choice(ACCTS), rng.choice(ASSETS), rng.randint(1, 5000)))
        else:
            ops.append(
                (
                    "transfer",
                    rng.choice(ACCTS),
                    rng.choice(ACCTS),
                    rng.choice(ASSETS),
                    rng.randint(1, 5000),
                )
            )
    return ops


def _apply(state, op):
    kind, sender, recipient, asset, amount = op
    if kind == "credit":
        return credit(state=state, recipient=recipient, asset=asset, amount=amount)
    return transfer(state=state, sender=sender, recipient=recipient, asset=asset, amount=amount)


# --- I1: only the named keys change ------------------------------------------


def test_only_named_keys_change():
    state = BalanceState()
    for op in _random_ops(seed=1):
        before = _balances(state)
        result = _apply(state, op)
        if isinstance(result, BalanceAccepted):
            after = _balances(result.state)
            kind, sender, recipient, asset, _amount = op
            allowed = {(recipient, asset)}
            if kind == "transfer":
                allowed.add((sender, asset))
            changed = {k for k in set(before) | set(after) if before.get(k) != after.get(k)}
            assert changed <= allowed, f"op {op} changed unrelated keys: {changed - allowed}"
            state = result.state
        else:
            # Rejection is a no-op.
            assert _balances(state) == before


# --- I2: supply conservation (transfers conserve; credit adds exactly) --------


def test_per_asset_supply_equals_total_credited():
    state = BalanceState()
    credited: dict[str, int] = defaultdict(int)
    for op in _random_ops(seed=2):
        result = _apply(state, op)
        if isinstance(result, BalanceAccepted):
            if op[0] == "credit":
                credited[op[3]] += op[4]
            state = result.state
    for asset in ASSETS:
        supply = sum(state.balance_of(acct, asset) for acct in ACCTS)
        assert supply == credited[asset], f"supply drift for asset {asset[:8]}"


def test_transfer_conserves_supply_per_call():
    state = credit(state=BalanceState(), recipient=ACCTS[0], asset=ASSETS[0], amount=1000).state
    for op in _random_ops(seed=3):
        if op[0] != "transfer":
            continue
        asset = op[3]
        before = sum(state.balance_of(a, asset) for a in ACCTS)
        result = _apply(state, op)
        if isinstance(result, BalanceAccepted):
            after = sum(result.state.balance_of(a, asset) for a in ACCTS)
            assert after == before  # transfer never changes the per-asset total
            state = result.state


# --- I3: non-negativity, bounds, sparsity ------------------------------------


def test_balances_are_bounded_sparse_and_nonnegative():
    state = BalanceState()
    for op in _random_ops(seed=4):
        result = _apply(state, op)
        if isinstance(result, BalanceAccepted):
            state = result.state
    for e in state.entries:
        assert 1 <= e.amount <= MAX_BALANCE  # sparse: never stores 0, never exceeds MAX
    # No duplicate (pubkey, asset) keys.
    keys = [(e.pubkey, e.asset) for e in state.entries]
    assert len(keys) == len(set(keys))


# --- I4: rejection never changes state ---------------------------------------


def test_rejections_are_no_ops():
    state = credit(state=BalanceState(), recipient=ACCTS[0], asset=ASSETS[0], amount=100).state
    root = state.state_root()
    bad_ops = [
        ("transfer", ACCTS[0], ACCTS[0], ASSETS[0], 10),  # self
        ("transfer", ACCTS[0], ACCTS[1], ASSETS[0], 10_000),  # insufficient
        ("transfer", "0x11", ACCTS[1], ASSETS[0], 10),  # invalid sender
        ("credit", None, ACCTS[0], "0xbb", 10),  # invalid asset
        ("credit", None, ACCTS[0], ASSETS[0], 0),  # invalid amount
    ]
    for op in bad_ops:
        result = _apply(state, op)
        assert isinstance(result, BalanceRejected)
        assert state.state_root() == root
