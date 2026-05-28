"""Independent **semantic invariants** for the buyback/burn accounting rails.

Asserted against the authoritative ``src/core/burn_receipts.py`` rails alone
(not a Python/Rust diff). They pin the buyback-accounting intent: a burn never
exceeds its budget (burn floor), reduces supply by exactly the burned amount
(supply conservation), and adds exactly that amount to the public accumulator
(batch sum); a no-burn step is inert.

See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
for _p in (str(REPO), str(TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import burn_receipts_lib as b  # noqa: E402


def _accept(tx) -> bool:
    return b.apply_tx(tx)[0]


# --- I1: budget floor — a valid burn never exceeds its budget -----------------


def test_valid_burn_requires_budget_at_least_amount():
    for amount in (1, 10, 100, 0x7FFF):
        # Supply large enough that the supply rail is not the binding constraint.
        assert _accept(b._burn(amount, budget=amount, supply=0xFFFF))  # budget == amount
        if amount + 1 <= 0x7FFF:
            assert _accept(b._burn(amount, budget=amount + 1, supply=0xFFFF))  # budget > amount
        if amount > 1:
            assert not _accept(b._burn(amount, budget=amount - 1, supply=0xFFFF))  # budget < amount


# --- I2: supply conservation — burn reduces supply by exactly burn_amount -----


def test_supply_conservation():
    rng = random.Random(7)
    for _ in range(200):
        amount = rng.randint(1, 200)
        supply = rng.randint(amount, 0xFFFF)
        tx = b._burn(amount, supply=supply)
        # The committed tx asserts supply_after == supply_before - amount.
        assert tx["supply_after"] == tx["supply_before"] - amount
        assert _accept(tx)
        # Any other supply_after must be rejected.
        bad = {**tx, "supply_after": tx["supply_after"] + 1}
        assert not _accept(bad)


# --- I3: accumulator — batch sum grows by exactly burn_amount -----------------


def test_batch_accumulator_adds_burn():
    rng = random.Random(11)
    for _ in range(200):
        amount = rng.randint(1, 200)
        batch = rng.randint(0, 0x7000)
        tx = b._burn(amount, batch=batch, supply=0xFFFF)
        assert tx["batch_burn_sum_after"] == tx["batch_burn_sum_before"] + amount
        assert _accept(tx)
        bad = {**tx, "batch_burn_sum_after": batch}  # no growth
        assert not _accept(bad)


# --- I4: no-burn is inert (supply and accumulator unchanged, no payout) -------


def test_no_burn_is_inert():
    tx = b._no_burn(supply=500, batch=42)
    assert _accept(tx)
    assert tx["supply_after"] == tx["supply_before"]
    assert tx["batch_burn_sum_after"] == tx["batch_burn_sum_before"]
    # A no-burn step that nonetheless moves supply or burns is rejected.
    assert not _accept({**tx, "supply_after": 499})
    assert not _accept({**tx, "burn_amount": 1})


# --- I5: replay gate — burning requires bound receipt, unused nullifier, policy


def test_burn_requires_all_replay_flags():
    base = b._burn(10)
    assert _accept(base)
    for flag in ("receipt_bound", "nullifier_unused", "policy_ok"):
        assert not _accept({**base, flag: 0})
