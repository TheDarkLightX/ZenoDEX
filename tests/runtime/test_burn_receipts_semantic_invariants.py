"""Independent **semantic invariants** for the buyback/burn accounting rails.

Asserted against the authoritative ``src/core/burn_receipts.py`` rails alone
(not a Python/Rust diff). They pin the buyback-accounting intent: a burn never
exceeds its budget (burn floor), reduces supply by exactly the burned amount
(supply conservation), and adds exactly that amount to the public accumulator
(batch sum); a no-burn step is inert.

See docs/runtime/SEMANTIC_DRIFT_CONTROLS.md.
"""

from __future__ import annotations

import itertools
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


def _expected_rail_result(tx: dict) -> tuple[bool, str | None]:
    vals = [tx.get(key) for key in b._FIELDS]
    if any(not isinstance(value, int) or isinstance(value, bool) for value in vals):
        return False, b.REJ_BAD_NUMERIC_FIELD
    d = dict(zip(b._FIELDS, vals, strict=True))

    if d["do_burn"] not in (0, 1):
        return False, b.REJ_REPLAY
    for flag in ("receipt_bound", "nullifier_unused", "policy_ok"):
        if d[flag] not in (0, 1):
            return False, b.REJ_REPLAY
    if d["do_burn"] == 1 and not (
        d["receipt_bound"] == 1 and d["nullifier_unused"] == 1 and d["policy_ok"] == 1
    ):
        return False, b.REJ_REPLAY

    for field in ("burn_amount", "receipt_amount", "burn_budget"):
        if d[field] < 0 or d[field] > 0x7FFF:
            return False, b.REJ_AMOUNT
    if d["do_burn"] == 0:
        if d["burn_amount"] != 0 or d["receipt_amount"] != 0:
            return False, b.REJ_AMOUNT
    elif not (
        d["burn_amount"] > 0
        and d["burn_amount"] == d["receipt_amount"]
        and d["burn_budget"] >= d["burn_amount"]
    ):
        return False, b.REJ_AMOUNT

    for field in ("supply_before", "supply_after"):
        if d[field] < 0 or d[field] > 0xFFFF:
            return False, b.REJ_SUPPLY
    if d["do_burn"] == 0:
        if d["supply_after"] != d["supply_before"]:
            return False, b.REJ_SUPPLY
    elif not (
        d["supply_before"] >= d["burn_amount"]
        and d["supply_after"] == d["supply_before"] - d["burn_amount"]
    ):
        return False, b.REJ_SUPPLY

    if d["batch_burn_sum_before"] < 0 or d["batch_burn_sum_before"] > 0x7FFF:
        return False, b.REJ_BATCH
    if d["batch_burn_sum_after"] < 0 or d["batch_burn_sum_after"] > 0xFFFF:
        return False, b.REJ_BATCH
    if d["do_burn"] == 0:
        if d["batch_burn_sum_after"] != d["batch_burn_sum_before"]:
            return False, b.REJ_BATCH
    elif d["batch_burn_sum_after"] != d["batch_burn_sum_before"] + d["burn_amount"]:
        return False, b.REJ_BATCH
    return True, None


def test_exhaustive_burn_rail_boundary_lattice_classifies_all_cases():
    """Complete over a declared integer rail lattice.

    The grid preserves the rail tuple shape and varies the host flags, burn
    amount, receipt amount, budget, supply edge, and batch-accumulator edge over
    small boundary alphabets. The oracle below is a direct statement of the rail
    contract and reject order, independent of the production rail helpers.
    """
    cases: set[tuple[int, ...]] = set()
    for do_burn in (0, 1, 2):
        for receipt_bound, nullifier_unused, policy_ok in itertools.product(
            (0, 1),
            repeat=3,
        ):
            for burn_amount in (0, 1, 2, 0x7FFF, 0x8000):
                receipt_amount_values = {0, burn_amount, burn_amount + 1, 0x8000}
                burn_budget_values = {0, burn_amount - 1, burn_amount, 0x7FFF, 0x8000}
                supply_before_values = {0, burn_amount, burn_amount + 1, 0x10000}
                for receipt_amount, burn_budget, supply_before in itertools.product(
                    receipt_amount_values,
                    burn_budget_values,
                    supply_before_values,
                ):
                    supply_after_values = {
                        supply_before,
                        supply_before - burn_amount,
                        supply_before - burn_amount + 1,
                        0x10000,
                    }
                    for supply_after in supply_after_values:
                        for batch_before in (0, 0x7FFF, 0x8000):
                            batch_after_values = {
                                batch_before,
                                batch_before + burn_amount,
                                batch_before + burn_amount + 1,
                                0x10000,
                            }
                            for batch_after in batch_after_values:
                                cases.add(
                                    (
                                        do_burn,
                                        receipt_bound,
                                        nullifier_unused,
                                        policy_ok,
                                        burn_amount,
                                        receipt_amount,
                                        burn_budget,
                                        supply_before,
                                        supply_after,
                                        batch_before,
                                        batch_after,
                                    )
                                )

    assert len(cases) == 237_744
    outcomes: dict[str, int] = {}
    for vals in cases:
        tx = dict(zip(b._FIELDS, vals, strict=True))
        expected_accept, expected_reason = _expected_rail_result(tx)
        actual_accept, actual_reason, _actual_vals = b.apply_tx(tx)
        assert (actual_accept, actual_reason) == (expected_accept, expected_reason), tx
        key = "ok" if actual_accept else str(actual_reason)
        outcomes[key] = outcomes.get(key, 0) + 1
        if actual_accept:
            assert tx["supply_before"] - tx["supply_after"] == tx["burn_amount"]
            assert tx["batch_burn_sum_after"] - tx["batch_burn_sum_before"] == tx["burn_amount"]

    assert outcomes["ok"] > 0
    assert {
        b.REJ_REPLAY,
        b.REJ_AMOUNT,
        b.REJ_SUPPLY,
        b.REJ_BATCH,
    } <= set(outcomes)
