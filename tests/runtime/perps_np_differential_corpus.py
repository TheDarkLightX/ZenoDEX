"""Hostile corpus for the P0-3 perps-NP guest<->authority differential.

Each case is a list of guest actions (the same JSON shape the
`tau_state_transition_execute` schema accepts) applied FROM SCRATCH (every case
begins with ``init_market``), so neither side needs a seeded pre-state. The
harness drives the SAME actions through the live Python authority and the
host-executed guest and requires observational equivalence.

Fixtures kept separate from the test so a reviewer can audit the corpus.
"""

from __future__ import annotations

import hashlib
from typing import Any

from tools.runtime.perps_np_guest_differential import valid_collateral_binding

OWNER_A = "0x" + "aa" * 48
OWNER_B = "0x" + "bb" * 48
OWNER_C = "0x" + "cc" * 48
OWNER_D = "0x" + "dd" * 48
E8 = 100_000_000


def _h32(seed: str) -> str:
    return hashlib.sha256(seed.encode()).hexdigest()


def init(*, index_e8: int = 1 * E8, insurance_e8: int = 0) -> dict[str, Any]:
    return {
        "kind": "init_market",
        "market_id": "ZENO-PERP",
        "index_price_e8": index_e8,
        "insurance_seed_e8": insurance_e8,
    }


def deposit(pubkey: str, amount_e8: int, nonce: int) -> dict[str, Any]:
    return {
        "kind": "deposit_collateral",
        "pubkey": pubkey,
        "amount_e8": amount_e8,
        "nonce": nonce,
        "collateral_binding": valid_collateral_binding(f"{pubkey}:{nonce}"),
    }


def withdraw(pubkey: str, amount_e8: int, nonce: int) -> dict[str, Any]:
    return {
        "kind": "withdraw_collateral",
        "pubkey": pubkey,
        "amount_e8": amount_e8,
        "nonce": nonce,
    }


def oracle(price_e8: int) -> dict[str, Any]:
    return {
        "oracle_bridge_id": "perps-np-differential-oracle",
        "oracle_bridge_hash": _h32("oracle_bridge"),
        "price_e8": price_e8,
        "price_timestamp": 0,
        "max_staleness_seconds": 3600,
        "observed_at": 0,
        "pre_price_batch_commitment": _h32("pre_price_batch"),
    }


def intent(pubkey: str, target_base: int, nonce: int, *, limit_price_e8: int = 0) -> dict[str, Any]:
    return {
        "pubkey": pubkey,
        "target_base": target_base,
        "limit_price_e8": limit_price_e8,
        "min_fill_base": 0,
        "expiry_epoch": 1 << 62,
        "nonce": nonce,
    }


def run_epoch(clearing_e8: int, funding_bps: int, intents: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    return {
        "kind": "run_epoch",
        "oracle": oracle(clearing_e8),
        "clearing_price_e8": clearing_e8,
        "funding_rate_bps": funding_bps,
        "intents": list(intents or []),
    }


# Cases that BOTH sides must accept and end observationally equivalent.
CORPUS: list[dict[str, Any]] = [
    {"name": "deposit_one_account", "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1)]},
    {
        "name": "deposit_then_partial_withdraw",
        "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1), withdraw(OWNER_A, 2_000 * E8, 2)],
    },
    {
        "name": "deposit_then_full_withdraw_account_leaves",
        "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1), withdraw(OWNER_A, 5_000 * E8, 2)],
    },
    {
        "name": "two_accounts_join",
        "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1), deposit(OWNER_B, 3_000 * E8, 1)],
    },
    {
        "name": "run_epoch_four_wallets_no_intents_no_positions",
        "actions": [
            init(insurance_e8=1_000 * E8),
            deposit(OWNER_A, 5_000 * E8, 1),
            deposit(OWNER_B, 5_000 * E8, 1),
            deposit(OWNER_C, 5_000 * E8, 1),
            deposit(OWNER_D, 5_000 * E8, 1),
            run_epoch(1 * E8, 0),
        ],
    },
    {
        "name": "run_epoch_four_wallet_net_zero_match",
        "actions": [
            init(insurance_e8=1_000 * E8),
            deposit(OWNER_A, 5_000 * E8, 1),
            deposit(OWNER_B, 5_000 * E8, 1),
            deposit(OWNER_C, 5_000 * E8, 1),
            deposit(OWNER_D, 5_000 * E8, 1),
            run_epoch(
                1 * E8,
                0,
                [
                    intent(OWNER_A, 10, 2),
                    intent(OWNER_B, 6, 2),
                    intent(OWNER_C, -8, 2),
                    intent(OWNER_D, -8, 2),
                ],
            ),
        ],
    },
    {
        "name": "match_then_price_move_funding",
        "actions": [
            init(insurance_e8=2_000 * E8),
            deposit(OWNER_A, 8_000 * E8, 1),
            deposit(OWNER_B, 8_000 * E8, 1),
            deposit(OWNER_C, 8_000 * E8, 1),
            deposit(OWNER_D, 8_000 * E8, 1),
            run_epoch(
                1 * E8,
                0,
                [
                    intent(OWNER_A, 10, 2),
                    intent(OWNER_B, 6, 2),
                    intent(OWNER_C, -8, 2),
                    intent(OWNER_D, -8, 2),
                ],
            ),
            run_epoch(101_000_000, 10),  # +1% mark move + funding on the open book
        ],
    },
    {
        "name": "four_accounts_largest_remainder_net_zero",
        "actions": [
            init(insurance_e8=2_000 * E8),
            deposit(OWNER_A, 8_000 * E8, 1),
            deposit(OWNER_B, 8_000 * E8, 1),
            deposit(OWNER_C, 8_000 * E8, 1),
            deposit(OWNER_D, 8_000 * E8, 1),
            run_epoch(
                1 * E8,
                0,
                [
                    intent(OWNER_A, 12, 2),
                    intent(OWNER_B, 5, 2),
                    intent(OWNER_C, -10, 2),
                    intent(OWNER_D, -7, 2),
                ],
            ),
        ],
    },
]

# Cases that BOTH sides must REJECT, for the same semantic reason CLASS.
REJECT_CORPUS: list[dict[str, Any]] = [
    {
        "name": "withdraw_exceeds_collateral",
        "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1), withdraw(OWNER_A, 9_000 * E8, 2)],
        "expect_class": "insufficient_collateral_or_balance",
    },
    # --- P0-3b strict-sequential regression cases (2026-06-06) ----------------
    # Before the guest was fixed (surfaces.rs: was `nonce <= account.nonce`,
    # MONOTONE), it ACCEPTED a GAP nonce that the live chain replay authority
    # (replay_guard.admit, strict-sequential) REJECTS -- the guest was more
    # permissive than the chain. These cases pin the fix: a gap and a duplicate
    # nonce now fail closed on BOTH sides for the same class, so the differential
    # would re-fail if the guest ever regressed to monotone.
    {
        "name": "deposit_gap_nonce_rejected_strict_sequential",
        "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1), deposit(OWNER_A, 1_000 * E8, 3)],
        "expect_class": "nonce_or_replay",
    },
    {
        "name": "deposit_duplicate_nonce_rejected",
        "actions": [init(), deposit(OWNER_A, 5_000 * E8, 1), deposit(OWNER_A, 1_000 * E8, 1)],
        "expect_class": "nonce_or_replay",
    },
    {
        "name": "withdraw_gap_nonce_rejected_strict_sequential",
        "actions": [
            init(),
            deposit(OWNER_A, 5_000 * E8, 1),
            withdraw(OWNER_A, 1_000 * E8, 4),
        ],
        "expect_class": "nonce_or_replay",
    },
]
