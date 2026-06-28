#!/usr/bin/env python3
"""Adversarial replay for coupled-capacity CoW exact DP.

This research checker strengthens the 2026-06-27 CoW capacity-DP breakthrough
with deterministic coupled-sender cases. It compares the bounded DP selector
against the brute-force oracle and records where DP improves on greedy.
"""

from __future__ import annotations

import json
import random
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_cow_search import (  # noqa: E402
    _CowSelectionContext,
    _assignment_balance_safe,
    _cow_pair_selection_key,
    _is_better_cow_pair_key,
    _partition_cow_candidates,
    _select_cow_pairs,
    _select_cow_pairs_bruteforce,
    _select_cow_pairs_capacity_dp,
    _select_cow_pairs_greedy,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "ce" * 32
SEED = 2026062805
PATTERN_COUNT = 5
VARIANTS_PER_PATTERN = 4


@dataclass(frozen=True)
class _CowCase:
    case_id: str
    pattern: str
    intents: list[Intent]
    balances: BalanceTable
    note: str


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _pool() -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _swap(
    intent_no: int,
    sender: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    min_amount_out: int,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_no),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": int(amount_in),
            "min_amount_out": int(min_amount_out),
        },
    )


def _add_balance(balances: BalanceTable, sender: str, asset: str, amount: int) -> None:
    balances.set(sender, asset, int(balances.get(sender, asset)) + int(amount))


def _case_from_rows(
    *,
    case_id: str,
    pattern: str,
    left_rows: list[tuple[int, str, int, int]],
    right_rows: list[tuple[int, str, int, int]],
    balances: BalanceTable,
    note: str,
) -> _CowCase:
    intents = [
        _swap(intent_no, sender, ASSET0, ASSET1, amount_in, min_out)
        for intent_no, sender, amount_in, min_out in left_rows
    ]
    intents.extend(
        _swap(intent_no, sender, ASSET1, ASSET0, amount_in, min_out)
        for intent_no, sender, amount_in, min_out in right_rows
    )
    return _CowCase(
        case_id=case_id,
        pattern=pattern,
        intents=intents,
        balances=balances,
        note=note,
    )


def _shared_left_case(variant: int) -> _CowCase:
    balances = BalanceTable()
    coupled = _sender(20 + variant)
    right_a = _sender(40 + variant)
    right_b = _sender(50 + variant)
    right_c = _sender(60 + variant)
    balances.set(coupled, ASSET0, 210 + 15 * variant)
    for sender, amount in ((right_a, 92), (right_b, 230), (right_c, 140)):
        balances.set(sender, ASSET1, amount + 5 * variant)
    left_rows = [
        (10_000 + variant * 100, coupled, 110 + variant, 90),
        (10_001 + variant * 100, coupled, 215 + 3 * variant, 84),
        (10_002 + variant * 100, _sender(70 + variant), 35, 500),
        (10_003 + variant * 100, _sender(80 + variant), 45, 500),
        (10_004 + variant * 100, _sender(90 + variant), 55, 500),
    ]
    for intent_no, sender, amount_in, _min_out in left_rows[2:]:
        _add_balance(balances, sender, ASSET0, amount_in)
    right_rows = [
        (11_000 + variant * 100, right_a, 92 + variant, 105),
        (11_001 + variant * 100, right_b, 230 + 5 * variant, 180),
        (11_002 + variant * 100, right_c, 140 + 3 * variant, 120),
        (11_003 + variant * 100, _sender(100 + variant), 35, 500),
        (11_004 + variant * 100, _sender(110 + variant), 45, 500),
    ]
    for _intent_no, sender, amount_in, _min_out in right_rows[3:]:
        _add_balance(balances, sender, ASSET1, amount_in)
    return _case_from_rows(
        case_id=f"shared_left_{variant}",
        pattern="shared_left",
        left_rows=left_rows,
        right_rows=right_rows,
        balances=balances,
        note="One asset0 sender is capacity-coupled across multiple feasible pairs.",
    )


def _shared_right_case(variant: int) -> _CowCase:
    balances = BalanceTable()
    right_coupled = _sender(130 + variant)
    balances.set(right_coupled, ASSET1, 225 + 7 * variant)
    left_rows: list[tuple[int, str, int, int]] = []
    for idx, amount in enumerate((95, 180, 245, 60, 75)):
        sender = _sender(150 + variant * 10 + idx)
        balances.set(sender, ASSET0, amount + idx)
        left_rows.append(
            (
                12_000 + variant * 100 + idx,
                sender,
                amount + idx,
                70 + (idx % 3) * 25,
            )
        )
    right_rows = [
        (13_000 + variant * 100, right_coupled, 100 + variant, 90),
        (13_001 + variant * 100, right_coupled, 220 + 3 * variant, 150),
        (13_002 + variant * 100, _sender(170 + variant), 55, 500),
        (13_003 + variant * 100, _sender(180 + variant), 65, 500),
        (13_004 + variant * 100, _sender(190 + variant), 75, 500),
    ]
    for _intent_no, sender, amount_in, _min_out in right_rows[2:]:
        _add_balance(balances, sender, ASSET1, amount_in)
    return _case_from_rows(
        case_id=f"shared_right_{variant}",
        pattern="shared_right",
        left_rows=left_rows,
        right_rows=right_rows,
        balances=balances,
        note="One asset1 sender is capacity-coupled across multiple feasible pairs.",
    )


def _dual_coupled_case(variant: int) -> _CowCase:
    balances = BalanceTable()
    left_coupled = _sender(210 + variant)
    right_coupled = _sender(220 + variant)
    balances.set(left_coupled, ASSET0, 300 + 11 * variant)
    balances.set(right_coupled, ASSET1, 295 + 9 * variant)
    left_rows = [
        (14_000 + variant * 100, left_coupled, 95 + variant, 80),
        (14_001 + variant * 100, left_coupled, 140 + 2 * variant, 120),
        (14_002 + variant * 100, left_coupled, 210 + 3 * variant, 190),
        (14_003 + variant * 100, _sender(230 + variant), 85, 70),
        (14_004 + variant * 100, _sender(240 + variant), 72, 60),
        (14_005 + variant * 100, _sender(250 + variant), 50, 700),
    ]
    for _intent_no, sender, amount_in, _min_out in left_rows[3:]:
        _add_balance(balances, sender, ASSET0, amount_in)
    right_rows = [
        (15_000 + variant * 100, right_coupled, 100 + variant, 80),
        (15_001 + variant * 100, right_coupled, 150 + 2 * variant, 115),
        (15_002 + variant * 100, right_coupled, 205 + 3 * variant, 185),
        (15_003 + variant * 100, _sender(260 + variant), 90, 75),
        (15_004 + variant * 100, _sender(270 + variant), 76, 65),
        (15_005 + variant * 100, _sender(280 + variant), 50, 700),
    ]
    for _intent_no, sender, amount_in, _min_out in right_rows[3:]:
        _add_balance(balances, sender, ASSET1, amount_in)
    return _case_from_rows(
        case_id=f"dual_coupled_{variant}",
        pattern="dual_coupled",
        left_rows=left_rows,
        right_rows=right_rows,
        balances=balances,
        note="Both sides have repeated senders and infeasible decoy edges.",
    )


def _sparse_cliff_case(variant: int) -> _CowCase:
    balances = BalanceTable()
    left_coupled = _sender(310 + variant)
    right_coupled = _sender(320 + variant)
    balances.set(left_coupled, ASSET0, 260 + 5 * variant)
    balances.set(right_coupled, ASSET1, 250 + 7 * variant)
    left_rows: list[tuple[int, str, int, int]] = []
    right_rows: list[tuple[int, str, int, int]] = []
    for idx, amount in enumerate((90, 130, 190, 45, 55, 65)):
        sender = left_coupled if idx < 3 else _sender(330 + variant * 10 + idx)
        if sender != left_coupled:
            balances.set(sender, ASSET0, amount)
        left_rows.append(
            (
                16_000 + variant * 100 + idx,
                sender,
                amount + variant,
                80 + idx * 25,
            )
        )
    for idx, amount in enumerate((85, 135, 205, 40, 50, 60)):
        sender = right_coupled if idx < 3 else _sender(350 + variant * 10 + idx)
        if sender != right_coupled:
            balances.set(sender, ASSET1, amount)
        right_rows.append(
            (
                17_000 + variant * 100 + idx,
                sender,
                amount + variant,
                75 + idx * 27,
            )
        )
    return _case_from_rows(
        case_id=f"sparse_cliff_{variant}",
        pattern="sparse_cliff",
        left_rows=left_rows,
        right_rows=right_rows,
        balances=balances,
        note="Minimum-output cliffs create a sparse feasible graph.",
    )


def _deterministic_fuzz_case(variant: int) -> _CowCase:
    rng = random.Random(SEED + variant)
    balances = BalanceTable()
    left_senders = [_sender(410 + variant), _sender(420 + variant), _sender(430 + variant)]
    right_senders = [_sender(510 + variant), _sender(520 + variant), _sender(530 + variant)]
    for sender in left_senders:
        balances.set(sender, ASSET0, 170 + rng.randrange(0, 90))
    for sender in right_senders:
        balances.set(sender, ASSET1, 165 + rng.randrange(0, 90))
    left_rows: list[tuple[int, str, int, int]] = []
    right_rows: list[tuple[int, str, int, int]] = []
    for idx in range(7):
        sender = left_senders[idx % len(left_senders)]
        amount = 55 + rng.randrange(0, 115)
        min_out = 35 + rng.randrange(0, 120)
        left_rows.append((18_000 + variant * 100 + idx, sender, amount, min_out))
    for idx in range(7):
        sender = right_senders[(idx + 1) % len(right_senders)]
        amount = 50 + rng.randrange(0, 120)
        min_out = 30 + rng.randrange(0, 125)
        right_rows.append((19_000 + variant * 100 + idx, sender, amount, min_out))
    return _case_from_rows(
        case_id=f"deterministic_fuzz_{variant}",
        pattern="deterministic_fuzz",
        left_rows=left_rows,
        right_rows=right_rows,
        balances=balances,
        note="Seeded small coupled-capacity graph with repeated senders.",
    )


def _cases() -> list[_CowCase]:
    builders = (
        _shared_left_case,
        _shared_right_case,
        _dual_coupled_case,
        _sparse_cliff_case,
        _deterministic_fuzz_case,
    )
    return [builder(variant) for builder in builders for variant in range(VARIANTS_PER_PATTERN)]


def _pair_ids(pairs: list[tuple[Any, Any]]) -> list[tuple[str, str]]:
    return [(left.intent.intent_id, right.intent.intent_id) for left, right in pairs]


def _case_result(case: _CowCase) -> dict[str, Any]:
    pool = _pool()
    partition = _partition_cow_candidates(case.intents, pool)
    context = _CowSelectionContext(balances=case.balances, asset0=ASSET0, asset1=ASSET1)
    started = time.perf_counter()
    greedy_pairs = _select_cow_pairs_greedy(partition.side_01, partition.side_10, context=context)
    greedy_s = time.perf_counter() - started
    started = time.perf_counter()
    dp_pairs = _select_cow_pairs_capacity_dp(partition.side_01, partition.side_10, context=context)
    dp_s = time.perf_counter() - started
    started = time.perf_counter()
    brute_pairs = _select_cow_pairs_bruteforce(
        partition.side_01,
        partition.side_10,
        context=context,
    )
    brute_s = time.perf_counter() - started
    selected_pairs = _select_cow_pairs(partition.side_01, partition.side_10, context=context)

    greedy_key = _cow_pair_selection_key(greedy_pairs)
    dp_key = _cow_pair_selection_key(dp_pairs)
    brute_key = _cow_pair_selection_key(brute_pairs)
    selected_key = _cow_pair_selection_key(selected_pairs)
    dp_beats_greedy = _is_better_cow_pair_key(dp_key, greedy_key)
    assignment_safe = _assignment_balance_safe(
        partition.side_01,
        partition.side_10,
        context=context,
    )
    return {
        "case_id": case.case_id,
        "pattern": case.pattern,
        "note": case.note,
        "candidate_count": len(partition.side_01) + len(partition.side_10),
        "side_01": len(partition.side_01),
        "side_10": len(partition.side_10),
        "assignment_balance_safe": assignment_safe,
        "dp_matches_bruteforce": dp_key == brute_key,
        "core_selector_matches_dp": selected_key == dp_key,
        "dp_beats_greedy": dp_beats_greedy,
        "volume_lift": int(dp_key[0]) - int(greedy_key[0]),
        "surplus_lift": int(dp_key[1]) - int(greedy_key[1]),
        "greedy_key": greedy_key,
        "dp_key": dp_key,
        "bruteforce_key": brute_key,
        "selected_key": selected_key,
        "greedy_pair_ids": _pair_ids(greedy_pairs),
        "dp_pair_ids": _pair_ids(dp_pairs),
        "bruteforce_pair_ids": _pair_ids(brute_pairs),
        "timing_ms": {
            "greedy": round(greedy_s * 1000.0, 3),
            "capacity_dp": round(dp_s * 1000.0, 3),
            "bruteforce": round(brute_s * 1000.0, 3),
        },
    }


def build_report() -> dict[str, Any]:
    started = time.perf_counter()
    rows = [_case_result(case) for case in _cases()]
    exact_mismatches = [row for row in rows if not row["dp_matches_bruteforce"]]
    core_mismatches = [row for row in rows if not row["core_selector_matches_dp"]]
    assignment_safe_rows = [row for row in rows if row["assignment_balance_safe"]]
    lift_rows = [row for row in rows if row["dp_beats_greedy"]]
    return {
        "schema": "zenodex/cow_capacity_dp_adversarial/v1",
        "ok": (
            not exact_mismatches
            and not core_mismatches
            and not assignment_safe_rows
            and len(lift_rows) >= 8
        ),
        "seed": SEED,
        "case_count": len(rows),
        "pattern_count": PATTERN_COUNT,
        "variants_per_pattern": VARIANTS_PER_PATTERN,
        "exact_mismatch_count": len(exact_mismatches),
        "core_mismatch_count": len(core_mismatches),
        "assignment_safe_case_count": len(assignment_safe_rows),
        "greedy_lift_case_count": len(lift_rows),
        "max_candidate_count": max(row["candidate_count"] for row in rows),
        "max_volume_lift": max(row["volume_lift"] for row in rows),
        "max_surplus_lift": max(row["surplus_lift"] for row in rows),
        "pattern_summary": _pattern_summary(rows),
        "first_mismatch": (
            exact_mismatches or core_mismatches or assignment_safe_rows or [None]
        )[0],
        "cases": rows,
        "non_claims": [
            "This is a deterministic adversarial research checker, not production activation.",
            "The result is bounded to small coupled-capacity CoW batches.",
            "It does not claim a polynomial algorithm for arbitrary grouped-capacity matching.",
            "Settlement authority remains with fail-closed materialization and balance checks.",
        ],
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def _pattern_summary(rows: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    summary: dict[str, dict[str, int]] = {}
    for row in rows:
        pattern = str(row["pattern"])
        current = summary.setdefault(
            pattern,
            {"cases": 0, "exact_mismatches": 0, "core_mismatches": 0, "greedy_lifts": 0},
        )
        current["cases"] += 1
        current["exact_mismatches"] += int(not row["dp_matches_bruteforce"])
        current["core_mismatches"] += int(not row["core_selector_matches_dp"])
        current["greedy_lifts"] += int(bool(row["dp_beats_greedy"]))
    return summary


def main() -> int:
    report = build_report()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
