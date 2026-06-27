#!/usr/bin/env python3
"""Replay the capacity-coupled CoW exact-DP breakthrough."""

from __future__ import annotations

import argparse
import json
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
from src.core.settlement import Fill  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_cow_capacity_dp_breakthrough_20260627"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_COW_CAPACITY_DP_BREAKTHROUGH_20260627.md"

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "cf" * 32


@dataclass(frozen=True)
class CowCapacityCase:
    case_id: str
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


def _swap(intent_no: int, sender: str, asset_in: str, asset_out: str, amount_in: int, min_amount_out: int) -> Intent:
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


def _volume_witness() -> CowCapacityCase:
    balances = BalanceTable()
    coupled = _sender(91)
    balances.set(coupled, ASSET0, 200)
    balances.set(_sender(101), ASSET1, 90)
    balances.set(_sender(102), ASSET1, 200)
    for sender_no in (92, 93, 94):
        balances.set(_sender(sender_no), ASSET0, 10)
    for sender_no in (103, 104):
        balances.set(_sender(sender_no), ASSET1, 10)
    return CowCapacityCase(
        case_id="coupled_sender_volume_witness",
        intents=[
            _swap(1410, coupled, ASSET0, ASSET1, 100, 90),
            _swap(1411, coupled, ASSET0, ASSET1, 200, 80),
            _swap(1412, _sender(101), ASSET1, ASSET0, 90, 100),
            _swap(1413, _sender(102), ASSET1, ASSET0, 200, 190),
            _swap(1414, _sender(92), ASSET0, ASSET1, 10, 1_000),
            _swap(1415, _sender(93), ASSET0, ASSET1, 10, 1_000),
            _swap(1416, _sender(94), ASSET0, ASSET1, 10, 1_000),
            _swap(1417, _sender(103), ASSET1, ASSET0, 10, 1_000),
            _swap(1418, _sender(104), ASSET1, ASSET0, 10, 1_000),
        ],
        balances=balances,
        note="Greedy consumes the coupled sender on a smaller feasible pair; exact DP keeps capacity for the higher-volume pair.",
    )


def _surplus_witness() -> CowCapacityCase:
    balances = BalanceTable()
    for sender_no in (41, 42, 43, 44, 45):
        balances.set(_sender(sender_no), ASSET0, 100)
    balances.set(_sender(51), ASSET1, 100)
    balances.set(_sender(52), ASSET1, 0)
    balances.set(_sender(53), ASSET1, 100)
    balances.set(_sender(54), ASSET1, 100)
    return CowCapacityCase(
        case_id="surplus_witness",
        intents=[
            _swap(1380, _sender(41), ASSET0, ASSET1, 150, 90),
            _swap(1381, _sender(42), ASSET0, ASSET1, 100, 80),
            _swap(1382, _sender(43), ASSET0, ASSET1, 100, 300),
            _swap(1383, _sender(44), ASSET0, ASSET1, 100, 50),
            _swap(1384, _sender(45), ASSET0, ASSET1, 100, 40),
            _swap(1385, _sender(51), ASSET1, ASSET0, 100, 50),
            _swap(1386, _sender(52), ASSET1, ASSET0, 100, 50),
            _swap(1387, _sender(53), ASSET1, ASSET0, 10, 200),
            _swap(1388, _sender(54), ASSET1, ASSET0, 10, 200),
        ],
        balances=balances,
        note="Exact DP chooses the same volume with better surplus after filtering infeasible and overdrawn candidates.",
    )


def _parity_case(seed: int) -> CowCapacityCase:
    balances = BalanceTable()
    coupled0 = _sender(120 + seed)
    coupled1 = _sender(140 + seed)
    balances.set(coupled0, ASSET0, 220)
    balances.set(coupled1, ASSET1, 210)
    intents: list[Intent] = []
    for idx in range(4):
        amount = 65 + ((seed * 19 + idx * 31) % 85)
        min_out = 45 + ((seed * 11 + idx * 13) % 65)
        sender = coupled0 if idx < 3 else _sender(160 + seed * 10 + idx)
        if sender != coupled0:
            balances.set(sender, ASSET0, amount)
        intents.append(_swap(5_000 + seed * 100 + idx, sender, ASSET0, ASSET1, amount, min_out))
    for idx in range(5):
        amount = 55 + ((seed * 23 + idx * 17) % 95)
        min_out = 35 + ((seed * 7 + idx * 19) % 75)
        sender = coupled1 if idx < 3 else _sender(180 + seed * 10 + idx)
        if sender != coupled1:
            balances.set(sender, ASSET1, amount)
        intents.append(_swap(6_000 + seed * 100 + idx, sender, ASSET1, ASSET0, amount, min_out))
    return CowCapacityCase(
        case_id=f"parity_seed_{seed}",
        intents=intents,
        balances=balances,
        note="Deterministic coupled-capacity parity case against brute force.",
    )


def cases() -> tuple[CowCapacityCase, ...]:
    return (_volume_witness(), _surplus_witness(), _parity_case(1), _parity_case(2), _parity_case(3))


def _timed(fn: Any) -> tuple[Any, float]:
    started = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - started


def _pair_ids(pairs: list[tuple[Any, Any]]) -> list[tuple[str, str]]:
    return [(left.intent.intent_id, right.intent.intent_id) for left, right in pairs]


def _case_result(case: CowCapacityCase) -> dict[str, Any]:
    pool = _pool()
    partition = _partition_cow_candidates(case.intents, pool)
    context = _CowSelectionContext(balances=case.balances, asset0=ASSET0, asset1=ASSET1)
    greedy_pairs, greedy_s = _timed(lambda: _select_cow_pairs_greedy(partition.side_01, partition.side_10, context=context))
    dp_pairs, dp_s = _timed(lambda: _select_cow_pairs_capacity_dp(partition.side_01, partition.side_10, context=context))
    brute_pairs, brute_s = _timed(lambda: _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context))
    selected_pairs = _select_cow_pairs(partition.side_01, partition.side_10, context=context)
    greedy_key = _cow_pair_selection_key(greedy_pairs)
    dp_key = _cow_pair_selection_key(dp_pairs)
    brute_key = _cow_pair_selection_key(brute_pairs)
    selected_key = _cow_pair_selection_key(selected_pairs)
    return {
        "case_id": case.case_id,
        "note": case.note,
        "total_candidates": len(partition.side_01) + len(partition.side_10),
        "side_01": len(partition.side_01),
        "side_10": len(partition.side_10),
        "assignment_balance_safe": _assignment_balance_safe(partition.side_01, partition.side_10, context=context),
        "dp_matches_bruteforce": dp_key == brute_key,
        "core_selector_matches_dp": selected_key == dp_key,
        "dp_beats_greedy": _is_better_cow_pair_key(dp_key, greedy_key),
        "volume_lift": int(dp_key[0]) - int(greedy_key[0]),
        "surplus_lift": int(dp_key[1]) - int(greedy_key[1]),
        "greedy_key": greedy_key,
        "dp_key": dp_key,
        "bruteforce_key": brute_key,
        "selected_key": selected_key,
        "greedy_pair_ids": _pair_ids(greedy_pairs),
        "dp_pair_ids": _pair_ids(dp_pairs),
        "bruteforce_pair_ids": _pair_ids(brute_pairs),
        "timing_s": {
            "greedy": greedy_s,
            "capacity_dp": dp_s,
            "bruteforce": brute_s,
        },
    }


def build_report() -> dict[str, Any]:
    rows = [_case_result(case) for case in cases()]
    exact_mismatches = [row for row in rows if not row["dp_matches_bruteforce"]]
    core_mismatches = [row for row in rows if not row["core_selector_matches_dp"]]
    lift_rows = [row for row in rows if row["dp_beats_greedy"]]
    return {
        "schema": "zenodex.cow_capacity_dp_breakthrough_report.v1",
        "date": "2026-06-27",
        "ok": not exact_mismatches and not core_mismatches and len(lift_rows) >= 2,
        "breakthrough": {
            "name": "Capacity-coupled CoW bounded exact DP",
            "summary": "The CoW selector now replaces the greedy grouped-capacity fallback with exact DP for small coupled batches, preserving brute-force volume/surplus/tie semantics under repeated senders.",
            "authority_boundary": "The selector proposes CoW netting pairs; settlement materialization still performs fail-closed aggregate balance checks before mutating balances.",
        },
        "case_count": len(rows),
        "exact_mismatch_count": len(exact_mismatches),
        "core_mismatch_count": len(core_mismatches),
        "greedy_lift_case_count": len(lift_rows),
        "max_total_candidates": max(row["total_candidates"] for row in rows),
        "cases": rows,
        "non_claims": [
            "This is a bounded exact DP for small grouped-capacity CoW batches, not a polynomial algorithm for arbitrary grouped-capacity matching.",
            "Uncoupled large batches still use Hungarian assignment; large coupled batches still retain the greedy/fail-closed fallback.",
            "The report measures selector quality against brute force on a deterministic bounded corpus, not production activation.",
        ],
        "replay_command": "python3 tools/zenodex_cow_capacity_dp_breakthrough_20260627.py",
    }


def write_markdown(report: dict[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX CoW Capacity-DP Breakthrough - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(report["breakthrough"]["summary"])
    lines.append("")
    lines.append(report["breakthrough"]["authority_boundary"])
    lines.append("")
    lines.append(
        f"Cases: `{report['case_count']}`. Exact mismatches: `{report['exact_mismatch_count']}`. Core selector mismatches: `{report['core_mismatch_count']}`. Greedy-lift cases: `{report['greedy_lift_case_count']}`. Max candidates: `{report['max_total_candidates']}`."
    )
    lines.append("")
    lines.append("## Cases")
    lines.append("")
    lines.append("| case | candidates | DP=brute | core=DP | beats greedy | volume lift | surplus lift |")
    lines.append("| --- | ---: | --- | --- | --- | ---: | ---: |")
    for row in report["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['total_candidates']}` | `{row['dp_matches_bruteforce']}` | `{row['core_selector_matches_dp']}` | `{row['dp_beats_greedy']}` | `{row['volume_lift']}` | `{row['surplus_lift']}` |"
        )
    lines.append("")
    lines.append("## Algorithm")
    lines.append("")
    lines.append("State:")
    lines.append("")
    lines.append("```text")
    lines.append("(side_01_prefix_index, used_side_10_mask, debits_by_asset0_sender, debits_by_asset1_sender)")
    lines.append("```")
    lines.append("")
    lines.append("The DP explores skip-or-pair decisions for each `asset0 -> asset1` candidate. A pair is admitted only when the reciprocal minimum-output inequalities hold and both sender debit vectors remain within the pre-netting balance snapshot. The selected suffix is compared with the same `(volume, surplus, pair-id tie)` key used by the brute-force oracle.")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    lines.append("")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON, output_md: Path = REPORT_MD) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    parser.add_argument("--output-md", default=str(REPORT_MD))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "case_count": report["case_count"],
                "exact_mismatch_count": report["exact_mismatch_count"],
                "greedy_lift_case_count": report["greedy_lift_case_count"],
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
