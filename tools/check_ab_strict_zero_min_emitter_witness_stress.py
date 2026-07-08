#!/usr/bin/env python3
"""Stress-refute host packets for the AB strict zero-min Lean witness.

This research-only checker broadens the deterministic packet search around
`check_ab_strict_zero_min_emitter_witness.py`. It generates strict executable
zero-min same-pool exact-in batches, emits the same host witness packet shape,
and mutates every packet to keep the witness verifier fail-closed.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import (  # noqa: E402
    _best_order_by_objective_bruteforce,
    _best_order_by_objective_subset_dp,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _HostMaskSet,
    _HostRecord,
    _child_frontier,
    _compressed_records,
    _full_state_records,
    _mask_set_json,
    _mutated_packets,
    _record_json,
    _sha256_json,
    _strip_timing,
    _with_packet_hash,
    verify_witness_packet,
)
from tools.check_ab_zero_min_economic_compression_certificate import (  # noqa: E402
    ASSET0,
    ASSET1,
    POOL_ID,
    _context,
    _economic_key,
    _intent,
    _sender,
)

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_strict_zero_min_emitter_witness_stress_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_STRICT_ZERO_MIN_EMITTER_WITNESS_STRESS_20260629.md"

SEED = 2_026_062_901
CASE_COUNT = 180
MAX_N = 6
MIN_STRICT_PACKET_COUNT = 160
FEE_BPS_VALUES = (0, 1, 2, 5, 30, 75, 100)


@dataclass(frozen=True)
class _StressCase:
    case_id: str
    pool: PoolState
    intents: list[Any]
    balances: BalanceTable
    pattern: str


def _pool(case_no: int, *, reserve_in: int, reserve_out: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve_in),
        reserve1=int(reserve_out),
        fee_bps=int(fee_bps),
        lp_supply=10_000 + case_no,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _amount_pattern(case_no: int, n: int, rng: random.Random) -> tuple[str, list[int]]:
    pattern_id = case_no % 9
    if pattern_id == 0:
        return "flat", [8 + (case_no % 5)] * n
    if pattern_id == 1:
        return "ascending", [7 + idx * 5 + (case_no % 3) for idx in range(n)]
    if pattern_id == 2:
        return "descending", [7 + (n - idx) * 5 + (case_no % 3) for idx in range(n)]
    if pattern_id == 3:
        fib = (8, 13, 21, 34, 55, 89)
        return "fibonacci", [fib[idx] for idx in range(n)]
    if pattern_id == 4:
        return "alternating", [12 if idx % 2 == 0 else 73 + (case_no % 11) for idx in range(n)]
    if pattern_id == 5:
        return "one_large_prefix", [160 + (case_no % 37), *([9 + (case_no % 7)] * (n - 1))]
    if pattern_id == 6:
        return "one_large_suffix", [9 + (case_no % 7)] * (n - 1) + [160 + (case_no % 37)]
    if pattern_id == 7:
        return "near_tie_pairs", [24 + ((idx // 2) % 3) for idx in range(n)]
    return "seeded_random", [rng.randint(8, 190) for _ in range(n)]


def _sender_no(case_no: int, idx: int) -> int:
    return ((case_no * 11 + idx) % 240) + 1


def _random_case(case_no: int, rng: random.Random) -> _StressCase:
    n = 2 + (case_no % (MAX_N - 1))
    pattern, amounts = _amount_pattern(case_no, n, rng)
    fee_bps = FEE_BPS_VALUES[case_no % len(FEE_BPS_VALUES)]
    total_amount = sum(amounts)
    reserve_in = 450 + rng.randint(0, 3_500) + (case_no % 17) * 19
    reserve_out = 20_000 + rng.randint(0, 180_000) + total_amount * 50
    pool = _pool(case_no, reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps)
    balances = BalanceTable()
    intents = []
    for idx, amount_in in enumerate(amounts):
        sender_no = _sender_no(case_no, idx)
        balances.set(_sender(sender_no), ASSET0, int(amount_in) + 10_000)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _intent(
                300_000 + case_no * 16 + idx,
                sender_no=sender_no,
                amount_in=int(amount_in),
                min_amount_out=0,
            )
        )
    return _StressCase(
        case_id=f"stress_{case_no:03d}_{pattern}_n{n}_fee{fee_bps}",
        pool=pool,
        intents=intents,
        balances=balances,
        pattern=pattern,
    )


def _order_from_record(intents: list[Any], record: _HostRecord) -> tuple[Any, ...]:
    by_id = {intent.intent_id: intent for intent in intents}
    return tuple(by_id[intent_id] for intent_id in record.order_ids)


def _build_packet_from_case(case: _StressCase) -> tuple[dict[str, Any] | None, str | None]:
    context = _context(case.pool, case.intents, case.balances)
    n = len(case.intents)
    full_mask = (1 << n) - 1
    full_dp = _full_state_records(case.intents, context)
    compressed_dp = _compressed_records(case.intents, context)
    final_compressed = compressed_dp[full_mask]
    if final_compressed is None:
        return None, "compressed_full_mask_not_executable"
    final_full_records = full_dp[full_mask]
    if not final_full_records:
        return None, "full_frontier_empty"

    children = _child_frontier(final_full_records, full_mask)
    winner = _HostMaskSet(mask_id=full_mask, selected=final_compressed, all_records=(final_compressed,))
    parent_record = _HostRecord(int(context.r_in0), int(context.r_out0), ())
    parent = _HostMaskSet(mask_id=0, selected=parent_record, all_records=(parent_record,))
    full = _best_order_by_objective_subset_dp(case.intents, context)
    brute = _best_order_by_objective_bruteforce(case.intents, context)
    compressed_order = _order_from_record(case.intents, final_compressed)
    packet = {
        "schema": "zenodex.ab_strict_zero_min_emitter_witness_packet.v1",
        "case_id": case.case_id,
        "scope": "stress_same_pool_same_direction_exact_in_zero_min_strict_executable",
        "authority_boundary": "research_only_no_settlement_or_state_authority",
        "no_authority_effect": True,
        "bit_count": int(n),
        "full_mask": int(full_mask),
        "initial_reserve_in": int(context.r_in0),
        "initial_reserve_out": int(context.r_out0),
        "executed_input": int(sum(int(intent.get_field("amount_in")) for intent in case.intents)),
        "pool": {
            "reserve_in": int(context.r_in0),
            "reserve_out": int(context.r_out0),
            "fee_bps": int(context.pool_state.fee_bps),
        },
        "amounts": [int(intent.get_field("amount_in")) for intent in case.intents],
        "min_amount_out": [int(intent.get_field("min_amount_out", 0)) for intent in case.intents],
        "stress": {
            "seed": SEED,
            "pattern": case.pattern,
            "case_count": CASE_COUNT,
        },
        "parent": _mask_set_json(parent, include_all_records=True),
        "winner": _mask_set_json(winner, include_all_records=True),
        "children": [_mask_set_json(child, include_all_records=True) for child in children],
        "masks": [_mask_set_json(winner, include_all_records=True)],
        "compressed_table": [
            {"mask_id": mask_id, "selected": _record_json(record)}
            for mask_id, record in enumerate(compressed_dp)
            if record is not None
        ],
        "lean_contract": {
            "structure": "StrictCompressedFullMaskEconomicWitness",
            "valid_predicate": "strictCompressedFullMaskEconomicWitnessValid",
            "endpoint": "strictCompressedFullMaskEconomicWitness_validates",
        },
        "economic_keys": {
            "compressed": list(_economic_key(compressed_order, context)),
            "full_subset_dp": list(_economic_key(full, context)) if full is not None else [-1, -1],
            "brute_force": list(_economic_key(brute, context)) if brute is not None else None,
        },
    }
    return _with_packet_hash(packet), None


def _iter_cases() -> list[_StressCase]:
    rng = random.Random(SEED)
    return [_random_case(case_no, rng) for case_no in range(CASE_COUNT)]


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    rows: list[dict[str, Any]] = []
    mutation_rows: list[dict[str, Any]] = []
    skipped: list[dict[str, str]] = []
    first_packet: dict[str, Any] | None = None
    pattern_counts: dict[str, int] = {}
    fee_counts: dict[str, int] = {}
    n_counts: dict[str, int] = {}

    for case in _iter_cases():
        pattern_counts[case.pattern] = pattern_counts.get(case.pattern, 0) + 1
        fee_counts[str(case.pool.fee_bps)] = fee_counts.get(str(case.pool.fee_bps), 0) + 1
        n_counts[str(len(case.intents))] = n_counts.get(str(len(case.intents)), 0) + 1
        packet, skip_reason = _build_packet_from_case(case)
        if packet is None:
            skipped.append({"case_id": case.case_id, "reason": str(skip_reason)})
            continue
        if first_packet is None:
            first_packet = packet
        verification = verify_witness_packet(packet)
        rows.append(
            {
                "case_id": packet["case_id"],
                "ok": verification["ok"],
                "reasons": verification["reasons"],
                "packet_hash": packet["packet_hash"],
                "bit_count": packet["bit_count"],
                "fee_bps": packet["pool"]["fee_bps"],
                "pattern": packet["stress"]["pattern"],
                "children_count": len(packet["children"]),
                "compressed_table_count": len(packet["compressed_table"]),
                "winner_order": packet["winner"]["selected"]["order_short"],
                "amount_digest": _sha256_json(packet["amounts"]),
                "economic_keys": packet["economic_keys"],
                "checks": verification["checks"],
            }
        )
        for mutation_id, mutated in _mutated_packets(packet):
            mutated_verification = verify_witness_packet(mutated)
            mutation_rows.append(
                {
                    "case_id": packet["case_id"],
                    "mutation_id": mutation_id,
                    "accepted": bool(mutated_verification["ok"]),
                    "reasons": mutated_verification["reasons"],
                }
            )

    return {
        "schema": "zenodex/ab_strict_zero_min_emitter_witness_stress_search/v1",
        "seed": SEED,
        "case_count": CASE_COUNT,
        "strict_packet_count": len(rows),
        "valid_packet_count": sum(1 for row in rows if row["ok"]),
        "skipped_count": len(skipped),
        "skipped": skipped[:20],
        "first_invalid_packet": next((row for row in rows if not row["ok"]), None),
        "mutation_count": len(mutation_rows),
        "mutation_accept_count": sum(1 for row in mutation_rows if row["accepted"]),
        "first_mutation_accept": next((row for row in mutation_rows if row["accepted"]), None),
        "coverage": {
            "n_counts": dict(sorted(n_counts.items())),
            "fee_bps_counts": dict(sorted(fee_counts.items(), key=lambda item: int(item[0]))),
            "pattern_counts": dict(sorted(pattern_counts.items())),
            "max_bit_count": max((int(row["bit_count"]) for row in rows), default=0),
            "max_children_count": max((int(row["children_count"]) for row in rows), default=0),
        },
        "cases": rows,
        "mutations": mutation_rows,
        "first_packet": first_packet,
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def deterministic_replay(first: Mapping[str, Any]) -> dict[str, Any]:
    second = run_search()
    first_hash = _sha256_json(_strip_timing(first))
    second_hash = _sha256_json(_strip_timing(second))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["case_count"] == CASE_COUNT
        and search["strict_packet_count"] >= MIN_STRICT_PACKET_COUNT
        and search["valid_packet_count"] == search["strict_packet_count"]
        and search["mutation_count"] == search["strict_packet_count"] * 7
        and search["mutation_accept_count"] == 0
        and search["first_invalid_packet"] is None
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_emitter_witness_stress_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A deterministic stress refuter broadens the strict zero-min host witness packet search "
            "and rejects all generated packet mutations under the existing verifier."
        ),
        "authority_boundary": "Research-only stress evidence; no settlement, state-root, production, or governance authority.",
        "search": search,
        "deterministic_replay": deterministic,
        "non_claims": [
            "This stress run is not a proof of full compressed-DP induction.",
            "This stress run does not prove Lean-to-Python refinement.",
            "This stress run does not define canonical tie order.",
            "Nonzero min_amount_out batches are outside this artifact.",
            "Host bitset equivalence remains a separate proof obligation.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_strict_zero_min_emitter_witness_stress.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Emitter Witness Stress - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Evidence Summary",
        "",
        f"- Deterministic seed: `{search['seed']}`",
        f"- Generated cases: `{search['case_count']}`",
        f"- Strict executable witness packets: `{search['strict_packet_count']}`",
        f"- Valid witness packets: `{search['valid_packet_count']}`",
        f"- Skipped cases: `{search['skipped_count']}`",
        f"- Packet mutations checked: `{search['mutation_count']}`",
        f"- Mutation accepts: `{search['mutation_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Pattern histogram: `{coverage['pattern_counts']}`",
        f"- Max bit count: `{coverage['max_bit_count']}`",
        f"- Max child frontier count: `{coverage['max_children_count']}`",
        "",
        "## Contract Under Stress",
        "",
        "```text",
        "host packet parent/winner/children/bitCount/masks/initialReserveOut/executedInput",
        "  -> StrictCompressedFullMaskEconomicWitness",
        "existing verifier",
        "  -> packet hash, authority rail, full-mask coverage, child membership, economic-key parity",
        "stress mutations",
        "  -> each malformed packet must fail closed",
        "```",
        "",
        "## First Packet",
        "",
        "```json",
        json.dumps(search["first_packet"], indent=2, sort_keys=True),
        "```",
        "",
        "## Case Summary",
        "",
        "| case | ok | n | fee | children | key |",
        "| --- | --- | ---: | ---: | ---: | --- |",
    ]
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['bit_count']}` | "
            f"`{row['fee_bps']}` | `{row['children_count']}` | `{row['economic_keys']['compressed']}` |"
        )
    lines.extend(["", "## Mutation Summary", "", "| mutation | accepted count |", "| --- | ---: |"])
    mutation_ids = sorted({row["mutation_id"] for row in search["mutations"]})
    for mutation_id in mutation_ids:
        accepted_count = sum(
            1 for row in search["mutations"] if row["mutation_id"] == mutation_id and row["accepted"]
        )
        lines.append(f"| `{mutation_id}` | `{accepted_count}` |")
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-only", action="store_true", help="Write JSON without refreshing markdown")
    args = parser.parse_args()
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if not args.json_only:
        _write_markdown(report)
    print(json.dumps({"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
