#!/usr/bin/env python3
"""Stress-refute strict executable zero-min AB economic compression.

The supported certificate is narrow: same-pool, same-direction, exact-in,
min_amount_out=0, and a compressed full-mask order must exist. This tool
searches that strict surface for an economic-key mismatch between the
one-record min-reserve-out compression and the full-state subset DP. It also
records simple amount-sorted greedy failures as negative design evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import time
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
from tools.check_ab_zero_min_economic_compression_certificate import (  # noqa: E402
    ASSET0,
    ASSET1,
    POOL_ID,
    _compressed_min_reserve_out_order,
    _context,
    _economic_key,
    _intent,
    _sender,
    _short,
)

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_strict_zero_min_economic_refuter_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_STRICT_ZERO_MIN_ECONOMIC_REFUTER_20260628.md"

SEED = 2026062802
CASE_COUNT = 600
BRUTE_CASE_CAP = 80
AMOUNT_CHOICES = (1, 2, 3, 5, 8, 13, 21, 34, 55, 89)


def _random_case(case_no: int, rng: random.Random) -> tuple[PoolState, list[Any], BalanceTable]:
    pool = PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=rng.randint(50, 2_500),
        reserve1=rng.randint(50, 4_000),
        fee_bps=rng.choice([0, 1, 2, 5, 30, 75, 100, 250]),
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )
    intents = []
    balances = BalanceTable()
    for idx in range(rng.randint(2, 8)):
        random_amount = rng.randint(1, 150)
        amount_in = rng.choice([*AMOUNT_CHOICES, random_amount])
        sender_no = idx + 1
        balances.set(_sender(sender_no), ASSET0, amount_in + 100_000)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _intent(
                300_000 + case_no * 20 + idx,
                sender_no=sender_no,
                amount_in=amount_in,
                min_amount_out=0,
            )
        )
    return pool, intents, balances


def _amounts(intents: list[Any]) -> list[int]:
    return [int(intent.get_field("amount_in")) for intent in intents]


def _case_summary(pool: PoolState, intents: list[Any]) -> dict[str, Any]:
    return {
        "pool": {
            "reserve0": int(pool.reserve0),
            "reserve1": int(pool.reserve1),
            "fee_bps": int(pool.fee_bps),
        },
        "n": len(intents),
        "amounts": _amounts(intents),
    }


def _check_case(case_no: int, rng: random.Random, *, do_brute: bool) -> dict[str, Any]:
    pool, intents, balances = _random_case(case_no, rng)
    context = _context(pool, intents, balances)
    compressed = _compressed_min_reserve_out_order(intents, context)
    strict_scope = compressed is not None and len(compressed) == len(intents)
    row: dict[str, Any] = {
        "case_no": case_no,
        **_case_summary(pool, intents),
        "strict_scope": bool(strict_scope),
    }
    if not strict_scope:
        row["skip_reason"] = "compressed_full_mask_not_executable"
        return row

    full = _best_order_by_objective_subset_dp(intents, context)
    compressed_key = _economic_key(compressed, context)
    full_key = _economic_key(full, context) if full is not None else (-1, -1)
    brute_key: tuple[int, int] | None = None
    brute_order = None
    if do_brute and len(intents) <= 7:
        brute_order = _best_order_by_objective_bruteforce(intents, context)
        brute_key = _economic_key(brute_order, context) if brute_order is not None else (-1, -1)

    ascending = tuple(sorted(intents, key=lambda intent: (int(intent.get_field("amount_in")), intent.intent_id)))
    descending = tuple(sorted(intents, key=lambda intent: (-int(intent.get_field("amount_in")), intent.intent_id)))
    ascending_key = _economic_key(ascending, context)
    descending_key = _economic_key(descending, context)

    row.update(
        {
            "compressed_economic_key": compressed_key,
            "full_economic_key": full_key,
            "brute_economic_key": brute_key,
            "economic_parity_ok": compressed_key == full_key and (brute_key is None or compressed_key == brute_key),
            "brute_checked": brute_key is not None,
            "compressed_order": _short(tuple(intent.intent_id for intent in compressed)),
            "full_order": _short(tuple(intent.intent_id for intent in full or ())),
            "brute_order": _short(tuple(intent.intent_id for intent in brute_order or ())) if brute_order else None,
            "ascending_amount_key": ascending_key,
            "descending_amount_key": descending_key,
            "ascending_amount_greedy_ok": ascending_key == full_key,
            "descending_amount_greedy_ok": descending_key == full_key,
            "ascending_amount_order": _short(tuple(intent.intent_id for intent in ascending)),
            "descending_amount_order": _short(tuple(intent.intent_id for intent in descending)),
        }
    )
    return row


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    rng = random.Random(SEED)
    rows: list[dict[str, Any]] = []
    brute_checked = 0
    for case_no in range(CASE_COUNT):
        do_brute = brute_checked < BRUTE_CASE_CAP
        row = _check_case(case_no, rng, do_brute=do_brute)
        if row.get("brute_checked"):
            brute_checked += 1
        rows.append(row)

    strict_rows = [row for row in rows if row["strict_scope"]]
    mismatches = [row for row in strict_rows if not row["economic_parity_ok"]]
    brute_mismatches = [
        row
        for row in strict_rows
        if row.get("brute_checked") and row["compressed_economic_key"] != row["brute_economic_key"]
    ]
    ascending_failures = [row for row in strict_rows if not row["ascending_amount_greedy_ok"]]
    descending_failures = [row for row in strict_rows if not row["descending_amount_greedy_ok"]]
    return {
        "schema": "zenodex/ab_strict_zero_min_economic_refuter/v1",
        "seed": SEED,
        "case_count": CASE_COUNT,
        "strict_scope_count": len(strict_rows),
        "skipped_non_strict_count": CASE_COUNT - len(strict_rows),
        "brute_checked_count": brute_checked,
        "mismatch_count": len(mismatches),
        "brute_mismatch_count": len(brute_mismatches),
        "ascending_amount_greedy_failure_count": len(ascending_failures),
        "descending_amount_greedy_failure_count": len(descending_failures),
        "first_mismatch": mismatches[0] if mismatches else None,
        "first_brute_mismatch": brute_mismatches[0] if brute_mismatches else None,
        "first_ascending_amount_greedy_failure": ascending_failures[0] if ascending_failures else None,
        "first_descending_amount_greedy_failure": descending_failures[0] if descending_failures else None,
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _strip_timing(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _strip_timing(item) for key, item in value.items() if key != "elapsed_ms"}
    if isinstance(value, list):
        return [_strip_timing(item) for item in value]
    return value


def deterministic_replay(first: Mapping[str, Any]) -> dict[str, Any]:
    second = run_search()
    first_hash = _sha256_json(_strip_timing(first))
    second_hash = _sha256_json(_strip_timing(second))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["strict_scope_count"] >= 300
        and search["mismatch_count"] == 0
        and search["brute_mismatch_count"] == 0
        and search["ascending_amount_greedy_failure_count"] > 0
        and search["descending_amount_greedy_failure_count"] > 0
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_economic_refuter_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "summary": "A deterministic stress refuter found no economic-key mismatch inside the strict executable zero-min AB compression surface, while refuting simple amount-sorted greedy replacements.",
        "authority_boundary": "This is research evidence only. It does not select production AB orders or authorize settlement.",
        "search": search,
        "deterministic_replay": deterministic,
        "non_claims": [
            "This is not a proof of the strict executable zero-min compression theorem.",
            "Canonical tie order remains outside the economic-key claim.",
            "Zero-min cases without a compressed executable full-mask order are outside this strict surface.",
            "Nonzero min_amount_out batches remain outside this compression surface.",
            "Amount-sorted greedy orders are refuted as replacements for the one-record DP.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_strict_zero_min_economic_refuter.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Economic Refuter - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Search Summary",
        "",
        f"- Seed: `{search['seed']}`",
        f"- Random cases: `{search['case_count']}`",
        f"- Strict executable zero-min cases: `{search['strict_scope_count']}`",
        f"- Non-strict skipped cases: `{search['skipped_non_strict_count']}`",
        f"- Brute-force cross-checks: `{search['brute_checked_count']}`",
        f"- Economic-key mismatches: `{search['mismatch_count']}`",
        f"- Brute-force mismatches: `{search['brute_mismatch_count']}`",
        f"- Ascending amount-greedy failures: `{search['ascending_amount_greedy_failure_count']}`",
        f"- Descending amount-greedy failures: `{search['descending_amount_greedy_failure_count']}`",
        "",
        "The strict surface requires a compressed executable full-mask order. Cases outside that surface are skipped rather than treated as support.",
        "",
        "## First Ascending Greedy Failure",
        "",
        "```json",
        json.dumps(search["first_ascending_amount_greedy_failure"], indent=2, sort_keys=True),
        "```",
        "",
        "## First Descending Greedy Failure",
        "",
        "```json",
        json.dumps(search["first_descending_amount_greedy_failure"], indent=2, sort_keys=True),
        "```",
        "",
        "## Non-Claims",
        "",
    ]
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json))
    search = report["search"]
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "case_count": search["case_count"],
                "strict_scope_count": search["strict_scope_count"],
                "mismatch_count": search["mismatch_count"],
                "brute_checked_count": search["brute_checked_count"],
                "ascending_amount_greedy_failure_count": search["ascending_amount_greedy_failure_count"],
                "descending_amount_greedy_failure_count": search["descending_amount_greedy_failure_count"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
