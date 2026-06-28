#!/usr/bin/env python3
"""Exhaustively refute a small AB strict zero-min compression surface.

This research tool searches a declared small integer grid for economic-key
mismatches between one-record min-reserve-out compression, the full-state subset
DP, and brute force. It also records overbroad zero-min witnesses where the
compressed order cannot execute every intent although brute force can.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping

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

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_strict_zero_min_exhaustive_small_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_STRICT_ZERO_MIN_EXHAUSTIVE_SMALL_20260628.md"

RESERVE_IN_VALUES = (3, 5, 8, 13, 21)
RESERVE_OUT_VALUES = (3, 5, 8, 13, 21, 34)
FEE_BPS_VALUES = (0, 1, 30)
AMOUNT_VALUES_BY_N: Mapping[int, tuple[int, ...]] = {
    2: (1, 2, 3, 5, 8),
    3: (1, 2, 3, 5),
    4: (1, 2, 3),
}


def _pool(reserve_in: int, reserve_out: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve_in),
        reserve1=int(reserve_out),
        fee_bps=int(fee_bps),
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _intents_for_amounts(case_no: int, amounts: tuple[int, ...]) -> tuple[list[Any], BalanceTable]:
    balances = BalanceTable()
    intents = []
    for idx, amount_in in enumerate(amounts):
        sender_no = idx + 1
        balances.set(_sender(sender_no), ASSET0, int(amount_in) + 10_000)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _intent(
                500_000 + int(case_no) * 10 + idx,
                sender_no=sender_no,
                amount_in=int(amount_in),
                min_amount_out=0,
            )
        )
    return intents, balances


def _orders_short(order: tuple[Any, ...] | None) -> list[str]:
    return _short(tuple(intent.intent_id for intent in order or ()))


def _case_row(
    *,
    case_no: int,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amounts: tuple[int, ...],
) -> dict[str, Any]:
    pool = _pool(reserve_in, reserve_out, fee_bps)
    intents, balances = _intents_for_amounts(case_no, amounts)
    context = _context(pool, intents, balances)

    compressed = _compressed_min_reserve_out_order(intents, context)
    full = _best_order_by_objective_subset_dp(intents, context)
    brute = _best_order_by_objective_bruteforce(intents, context)

    total_input = sum(int(amount) for amount in amounts)
    compressed_key = _economic_key(compressed, context) if compressed is not None else (-1, -1)
    full_key = _economic_key(full, context) if full is not None else (-1, -1)
    brute_key = _economic_key(brute, context) if brute is not None else (-1, -1)
    strict_scope = compressed is not None and int(compressed_key[0]) == int(total_input)

    return {
        "case_no": int(case_no),
        "reserve_in": int(reserve_in),
        "reserve_out": int(reserve_out),
        "fee_bps": int(fee_bps),
        "n": len(amounts),
        "amounts": list(amounts),
        "total_input": int(total_input),
        "strict_scope": bool(strict_scope),
        "strict_economic_parity_ok": bool(
            strict_scope and compressed_key == full_key and compressed_key == brute_key
        ),
        "overbroad_zero_min_boundary": bool(not strict_scope and int(brute_key[0]) == int(total_input)),
        "compressed_key": compressed_key,
        "full_key": full_key,
        "brute_key": brute_key,
        "compressed_order": _orders_short(compressed),
        "full_order": _orders_short(full),
        "brute_order": _orders_short(brute),
    }


def _iter_cases() -> Iterable[tuple[int, int, int, tuple[int, ...]]]:
    for reserve_in in RESERVE_IN_VALUES:
        for reserve_out in RESERVE_OUT_VALUES:
            for fee_bps in FEE_BPS_VALUES:
                for n, amount_values in AMOUNT_VALUES_BY_N.items():
                    for amounts in itertools.product(amount_values, repeat=n):
                        yield int(reserve_in), int(reserve_out), int(fee_bps), tuple(int(v) for v in amounts)


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    rows = [
        _case_row(
            case_no=case_no,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            amounts=amounts,
        )
        for case_no, (reserve_in, reserve_out, fee_bps, amounts) in enumerate(_iter_cases())
    ]
    strict_rows = [row for row in rows if row["strict_scope"]]
    strict_mismatches = [row for row in strict_rows if not row["strict_economic_parity_ok"]]
    overbroad_boundaries = [row for row in rows if row["overbroad_zero_min_boundary"]]
    return {
        "schema": "zenodex/ab_strict_zero_min_exhaustive_small/v1",
        "grid": {
            "reserve_in_values": list(RESERVE_IN_VALUES),
            "reserve_out_values": list(RESERVE_OUT_VALUES),
            "fee_bps_values": list(FEE_BPS_VALUES),
            "amount_values_by_n": {str(key): list(value) for key, value in AMOUNT_VALUES_BY_N.items()},
        },
        "case_count": len(rows),
        "strict_scope_count": len(strict_rows),
        "strict_mismatch_count": len(strict_mismatches),
        "overbroad_zero_min_boundary_count": len(overbroad_boundaries),
        "first_strict_mismatch": strict_mismatches[0] if strict_mismatches else None,
        "first_overbroad_zero_min_boundary": overbroad_boundaries[0] if overbroad_boundaries else None,
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
        search["case_count"] == 15_300
        and search["strict_scope_count"] > 0
        and search["strict_mismatch_count"] == 0
        and search["overbroad_zero_min_boundary_count"] > 0
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_exhaustive_small_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "summary": (
            "A deterministic exhaustive small-grid refuter found no strict-scope economic-key "
            "mismatch for one-record min-reserve-out compression, while preserving explicit "
            "overbroad zero-min boundary witnesses."
        ),
        "authority_boundary": "Research evidence only. This artifact does not select production AB orders or authorize settlement.",
        "search": search,
        "deterministic_replay": deterministic,
        "non_claims": [
            "This is not a proof of the full strict executable zero-min compression theorem.",
            "The grid is finite and intentionally small.",
            "Canonical tie order remains outside the economic-key claim.",
            "Zero-min cases where compressed full-mask execution fails remain outside the strict supported surface.",
            "Nonzero min_amount_out batches remain outside this compression surface.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_strict_zero_min_exhaustive_small.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Exhaustive Small Refuter - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Grid",
        "",
        "```json",
        json.dumps(search["grid"], indent=2, sort_keys=True),
        "```",
        "",
        "## Search Summary",
        "",
        f"- Cases: `{search['case_count']}`",
        f"- Strict-scope cases: `{search['strict_scope_count']}`",
        f"- Strict-scope economic mismatches: `{search['strict_mismatch_count']}`",
        f"- Overbroad zero-min boundary witnesses: `{search['overbroad_zero_min_boundary_count']}`",
        "",
        "The strict surface requires the compressed full-mask order to execute all intents. Boundary witnesses are kept as non-claim evidence against the broader zero-min surface.",
        "",
        "## First Overbroad Zero-Min Boundary",
        "",
        "```json",
        json.dumps(search["first_overbroad_zero_min_boundary"], indent=2, sort_keys=True),
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
                "strict_mismatch_count": search["strict_mismatch_count"],
                "overbroad_zero_min_boundary_count": search["overbroad_zero_min_boundary_count"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
            },
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
