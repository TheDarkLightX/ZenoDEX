#!/usr/bin/env python3
"""Check observed child-frontier packets for the AB strict zero-min n=7 corpus.

This research-only checker extends the observed-frontier host witness replay to
the committed n=7 randomized corpus. It builds full child-frontier packets for
each case, validates the host obligations mirrored by Lean's observed frontier
endpoint, and records stable packet digests instead of storing the large packet
bodies in the report.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_strict_zero_min_arbitrary_subset_family_n7_randomized import (  # noqa: E402
    SEED as N7_SEED,
    _boundary_positive_case,
    _random_candidate,
)
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _mutated_packets,
    _sha256_json,
    _strip_timing,
    _with_packet_hash,
)
from tools.check_ab_strict_zero_min_emitter_witness_stress import _build_packet_from_case  # noqa: E402
from tools.check_ab_strict_zero_min_observed_frontier_witness import (  # noqa: E402
    EXPECTED_OBSERVED_MUTATION_COUNT,
    _observed_mutated_packets,
    verify_observed_frontier_packet,
)

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_observed_frontier_n7_randomized_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_OBSERVED_FRONTIER_N7_RANDOMIZED_20260629.md"
)

REPORT_SCHEMA = "zenodex.ab_strict_zero_min_observed_frontier_n7_randomized_report.v1"
SEARCH_SCHEMA = "zenodex/ab_strict_zero_min_observed_frontier_n7_randomized_search/v1"
SCOPE = "n7_randomized_same_pool_same_direction_exact_in_zero_min_strict_executable_observed_frontier"
TARGET_CASE_COUNT = 4
EXPECTED_CHILDREN_PER_CASE = 5_040


def _n7_cases() -> list[Any]:
    import random

    rng = random.Random(N7_SEED)
    return [
        _boundary_positive_case(),
        _random_candidate(0, rng),
        _random_candidate(1, rng),
        _random_candidate(2, rng),
    ]


def _canonical_json_size(value: Any) -> int:
    return len(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8"))


def _n7_packet_from_case(case: Any) -> tuple[dict[str, Any] | None, str | None]:
    packet, skip_reason = _build_packet_from_case(case)
    if packet is None:
        return None, skip_reason
    packet = dict(packet)
    packet["scope"] = SCOPE
    packet["stress"] = {
        "seed": N7_SEED,
        "pattern": case.pattern,
        "case_count": TARGET_CASE_COUNT,
    }
    return _with_packet_hash(packet), None


def _packet_summary(packet: Mapping[str, Any], verification: Mapping[str, Any]) -> dict[str, Any]:
    children = packet["children"]
    return {
        "case_id": packet["case_id"],
        "ok": verification["ok"],
        "reasons": verification["reasons"],
        "packet_hash": packet["packet_hash"],
        "packet_digest": _sha256_json(packet),
        "packet_canonical_bytes": _canonical_json_size(packet),
        "bit_count": packet["bit_count"],
        "fee_bps": packet["pool"]["fee_bps"],
        "pattern": packet["stress"]["pattern"],
        "children_count": len(children),
        "compressed_table_count": len(packet["compressed_table"]),
        "winner_order": packet["winner"]["selected"]["order_short"],
        "winner_selected": {
            "processed_reserve_in": packet["winner"]["selected"]["processed_reserve_in"],
            "reserve_out": packet["winner"]["selected"]["reserve_out"],
        },
        "economic_keys": packet["economic_keys"],
        "checks": verification["checks"],
    }


def _first_packet_brief(packet: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "case_id": packet["case_id"],
        "scope": packet["scope"],
        "authority_boundary": packet["authority_boundary"],
        "packet_hash": packet["packet_hash"],
        "packet_digest": _sha256_json(packet),
        "packet_canonical_bytes": _canonical_json_size(packet),
        "bit_count": packet["bit_count"],
        "full_mask": packet["full_mask"],
        "pool": packet["pool"],
        "amounts": packet["amounts"],
        "min_amount_out": packet["min_amount_out"],
        "children_count": len(packet["children"]),
        "first_child_digest": _sha256_json(packet["children"][0]) if packet["children"] else None,
        "last_child_digest": _sha256_json(packet["children"][-1]) if packet["children"] else None,
        "winner": packet["winner"]["selected"],
        "economic_keys": packet["economic_keys"],
        "stress": packet["stress"],
    }


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    rows: list[dict[str, Any]] = []
    mutation_rows: list[dict[str, Any]] = []
    skipped: list[dict[str, str]] = []
    first_packet_brief: dict[str, Any] | None = None

    for case in _n7_cases():
        packet, skip_reason = _n7_packet_from_case(case)
        if packet is None:
            skipped.append({"case_id": case.case_id, "reason": str(skip_reason)})
            continue
        if first_packet_brief is None:
            first_packet_brief = _first_packet_brief(packet)

        verification = verify_observed_frontier_packet(packet)
        rows.append(_packet_summary(packet, verification))
        for mutation_id, mutated_packet in [*_mutated_packets(packet), *_observed_mutated_packets(packet)]:
            mutated_verification = verify_observed_frontier_packet(mutated_packet)
            mutation_rows.append(
                {
                    "case_id": packet["case_id"],
                    "mutation_id": mutation_id,
                    "accepted": bool(mutated_verification["ok"]),
                    "reasons": mutated_verification["reasons"],
                }
            )

    return {
        "schema": SEARCH_SCHEMA,
        "seed": N7_SEED,
        "scope": SCOPE,
        "case_count": TARGET_CASE_COUNT,
        "strict_packet_count": len(rows),
        "valid_observed_packet_count": sum(1 for row in rows if row["ok"]),
        "skipped_count": len(skipped),
        "skipped": skipped,
        "first_invalid_packet": next((row for row in rows if not row["ok"]), None),
        "mutation_count": len(mutation_rows),
        "observed_mutation_count_per_packet": EXPECTED_OBSERVED_MUTATION_COUNT,
        "mutation_accept_count": sum(1 for row in mutation_rows if row["accepted"]),
        "first_mutation_accept": next((row for row in mutation_rows if row["accepted"]), None),
        "coverage": {
            "n_counts": {"7": sum(1 for row in rows if int(row["bit_count"]) == 7)},
            "fee_bps_counts": {
                str(fee_bps): sum(1 for row in rows if int(row["fee_bps"]) == fee_bps)
                for fee_bps in sorted({int(row["fee_bps"]) for row in rows})
            },
            "pattern_counts": {
                str(pattern): sum(1 for row in rows if row["pattern"] == pattern)
                for pattern in sorted({str(row["pattern"]) for row in rows})
            },
            "max_bit_count": max((int(row["bit_count"]) for row in rows), default=0),
            "max_children_count": max((int(row["children_count"]) for row in rows), default=0),
            "min_children_count": min((int(row["children_count"]) for row in rows), default=0),
            "reason_classes": sorted(
                {
                    reason
                    for mutation_row in mutation_rows
                    for reason in mutation_row["reasons"]
                }
            ),
        },
        "total_children_count": sum(int(row["children_count"]) for row in rows),
        "total_packet_canonical_bytes": sum(int(row["packet_canonical_bytes"]) for row in rows),
        "max_packet_canonical_bytes": max(
            (int(row["packet_canonical_bytes"]) for row in rows),
            default=0,
        ),
        "first_packet": first_packet_brief,
        "cases": rows,
        "mutations": mutation_rows,
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def deterministic_replay(first_search: Mapping[str, Any]) -> dict[str, Any]:
    second_search = run_search()
    first_hash = _sha256_json(_strip_timing(first_search))
    second_hash = _sha256_json(_strip_timing(second_search))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    expected_mutations = search["strict_packet_count"] * (7 + EXPECTED_OBSERVED_MUTATION_COUNT)
    ok = bool(
        search["case_count"] == TARGET_CASE_COUNT
        and search["strict_packet_count"] == TARGET_CASE_COUNT
        and search["valid_observed_packet_count"] == TARGET_CASE_COUNT
        and search["skipped_count"] == 0
        and search["first_invalid_packet"] is None
        and search["coverage"]["min_children_count"] == EXPECTED_CHILDREN_PER_CASE
        and search["coverage"]["max_children_count"] == EXPECTED_CHILDREN_PER_CASE
        and search["mutation_count"] == expected_mutations
        and search["mutation_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A deterministic host checker validates observed child-frontier obligations "
            "for the committed n=7 strict zero-min randomized corpus."
        ),
        "authority_boundary": (
            "Research-only observed-frontier evidence; no settlement, state-root, "
            "production, routing, matching, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "replay_command": (
            "python3 tools/check_ab_strict_zero_min_observed_frontier_n7_randomized_20260629.py"
        ),
        "non_claims": [
            "This checker is bounded to the committed four-case n=7 randomized corpus.",
            "This checker does not prove generation of the full child frontier in Lean.",
            "This checker does not prove recursive subset-mask induction.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "Nonzero min_amount_out batches are outside this artifact.",
            "This checker does not cover n=8 observed-frontier packets.",
            "No settlement, state-root, production, routing, matching, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# ZenoDEX AB Strict Zero-Min Observed Frontier n=7 Randomized",
        "",
        "## Summary",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Metrics",
        "",
        f"- Deterministic seed: `{search['seed']}`",
        f"- Cases checked: `{search['case_count']}`",
        f"- Valid observed-frontier packets: `{search['valid_observed_packet_count']}`",
        f"- Children per packet: `{coverage['max_children_count']}`",
        f"- Total observed children: `{search['total_children_count']}`",
        f"- Packet mutations checked: `{search['mutation_count']}`",
        f"- Mutation accepts: `{search['mutation_accept_count']}`",
        f"- Total canonical packet bytes replayed: `{search['total_packet_canonical_bytes']}`",
        f"- Max canonical packet bytes: `{search['max_packet_canonical_bytes']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Pattern histogram: `{coverage['pattern_counts']}`",
        f"- Reject reason classes: `{coverage['reason_classes']}`",
        "",
        "## First Packet Summary",
        "",
        "```json",
        json.dumps(search["first_packet"], indent=2, sort_keys=True),
        "```",
        "",
        "## Case Summary",
        "",
        "| case | ok | fee | children | packet bytes | key |",
        "| --- | --- | ---: | ---: | ---: | --- |",
    ]
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['fee_bps']}` | "
            f"`{row['children_count']}` | `{row['packet_canonical_bytes']}` | "
            f"`{row['economic_keys']['compressed']}` |"
        )
    lines.extend(["", "## Mutation Summary", "", "| mutation | accepted count |", "| --- | ---: |"])
    for mutation_id in sorted({row["mutation_id"] for row in search["mutations"]}):
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
