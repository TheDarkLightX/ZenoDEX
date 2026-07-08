#!/usr/bin/env python3
"""Check observed child-frontier host packets for the AB strict zero-min bridge.

This research-only checker validates the host-side premise shape mirrored by
Lean's `strictObservedFullMaskEmitterTableValid` theorem. It consumes the
deterministic stress packets from the strict zero-min emitter witness search,
then adds observed-frontier checks that the base packet verifier intentionally
does not own.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _all_bits_below_set,
    _mutated_packets,
    _sha256_json,
    _strip_timing,
    _with_packet_hash,
    verify_witness_packet,
)
from tools.check_ab_strict_zero_min_emitter_witness_stress import (  # noqa: E402
    CASE_COUNT,
    MIN_STRICT_PACKET_COUNT,
    SEED,
    _build_packet_from_case,
    _iter_cases,
)

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_strict_zero_min_observed_frontier_witness_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_OBSERVED_FRONTIER_WITNESS_20260629.md"
)

EXPECTED_OBSERVED_MUTATION_COUNT = 6


def _as_int(raw_number: object, *, default: int = -1) -> int:
    try:
        return int(raw_number)
    except (TypeError, ValueError):
        return default


def _selected_record(child: Mapping[str, Any]) -> Mapping[str, Any]:
    selected = child.get("selected")
    return selected if isinstance(selected, Mapping) else {}


def _records_for_child(child: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    records = child.get("all_records")
    if not isinstance(records, list):
        return []
    return [record for record in records if isinstance(record, Mapping)]


def _record_identity(record: Mapping[str, Any]) -> tuple[int, int, tuple[str, ...]]:
    return (
        _as_int(record.get("processed_reserve_in")),
        _as_int(record.get("reserve_out")),
        tuple(str(order_id) for order_id in record.get("order_ids", [])),
    )


def _child_identity(child: Mapping[str, Any]) -> tuple[int, int, int, tuple[str, ...]]:
    selected = _selected_record(child)
    processed_reserve_in, reserve_out, order_ids = _record_identity(selected)
    return (_as_int(child.get("mask_id")), processed_reserve_in, reserve_out, order_ids)


def _surplus(initial_reserve_out: int, record: Mapping[str, Any]) -> int:
    return int(initial_reserve_out) - _as_int(record.get("reserve_out"), default=0)


def verify_observed_frontier_packet(packet: Mapping[str, Any]) -> dict[str, Any]:
    """Validate observed-frontier obligations for one strict zero-min packet."""

    reasons: list[str] = []
    try:
        base_verification = verify_witness_packet(packet)
    except Exception as exc:  # pragma: no cover - malformed external packet guard.
        base_verification = {"ok": False, "reasons": [f"exception:{type(exc).__name__}"], "checks": {}}
    if base_verification["ok"] is not True:
        reasons.append("base_witness_packet_invalid")

    bit_count = _as_int(packet.get("bit_count"))
    initial_reserve_out = _as_int(packet.get("initial_reserve_out"), default=0)
    executed_input = _as_int(packet.get("executed_input"))
    winner = packet.get("winner")
    children = packet.get("children")
    economic_keys = packet.get("economic_keys")
    if not isinstance(winner, Mapping):
        winner = {}
        reasons.append("observed_winner_missing")
    if not isinstance(children, list) or not children:
        children = []
        reasons.append("observed_children_missing")
    if not isinstance(economic_keys, Mapping):
        economic_keys = {}
        reasons.append("observed_economic_keys_missing")

    winner_selected = _selected_record(winner)
    winner_identity = _child_identity(winner)
    child_identities: set[tuple[int, int, int, tuple[str, ...]]] = set()
    child_selected_reserve_out_values: list[int] = []

    for child in children:
        if not isinstance(child, Mapping):
            reasons.append("observed_child_not_mapping")
            continue
        child_identities.add(_child_identity(child))
        child_selected = _selected_record(child)
        child_selected_reserve_out_values.append(_as_int(child_selected.get("reserve_out"), default=0))

        if not _all_bits_below_set(_as_int(child.get("mask_id")), bit_count):
            reasons.append("child_missing_full_mask_coverage")

        records = _records_for_child(child)
        if not records:
            reasons.append("child_local_pruning_records_missing")
            continue
        if _as_int(child.get("all_records_count"), default=len(records)) != len(records):
            reasons.append("child_all_records_count_mismatch")
        if child.get("all_records_digest") != _sha256_json(records):
            reasons.append("child_all_records_digest_mismatch")

        selected_identity = _record_identity(child_selected)
        record_identities = {_record_identity(record) for record in records}
        if selected_identity not in record_identities:
            reasons.append("child_local_pruning_selected_not_record")

        selected_processed_reserve_in = _as_int(child_selected.get("processed_reserve_in"))
        selected_reserve_out = _as_int(child_selected.get("reserve_out"))
        for record in records:
            if _as_int(record.get("processed_reserve_in")) != selected_processed_reserve_in:
                reasons.append("child_local_pruning_processed_reserve_in_mismatch")
            if selected_reserve_out > _as_int(record.get("reserve_out")):
                reasons.append("child_local_pruning_reserve_out_not_min")

    if winner_identity not in child_identities:
        reasons.append("observed_winner_not_in_children")

    winner_reserve_out = _as_int(winner_selected.get("reserve_out"), default=0)
    if any(winner_reserve_out > child_reserve_out for child_reserve_out in child_selected_reserve_out_values):
        reasons.append("observed_winner_not_selected_family_dominator")

    if winner_reserve_out <= 0:
        reasons.append("observed_empty_suffix_not_executable")

    expected_key = [executed_input, _surplus(initial_reserve_out, winner_selected)]
    if economic_keys.get("compressed") != expected_key:
        reasons.append("observed_economic_key_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "checks": {
            "base_witness_packet_ok": base_verification["ok"] is True,
            "base_reasons": base_verification["reasons"],
            "all_children_cover_full_mask": "child_missing_full_mask_coverage" not in unique_reasons,
            "all_children_locally_pruned": not any(
                reason.startswith("child_local_pruning_") for reason in unique_reasons
            ),
            "winner_member_of_observed_children": winner_identity in child_identities,
            "winner_selected_family_dominator": "observed_winner_not_selected_family_dominator"
            not in unique_reasons,
            "empty_suffix_executable": winner_reserve_out > 0,
            "economic_key_matches_witness": economic_keys.get("compressed") == expected_key,
            "observed_child_count": len(children),
        },
    }


def _replace_first_child(packet: dict[str, Any], replacement_child: Mapping[str, Any]) -> None:
    packet["children"][0] = copy.deepcopy(replacement_child)


def _observed_mutated_packets(packet: Mapping[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    rows: list[tuple[str, dict[str, Any]]] = []
    children = packet.get("children")
    if not isinstance(children, list) or not children:
        return rows
    first_child = copy.deepcopy(children[0])
    winner = copy.deepcopy(packet["winner"])
    winner_reserve_out = _as_int(winner["selected"]["reserve_out"], default=1)

    bad_child_mask = copy.deepcopy(packet)
    bad_child = copy.deepcopy(first_child)
    bad_child["mask_id"] = _as_int(packet["full_mask"]) ^ 1
    _replace_first_child(bad_child_mask, bad_child)
    rows.append(("child_mask_missing_bit", _with_packet_hash(bad_child_mask)))

    bad_selected_identity = copy.deepcopy(packet)
    bad_child = copy.deepcopy(first_child)
    bad_child["selected"]["order_ids"] = [*bad_child["selected"]["order_ids"], "mutated-order"]
    bad_child["selected"]["order_short"] = [*bad_child["selected"].get("order_short", []), "mut"]
    _replace_first_child(bad_selected_identity, bad_child)
    rows.append(("child_selected_not_record", _with_packet_hash(bad_selected_identity)))

    bad_processed_reserve_in = copy.deepcopy(packet)
    bad_child = copy.deepcopy(first_child)
    extra_record = copy.deepcopy(bad_child["selected"])
    extra_record["processed_reserve_in"] = _as_int(extra_record["processed_reserve_in"]) + 1
    bad_child["all_records"].append(extra_record)
    bad_child["all_records_count"] = len(bad_child["all_records"])
    _replace_first_child(bad_processed_reserve_in, bad_child)
    rows.append(("child_processed_reserve_in_mismatch", _with_packet_hash(bad_processed_reserve_in)))

    bad_local_min = copy.deepcopy(packet)
    bad_child = copy.deepcopy(first_child)
    better_record = copy.deepcopy(bad_child["selected"])
    better_record["reserve_out"] = max(0, _as_int(better_record["reserve_out"]) - 1)
    bad_child["all_records"].append(better_record)
    bad_child["all_records_count"] = len(bad_child["all_records"])
    _replace_first_child(bad_local_min, bad_child)
    rows.append(("child_selected_not_local_min", _with_packet_hash(bad_local_min)))

    bad_winner_dominance = copy.deepcopy(packet)
    bad_child = copy.deepcopy(first_child)
    bad_child["selected"]["reserve_out"] = max(0, winner_reserve_out - 1)
    bad_child["all_records"] = [copy.deepcopy(bad_child["selected"])]
    bad_child["all_records_count"] = len(bad_child["all_records"])
    _replace_first_child(bad_winner_dominance, bad_child)
    rows.append(("child_selected_family_beats_winner", _with_packet_hash(bad_winner_dominance)))

    bad_empty_suffix = copy.deepcopy(packet)
    bad_empty_suffix["winner"]["selected"]["reserve_out"] = 0
    bad_empty_suffix["winner"]["all_records"] = [copy.deepcopy(bad_empty_suffix["winner"]["selected"])]
    rows.append(("winner_empty_suffix", _with_packet_hash(bad_empty_suffix)))

    return rows


def _iter_packets() -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    packets: list[dict[str, Any]] = []
    skipped: list[dict[str, str]] = []
    for stress_case in _iter_cases():
        packet, skip_reason = _build_packet_from_case(stress_case)
        if packet is None:
            skipped.append({"case_id": stress_case.case_id, "reason": str(skip_reason)})
            continue
        packets.append(packet)
    return packets, skipped


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    packets, skipped = _iter_packets()
    rows: list[dict[str, Any]] = []
    mutation_rows: list[dict[str, Any]] = []

    for packet in packets:
        verification = verify_observed_frontier_packet(packet)
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
                "economic_keys": packet["economic_keys"],
                "checks": verification["checks"],
            }
        )
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
        "schema": "zenodex/ab_strict_zero_min_observed_frontier_witness_search/v1",
        "seed": SEED,
        "case_count": CASE_COUNT,
        "strict_packet_count": len(rows),
        "valid_observed_packet_count": sum(1 for row in rows if row["ok"]),
        "skipped_count": len(skipped),
        "skipped": skipped[:20],
        "first_invalid_packet": next((row for row in rows if not row["ok"]), None),
        "mutation_count": len(mutation_rows),
        "observed_mutation_count_per_packet": EXPECTED_OBSERVED_MUTATION_COUNT,
        "mutation_accept_count": sum(1 for row in mutation_rows if row["accepted"]),
        "first_mutation_accept": next((row for row in mutation_rows if row["accepted"]), None),
        "coverage": {
            "n_counts": dict(
                sorted(
                    {
                        str(bit_count): sum(1 for row in rows if int(row["bit_count"]) == bit_count)
                        for bit_count in range(2, 7)
                    }.items()
                )
            ),
            "max_bit_count": max((int(row["bit_count"]) for row in rows), default=0),
            "max_children_count": max((int(row["children_count"]) for row in rows), default=0),
            "reason_classes": sorted(
                {
                    reason
                    for mutation_row in mutation_rows
                    for reason in mutation_row["reasons"]
                }
            ),
        },
        "cases": rows,
        "mutations": mutation_rows,
        "first_packet": packets[0] if packets else None,
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
        search["case_count"] == CASE_COUNT
        and search["strict_packet_count"] >= MIN_STRICT_PACKET_COUNT
        and search["valid_observed_packet_count"] == search["strict_packet_count"]
        and search["skipped_count"] == 0
        and search["mutation_count"] == expected_mutations
        and search["mutation_accept_count"] == 0
        and search["first_invalid_packet"] is None
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_observed_frontier_witness_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A deterministic host checker validates the observed child-frontier obligations "
            "assumed by Lean's strictObservedFullMaskEmitterTableValid endpoint across the "
            "strict zero-min stress packet corpus."
        ),
        "authority_boundary": (
            "Research-only observed-frontier evidence; no settlement, state-root, production, "
            "or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "non_claims": [
            "This checker does not prove generation of the full child frontier.",
            "This checker does not prove recursive subset-mask induction.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not define canonical tie order.",
            "Nonzero min_amount_out batches are outside this artifact.",
            "Host bitset equivalence remains a separate proof obligation.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_strict_zero_min_observed_frontier_witness.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Observed Frontier Witness - 2026-06-29",
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
        f"- Strict executable packets: `{search['strict_packet_count']}`",
        f"- Valid observed-frontier packets: `{search['valid_observed_packet_count']}`",
        f"- Skipped cases: `{search['skipped_count']}`",
        f"- Packet mutations checked: `{search['mutation_count']}`",
        f"- Mutation accepts: `{search['mutation_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Lean Premise Shape Checked",
        "",
        "```text",
        "strictObservedFullMaskEmitterTableValid table",
        "  -> packetHashBound and noAuthorityEffect rails",
        "  -> winnerMembershipBound",
        "  -> every observed child covers all bits below bitCount",
        "  -> every observed child satisfies local maskPruningInvariant",
        "  -> winner dominates observed selected family",
        "  -> winner executes empty suffix",
        "```",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Max bit count: `{coverage['max_bit_count']}`",
        f"- Max child frontier count: `{coverage['max_children_count']}`",
        f"- Reject reason classes: `{coverage['reason_classes']}`",
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
