#!/usr/bin/env python3
"""Build and refute host packets for the AB strict zero-min Lean witness.

This is a research-only bridge from the concrete one-record min-reserve-out
compressed DP to the Lean `StrictCompressedFullMaskEconomicWitness` contract.
It emits bounded host packets, checks the economic witness obligations, and
mutates the packets to keep the verifier contract fail-closed.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import (  # noqa: E402
    _best_order_by_objective_bruteforce,
    _best_order_by_objective_subset_dp,
)
from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_in  # noqa: E402
from tools.check_ab_zero_min_economic_compression_certificate import (  # noqa: E402
    _case,
    _context,
    _economic_key,
    _short,
)

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_strict_zero_min_emitter_witness_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_STRICT_ZERO_MIN_EMITTER_WITNESS_20260629.md"

WITNESS_CASE_PLAN: tuple[tuple[int, tuple[int, ...]], ...] = (
    (2, (0, 7)),
    (3, (0, 5)),
    (4, (2, 6)),
    (5, (1,)),
    (6, (0,)),
)


@dataclass(frozen=True)
class _HostRecord:
    processed_reserve_in: int
    reserve_out: int
    order_ids: tuple[str, ...]


@dataclass(frozen=True)
class _HostMaskSet:
    mask_id: int
    selected: _HostRecord
    all_records: tuple[_HostRecord, ...]


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


def _without_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in packet.items() if key != "packet_hash"}


def _packet_hash(packet: Mapping[str, Any]) -> str:
    return _sha256_json(_without_packet_hash(packet))


def _with_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    out = dict(packet)
    out["packet_hash"] = _packet_hash(out)
    return out


def _record_json(record: _HostRecord) -> dict[str, Any]:
    return {
        "processed_reserve_in": int(record.processed_reserve_in),
        "reserve_out": int(record.reserve_out),
        "order_ids": list(record.order_ids),
        "order_short": _short(record.order_ids),
    }


def _mask_set_json(mask_set: _HostMaskSet, *, include_all_records: bool) -> dict[str, Any]:
    out: dict[str, Any] = {
        "mask_id": int(mask_set.mask_id),
        "selected": _record_json(mask_set.selected),
        "all_records_count": len(mask_set.all_records),
        "all_records_digest": _sha256_json([_record_json(record) for record in mask_set.all_records]),
    }
    if include_all_records:
        out["all_records"] = [_record_json(record) for record in mask_set.all_records]
    return out


def _all_bits_below_set(mask_id: int, bit_count: int) -> bool:
    return all(bool(mask_id & (1 << bit_index)) for bit_index in range(bit_count))


def _amount_sums(intents: list[Any]) -> list[int]:
    n = len(intents)
    return [
        sum(int(intent.get_field("amount_in")) for idx, intent in enumerate(intents) if mask & (1 << idx))
        for mask in range(1 << n)
    ]


def _full_state_records(intents: list[Any], context: Any) -> list[list[_HostRecord]]:
    n = len(intents)
    sums = _amount_sums(intents)
    dp: list[list[_HostRecord]] = [[] for _ in range(1 << n)]
    dp[0] = [_HostRecord(int(context.r_in0), int(context.r_out0), ())]
    for mask in range(1 << n):
        expected_r_in = int(context.r_in0) + int(sums[mask])
        for record in dp[mask]:
            if int(record.processed_reserve_in) != expected_r_in:
                continue
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                amount_in = int(intent.get_field("amount_in"))
                min_amount_out = int(intent.get_field("min_amount_out", 0))
                try:
                    quote = quote_cpmm_swap_exact_in(
                        reserve_in=int(record.processed_reserve_in),
                        reserve_out=int(record.reserve_out),
                        amount_in=amount_in,
                        fee_bps=int(context.pool_state.fee_bps),
                    )
                except ValueError:
                    continue
                if int(quote.amount_out) < min_amount_out:
                    continue
                dp[mask | bit].append(
                    _HostRecord(
                        int(quote.reserve_in_after),
                        int(quote.reserve_out_after),
                        (*record.order_ids, intent.intent_id),
                    )
                )
    return dp


def _compressed_records(intents: list[Any], context: Any) -> list[_HostRecord | None]:
    n = len(intents)
    sums = _amount_sums(intents)
    dp: list[_HostRecord | None] = [None for _ in range(1 << n)]
    dp[0] = _HostRecord(int(context.r_in0), int(context.r_out0), ())
    for mask in range(1 << n):
        record = dp[mask]
        if record is None:
            continue
        expected_r_in = int(context.r_in0) + int(sums[mask])
        for idx, intent in enumerate(intents):
            bit = 1 << idx
            if mask & bit:
                continue
            amount_in = int(intent.get_field("amount_in"))
            min_amount_out = int(intent.get_field("min_amount_out", 0))
            try:
                quote = quote_cpmm_swap_exact_in(
                    reserve_in=expected_r_in,
                    reserve_out=int(record.reserve_out),
                    amount_in=amount_in,
                    fee_bps=int(context.pool_state.fee_bps),
                )
            except ValueError:
                continue
            if int(quote.amount_out) < min_amount_out:
                continue
            next_record = _HostRecord(
                int(quote.reserve_in_after),
                int(quote.reserve_out_after),
                (*record.order_ids, intent.intent_id),
            )
            current = dp[mask | bit]
            if (
                current is None
                or next_record.reserve_out < current.reserve_out
                or (next_record.reserve_out == current.reserve_out and next_record.order_ids < current.order_ids)
            ):
                dp[mask | bit] = next_record
    return dp


def _child_frontier(full_records: list[_HostRecord], full_mask: int) -> list[_HostMaskSet]:
    return [
        _HostMaskSet(mask_id=full_mask, selected=record, all_records=(record,))
        for record in sorted(full_records, key=lambda item: (item.reserve_out, item.order_ids))
    ]


def _build_witness_packet(n: int, variant: int) -> dict[str, Any]:
    pool, intents, balances = _case(n, variant, min_pattern="zero")
    context = _context(pool, intents, balances)
    full_dp = _full_state_records(intents, context)
    compressed_dp = _compressed_records(intents, context)
    full_mask = (1 << n) - 1
    final_compressed = compressed_dp[full_mask]
    if final_compressed is None:
        raise ValueError(f"compressed full mask not executable for n={n} variant={variant}")
    final_full_records = full_dp[full_mask]
    children = _child_frontier(final_full_records, full_mask)
    winner = _HostMaskSet(mask_id=full_mask, selected=final_compressed, all_records=(final_compressed,))
    parent_record = _HostRecord(int(context.r_in0), int(context.r_out0), ())
    parent = _HostMaskSet(mask_id=0, selected=parent_record, all_records=(parent_record,))
    full = _best_order_by_objective_subset_dp(intents, context)
    brute = _best_order_by_objective_bruteforce(intents, context) if n <= 7 else None
    compressed_order = tuple(
        {intent.intent_id: intent for intent in intents}[intent_id] for intent_id in final_compressed.order_ids
    )
    packet = {
        "schema": "zenodex.ab_strict_zero_min_emitter_witness_packet.v1",
        "case_id": f"n{n}_variant{variant}",
        "scope": "same_pool_same_direction_exact_in_zero_min_strict_executable",
        "authority_boundary": "research_only_no_settlement_or_state_authority",
        "no_authority_effect": True,
        "bit_count": int(n),
        "full_mask": int(full_mask),
        "initial_reserve_in": int(context.r_in0),
        "initial_reserve_out": int(context.r_out0),
        "executed_input": int(sum(int(intent.get_field("amount_in")) for intent in intents)),
        "pool": {
            "reserve_in": int(context.r_in0),
            "reserve_out": int(context.r_out0),
            "fee_bps": int(context.pool_state.fee_bps),
        },
        "amounts": [int(intent.get_field("amount_in")) for intent in intents],
        "min_amount_out": [int(intent.get_field("min_amount_out", 0)) for intent in intents],
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
    return _with_packet_hash(packet)


def _surplus(initial_reserve_out: int, record: Mapping[str, Any]) -> int:
    return int(initial_reserve_out) - int(record["reserve_out"])


def verify_witness_packet(packet: Mapping[str, Any]) -> dict[str, Any]:
    reasons: list[str] = []
    if packet.get("schema") != "zenodex.ab_strict_zero_min_emitter_witness_packet.v1":
        reasons.append("schema_mismatch")
    expected_hash = _packet_hash(packet)
    if packet.get("packet_hash") != expected_hash:
        reasons.append("packet_hash_mismatch")
    if packet.get("authority_boundary") != "research_only_no_settlement_or_state_authority":
        reasons.append("authority_boundary_mismatch")
    if packet.get("no_authority_effect") is not True:
        reasons.append("authority_effect_present")

    bit_count = int(packet.get("bit_count", -1))
    full_mask = int(packet.get("full_mask", -1))
    initial_reserve_in = int(packet.get("initial_reserve_in", -1))
    initial_reserve_out = int(packet.get("initial_reserve_out", -1))
    executed_input = int(packet.get("executed_input", -1))
    parent = packet.get("parent", {})
    winner = packet.get("winner", {})
    children = packet.get("children", [])
    winner_selected = winner.get("selected", {}) if isinstance(winner, Mapping) else {}

    if bit_count <= 0 or full_mask != (1 << bit_count) - 1:
        reasons.append("full_mask_not_range_mask")
    if not isinstance(parent, Mapping) or int(parent.get("mask_id", -1)) != 0:
        reasons.append("parent_mask_not_empty")
    if not isinstance(winner, Mapping) or int(winner.get("mask_id", -1)) != full_mask:
        reasons.append("winner_mask_not_full")
    if not _all_bits_below_set(int(winner.get("mask_id", -1)), bit_count):
        reasons.append("winner_missing_full_mask_bits")
    if int(parent.get("selected", {}).get("processed_reserve_in", -1)) != initial_reserve_in:
        reasons.append("parent_processed_reserve_in_mismatch")
    expected_final_r_in = initial_reserve_in + executed_input
    if int(winner_selected.get("processed_reserve_in", -1)) != expected_final_r_in:
        reasons.append("winner_processed_reserve_in_mismatch")
    if int(winner_selected.get("reserve_out", 0)) <= 0:
        reasons.append("winner_empty_suffix_not_executable")

    winner_identity = (
        int(winner.get("mask_id", -1)),
        int(winner_selected.get("processed_reserve_in", -1)),
        int(winner_selected.get("reserve_out", -1)),
        tuple(winner_selected.get("order_ids", [])),
    )
    child_identities = {
        (
            int(child.get("mask_id", -1)),
            int(child.get("selected", {}).get("processed_reserve_in", -1)),
            int(child.get("selected", {}).get("reserve_out", -1)),
            tuple(child.get("selected", {}).get("order_ids", [])),
        )
        for child in children
        if isinstance(child, Mapping)
    }
    if winner_identity not in child_identities:
        reasons.append("winner_not_in_child_frontier")

    child_surpluses: list[int] = []
    for child in children:
        if not isinstance(child, Mapping):
            continue
        records = child.get("all_records")
        if not isinstance(records, list) or not records:
            records = [child.get("selected", {})]
        for record in records:
            if isinstance(record, Mapping):
                child_surpluses.append(_surplus(initial_reserve_out, record))
    selected_surplus = _surplus(initial_reserve_out, winner_selected)
    full_frontier_surplus = max(child_surpluses) if child_surpluses else -1
    if selected_surplus < full_frontier_surplus:
        reasons.append("selected_key_does_not_dominate_full_frontier")
    keys = packet.get("economic_keys", {})
    expected_witness_key = [executed_input, selected_surplus]
    if keys.get("compressed") != expected_witness_key:
        reasons.append("compressed_key_mismatch_with_witness")
    if keys.get("compressed") != keys.get("full_subset_dp"):
        reasons.append("host_subset_dp_key_mismatch")
    if keys.get("brute_force") is not None and keys.get("compressed") != keys.get("brute_force"):
        reasons.append("host_bruteforce_key_mismatch")

    return {
        "ok": not reasons,
        "reasons": reasons,
        "checks": {
            "packet_hash_ok": packet.get("packet_hash") == expected_hash,
            "winner_covers_full_mask": _all_bits_below_set(int(winner.get("mask_id", -1)), bit_count),
            "winner_member_of_children": winner_identity in child_identities,
            "selected_surplus": selected_surplus,
            "full_frontier_surplus": full_frontier_surplus,
            "selected_key_dominates_full_frontier": selected_surplus >= full_frontier_surplus,
            "compressed_key_matches_witness": keys.get("compressed") == expected_witness_key,
            "empty_suffix_executable": int(winner_selected.get("reserve_out", 0)) > 0,
            "host_economic_key_parity": "host_subset_dp_key_mismatch" not in reasons
            and "host_bruteforce_key_mismatch" not in reasons,
            "no_authority_effect": packet.get("no_authority_effect") is True,
        },
    }


def _iter_cases() -> Iterable[tuple[int, int]]:
    for n, variants in WITNESS_CASE_PLAN:
        for variant in variants:
            yield int(n), int(variant)


def _mutated_packets(packet: Mapping[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    rows: list[tuple[str, dict[str, Any]]] = []
    bad_hash = dict(packet)
    bad_hash["packet_hash"] = "0" * 64
    rows.append(("bad_packet_hash", bad_hash))

    bad_authority = copy.deepcopy(packet)
    bad_authority["no_authority_effect"] = False
    rows.append(("authority_effect_present", _with_packet_hash(bad_authority)))

    bad_mask = copy.deepcopy(packet)
    bad_mask["winner"]["mask_id"] = int(packet["full_mask"]) ^ 1
    rows.append(("winner_missing_full_mask_bit", _with_packet_hash(bad_mask)))

    bad_children = copy.deepcopy(packet)
    bad_children["children"] = [
        child
        for child in bad_children["children"]
        if tuple(child["selected"]["order_ids"]) != tuple(packet["winner"]["selected"]["order_ids"])
    ]
    rows.append(("winner_removed_from_children", _with_packet_hash(bad_children)))

    bad_reserve = copy.deepcopy(packet)
    bad_reserve["winner"]["selected"]["reserve_out"] = int(packet["initial_reserve_out"])
    bad_reserve["winner"]["all_records"][0]["reserve_out"] = int(packet["initial_reserve_out"])
    rows.append(("selected_no_longer_dominates", _with_packet_hash(bad_reserve)))

    bad_input = copy.deepcopy(packet)
    bad_input["executed_input"] = int(packet["executed_input"]) + 1
    rows.append(("executed_input_mismatch", _with_packet_hash(bad_input)))

    bad_key = copy.deepcopy(packet)
    bad_key["economic_keys"]["compressed"] = [
        int(packet["economic_keys"]["compressed"][0]),
        int(packet["economic_keys"]["compressed"][1]) + 1,
    ]
    rows.append(("economic_key_mismatch", _with_packet_hash(bad_key)))

    return rows


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    packets = [_build_witness_packet(n, variant) for n, variant in _iter_cases()]
    rows = []
    mutation_rows = []
    for packet in packets:
        verification = verify_witness_packet(packet)
        rows.append(
            {
                "case_id": packet["case_id"],
                "ok": verification["ok"],
                "reasons": verification["reasons"],
                "packet_hash": packet["packet_hash"],
                "bit_count": packet["bit_count"],
                "children_count": len(packet["children"]),
                "compressed_table_count": len(packet["compressed_table"]),
                "winner_order": packet["winner"]["selected"]["order_short"],
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
        "schema": "zenodex/ab_strict_zero_min_emitter_witness_search/v1",
        "case_plan": [{"n": n, "variants": list(variants)} for n, variants in WITNESS_CASE_PLAN],
        "case_count": len(rows),
        "valid_packet_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_packet": next((row for row in rows if not row["ok"]), None),
        "mutation_count": len(mutation_rows),
        "mutation_accept_count": sum(1 for row in mutation_rows if row["accepted"]),
        "first_mutation_accept": next((row for row in mutation_rows if row["accepted"]), None),
        "cases": rows,
        "mutations": mutation_rows,
        "first_packet": packets[0] if packets else None,
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
        search["case_count"] == 8
        and search["valid_packet_count"] == search["case_count"]
        and search["mutation_count"] == search["case_count"] * 7
        and search["mutation_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_emitter_witness_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded host-side emitter witness packet schema maps strict zero-min compressed-DP "
            "outputs to the Lean full-mask economic witness contract and rejects packet mutations."
        ),
        "authority_boundary": "Research-only witness packets; no settlement, state-root, production, or governance authority.",
        "search": search,
        "deterministic_replay": deterministic,
        "non_claims": [
            "This is a bounded host witness/refuter, not a proof of full compressed-DP induction.",
            "The packet schema does not prove Lean-to-Python refinement.",
            "The packet schema does not define canonical tie order.",
            "Nonzero min_amount_out batches are outside this artifact.",
            "Host bitset equivalence remains a separate proof obligation.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_strict_zero_min_emitter_witness.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Emitter Witness - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Evidence Summary",
        "",
        f"- Witness packets checked: `{search['case_count']}`",
        f"- Valid witness packets: `{search['valid_packet_count']}`",
        f"- Packet mutations checked: `{search['mutation_count']}`",
        f"- Mutation accepts: `{search['mutation_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Lean Contract Mapping",
        "",
        "```text",
        "host packet parent/winner/children/bitCount/masks/initialReserveOut/executedInput",
        "  -> StrictCompressedFullMaskEconomicWitness",
        "strict host checks",
        "  -> strictCompressedFullMaskEconomicWitnessValid candidate obligation",
        "Lean endpoint",
        "  -> full-mask coverage, economic-key dominance, empty-suffix executability",
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
        "| case | ok | children | compressed table | key |",
        "| --- | --- | ---: | ---: | --- |",
    ]
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['children_count']}` | "
            f"`{row['compressed_table_count']}` | `{row['economic_keys']['compressed']}` |"
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
