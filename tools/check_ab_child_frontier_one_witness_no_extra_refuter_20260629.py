#!/usr/bin/env python3
"""Refute standalone no-extra claims for one-witness child-frontier packets.

This research-only checker builds a bounded countermodel: the same one-witness
packet covers every advertised child state in two worlds, but one world has an
extra generated state that is invisible to a verifier that only reads the
one-witness packet.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import time
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_one_witness_no_extra_refuter_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_ONE_WITNESS_NO_EXTRA_REFUTER_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_child_frontier_one_witness_packet.v1"
REPORT_SCHEMA = "zenodex.ab_child_frontier_one_witness_no_extra_refuter_report.v1"
SEARCH_SCHEMA = "zenodex/ab_child_frontier_one_witness_no_extra_refuter_search/v1"
SCOPE = "one_witness_child_frontier_no_extra_insufficiency"
AUTHORITY_BOUNDARY = (
    "Research-only certificate-boundary evidence; no settlement, state-root, "
    "production, routing, matching, pool-mutation, or governance authority."
)
EXPECTED_NEGATIVE_CONTROL_COUNT = 6


def _sha256_json(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _packet_hash(packet: Mapping[str, Any]) -> str:
    payload = {key: value for key, value in packet.items() if key != "packet_hash"}
    return _sha256_json(payload)


def _with_packet_hash(packet: dict[str, Any]) -> dict[str, Any]:
    packet = copy.deepcopy(packet)
    packet["packet_hash"] = _packet_hash(packet)
    return packet


def _strip_timing(payload: Any) -> Any:
    if isinstance(payload, dict):
        return {k: _strip_timing(v) for k, v in payload.items() if k != "elapsed_ms"}
    if isinstance(payload, list):
        return [_strip_timing(v) for v in payload]
    return payload


def _state(processed_reserve_in: int, reserve_out: int) -> dict[str, int]:
    return {
        "processed_reserve_in": int(processed_reserve_in),
        "reserve_out": int(reserve_out),
    }


def _state_key(state: Mapping[str, Any]) -> tuple[int, int]:
    return int(state["processed_reserve_in"]), int(state["reserve_out"])


def _sorted_state_rows(states: Iterable[Mapping[str, Any]]) -> list[dict[str, int]]:
    return [
        _state(processed_reserve_in, reserve_out)
        for processed_reserve_in, reserve_out in sorted(_state_key(row) for row in states)
    ]


def build_one_witness_packet() -> dict[str, Any]:
    child_states = [_state(100, 9900), _state(140, 9861)]
    witness_rows = [
        {
            "child_state": child_states[0],
            "parent_state": _state(0, 10000),
            "step_id": "swap_a",
        },
        {
            "child_state": child_states[1],
            "parent_state": _state(100, 9900),
            "step_id": "swap_b",
        },
    ]
    packet = {
        "schema": PACKET_SCHEMA,
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "coverage_witness_bound": True,
        "standalone_no_extra_bound": False,
        "child_states": child_states,
        "witness_rows": witness_rows,
        "witness_rows_digest": _sha256_json(witness_rows),
    }
    return _with_packet_hash(packet)


def coverage_only_verify(packet: Mapping[str, Any] | None) -> dict[str, Any]:
    if packet is None:
        return {"ok": False, "reasons": ["packet_missing"]}
    reasons: list[str] = []
    if packet.get("schema") != PACKET_SCHEMA:
        reasons.append("packet_schema_mismatch")
    if packet.get("scope") != SCOPE:
        reasons.append("packet_scope_mismatch")
    if packet.get("authority_boundary") != AUTHORITY_BOUNDARY:
        reasons.append("authority_boundary_mismatch")
    if packet.get("packet_hash_bound") is not True:
        reasons.append("packet_hash_bound_missing")
    if packet.get("no_authority_effect") is not True:
        reasons.append("authority_effect_present")
    if packet.get("coverage_witness_bound") is not True:
        reasons.append("coverage_witness_bound_missing")
    if packet.get("standalone_no_extra_bound") is True:
        reasons.append("forbidden_standalone_no_extra_claim")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")

    child_states = packet.get("child_states", [])
    witness_rows = packet.get("witness_rows", [])
    try:
        child_keys = {_state_key(row) for row in child_states}
        witness_child_keys = [_state_key(row["child_state"]) for row in witness_rows]
    except (KeyError, TypeError, ValueError):
        return {"ok": False, "reasons": ["packet_state_shape_malformed"]}

    seen: set[tuple[int, int]] = set()
    for key in witness_child_keys:
        if key not in child_keys:
            reasons.append("witness_child_not_in_frontier")
        if key in seen:
            reasons.append("duplicate_witness_row")
        seen.add(key)
    missing = child_keys - seen
    if missing:
        reasons.append("missing_child_state_witness")
    if packet.get("witness_rows_digest") != _sha256_json(witness_rows):
        reasons.append("witness_rows_digest_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "child_state_count": len(child_keys),
        "witness_count": len(witness_rows),
        "covered_child_state_count": len(child_keys & seen),
    }


def full_frontier_verify(
    packet: Mapping[str, Any],
    *,
    generated_states: Iterable[Mapping[str, Any]],
) -> dict[str, Any]:
    coverage = coverage_only_verify(packet)
    child_keys = {_state_key(row) for row in packet.get("child_states", [])}
    generated_keys = {_state_key(row) for row in generated_states}
    missing_generated = child_keys - generated_keys
    extra_generated = generated_keys - child_keys
    reasons = list(coverage["reasons"])
    if missing_generated:
        reasons.append("generated_frontier_missing_child_state")
    if extra_generated:
        reasons.append("generated_frontier_extra_child_state")
    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "generated_state_count": len(generated_keys),
        "missing_generated_state_count": len(missing_generated),
        "extra_generated_state_count": len(extra_generated),
        "extra_generated_states": _sorted_state_rows(
            _state(processed_reserve_in, reserve_out)
            for processed_reserve_in, reserve_out in extra_generated
        ),
    }


def _negative_controls(packet: Mapping[str, Any]) -> list[dict[str, Any]]:
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    missing_witness = copy.deepcopy(packet)
    missing_witness["witness_rows"] = missing_witness["witness_rows"][1:]
    missing_witness["witness_rows_digest"] = _sha256_json(missing_witness["witness_rows"])
    controls.append(
        (
            "missing_child_state_witness",
            _with_packet_hash(missing_witness),
            "missing_child_state_witness",
        )
    )

    duplicate = copy.deepcopy(packet)
    duplicate["witness_rows"].append(copy.deepcopy(duplicate["witness_rows"][0]))
    duplicate["witness_rows_digest"] = _sha256_json(duplicate["witness_rows"])
    controls.append(
        ("duplicate_witness_row", _with_packet_hash(duplicate), "duplicate_witness_row")
    )

    bad_child = copy.deepcopy(packet)
    bad_child["witness_rows"][0]["child_state"] = _state(999, 999)
    bad_child["witness_rows_digest"] = _sha256_json(bad_child["witness_rows"])
    controls.append(
        (
            "witness_child_not_in_frontier",
            _with_packet_hash(bad_child),
            "witness_child_not_in_frontier",
        )
    )

    bad_no_extra_claim = copy.deepcopy(packet)
    bad_no_extra_claim["standalone_no_extra_bound"] = True
    controls.append(
        (
            "forbidden_standalone_no_extra_claim",
            _with_packet_hash(bad_no_extra_claim),
            "forbidden_standalone_no_extra_claim",
        )
    )

    bad_authority = copy.deepcopy(packet)
    bad_authority["no_authority_effect"] = False
    controls.append(
        (
            "authority_effect_present",
            _with_packet_hash(bad_authority),
            "authority_effect_present",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, mutated_packet, expected_reason in controls:
        result = coverage_only_verify(mutated_packet)
        output.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(result["ok"]),
                "expected_reason": expected_reason,
                "reasons": result["reasons"],
            }
        )
    return output


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    packet = build_one_witness_packet()
    baseline_generated_states = copy.deepcopy(packet["child_states"])
    hidden_extra_state = _state(170, 9830)
    extra_generated_states = [*copy.deepcopy(packet["child_states"]), hidden_extra_state]

    baseline_coverage = coverage_only_verify(packet)
    baseline_full = full_frontier_verify(packet, generated_states=baseline_generated_states)
    extra_coverage = coverage_only_verify(packet)
    extra_full = full_frontier_verify(packet, generated_states=extra_generated_states)
    negative_controls = _negative_controls(packet)

    return {
        "schema": SEARCH_SCHEMA,
        "packet_hash": packet["packet_hash"],
        "witness_rows_digest": packet["witness_rows_digest"],
        "child_state_count": len(packet["child_states"]),
        "witness_count": len(packet["witness_rows"]),
        "baseline_generated_state_count": len(baseline_generated_states),
        "extra_generated_state_count": len(extra_generated_states),
        "hidden_extra_state": hidden_extra_state,
        "same_packet_hash_for_both_worlds": True,
        "coverage_only_baseline": baseline_coverage,
        "coverage_only_extra_world": extra_coverage,
        "full_baseline": baseline_full,
        "full_extra_world": extra_full,
        "countermodel_valid": bool(
            baseline_coverage["ok"]
            and extra_coverage["ok"]
            and baseline_full["ok"]
            and not extra_full["ok"]
            and "generated_frontier_extra_child_state" in extra_full["reasons"]
        ),
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(
            1 for control in negative_controls if control["accepted"]
        ),
        "negative_controls": negative_controls,
        "coverage_reason_classes": sorted(
            {reason for control in negative_controls for reason in control["reasons"]}
        ),
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def deterministic_replay(first_search: Mapping[str, Any]) -> dict[str, Any]:
    second_search = run_search()
    first_hash = _sha256_json(_strip_timing(first_search))
    second_hash = _sha256_json(_strip_timing(second_search))
    return {
        "ok": first_hash == second_hash,
        "first_hash": first_hash,
        "second_hash": second_hash,
    }


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["countermodel_valid"]
        and search["same_packet_hash_for_both_worlds"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded countermodel refutes standalone no-extra claims for "
            "one-witness child-frontier packets: the same packet covers all advertised "
            "child states while a hidden extra generated state remains invisible to "
            "coverage-only verification."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-ONE-WITNESS-NO-EXTRA-REFUTER-20260629",
            "mechanism_change": (
                "Treat one-witness child-frontier packets as coverage certificates, "
                "not standalone no-extra certificates."
            ),
            "representation_shift_used": "counterexample_boundary",
            "expected_metric_delta": {
                "safety": "+prevents overclaim",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+constant refuter only",
                "determinism_simplicity": "+clear certificate boundary",
            },
            "null_hypothesis": (
                "One predecessor witness per child state is sufficient to prove no "
                "extra generated child states."
            ),
            "falsification_recipe": (
                "Construct two worlds with identical one-witness packet hashes where "
                "coverage-only verification accepts both, but full generated-state "
                "verification rejects one for an extra generated state."
            ),
            "support_recipe": (
                "Require future no-extra certificates to bind all generated-state "
                "images, a generated-state digest, or a theorem strong enough to "
                "derive no-extra."
            ),
            "formal_obligations": (
                "Lean or Tau claims must distinguish coverage from no-extra generation."
            ),
            "risk_modes": [
                "coverage certificate overclaimed as equality certificate",
                "hidden generated state",
                "authority leakage",
                "stale packet hash",
            ],
            "status": "falsified",
        },
        "design_recommendation": [
            "Keep one-witness packets as coverage certificates only.",
            "For no-extra, add a generated-image digest, all-transition image check, or a stronger Lean theorem.",
            "Preserve the no-authority boundary until a production verifier independently checks the complete equality obligation.",
        ],
        "replay_command": (
            "python3 tools/check_ab_child_frontier_one_witness_no_extra_refuter_20260629.py"
        ),
        "non_claims": [
            "This refuter is a bounded certificate-boundary countermodel, not a proof about all possible ZenoDEX frontier certificates.",
            "This refuter does not invalidate n=7 or n=8 witness-coverage evidence.",
            "This refuter does not prove child-frontier generation in Lean.",
            "This refuter does not prove Python-to-Lean refinement.",
            "This refuter does not cover nonzero min_amount_out behavior.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB One-Witness No-Extra Refuter - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Countermodel",
        "",
        f"- Packet hash: `{search['packet_hash']}`",
        f"- Witness rows: `{search['witness_count']}`",
        f"- Advertised child states: `{search['child_state_count']}`",
        f"- Baseline generated states: `{search['baseline_generated_state_count']}`",
        f"- Extra-world generated states: `{search['extra_generated_state_count']}`",
        f"- Same packet hash for both worlds: `{search['same_packet_hash_for_both_worlds']}`",
        f"- Coverage-only accepts baseline: `{search['coverage_only_baseline']['ok']}`",
        f"- Coverage-only accepts extra world: `{search['coverage_only_extra_world']['ok']}`",
        f"- Full verifier accepts baseline: `{search['full_baseline']['ok']}`",
        f"- Full verifier accepts extra world: `{search['full_extra_world']['ok']}`",
        f"- Countermodel valid: `{search['countermodel_valid']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "The two worlds expose the same one-witness packet to a coverage-only verifier.",
        "Only a verifier that also receives or recomputes generated states can reject the extra-world case.",
        "",
        "## Hidden Extra State",
        "",
        "```json",
        json.dumps(search["hidden_extra_state"], indent=2, sort_keys=True),
        "```",
        "",
        "## Full Extra-World Rejection",
        "",
        "```json",
        json.dumps(search["full_extra_world"], indent=2, sort_keys=True),
        "```",
        "",
        "## Negative Controls",
        "",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        "",
        "| mutation | accepted | expected reason |",
        "| --- | ---: | --- |",
    ]
    for control in search["negative_controls"]:
        lines.append(
            f"| `{control['mutation_id']}` | `{control['accepted']}` | `{control['expected_reason']}` |"
        )
    lines.extend(["", "## Hypothesis Card", "", "```json"])
    lines.append(json.dumps(report["hypothesis_card"], indent=2, sort_keys=True))
    lines.extend(["```", "", "## Design Recommendation", ""])
    for item in report["design_recommendation"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="print full report")
    args = parser.parse_args()
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    _write_markdown(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
