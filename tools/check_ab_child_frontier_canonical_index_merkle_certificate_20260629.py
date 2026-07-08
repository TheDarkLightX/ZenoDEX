#!/usr/bin/env python3
"""Check canonical-index binding for AB child-frontier Merkle roots.

This research-only checker refines the count-aware Merkle certificate. A
count-aware verifier can still accept a permuted generated-image root for the
same child-state set. Canonical-index binding rejects that root malleability by
requiring each child state to appear at its sorted leaf index.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_child_frontier_count_aware_merkle_certificate_20260629 import (
    AUTHORITY_BOUNDARY,
    _child_states,
    _expected_sides,
    _leaf_hash,
    _node_hash,
    _packet_hash,
    _sha256_json,
    _sorted_state_rows,
    _state,
    _state_key,
    _state_set_digest,
    _strip_timing,
    _verify_proof_naive,
    _with_packet_hash,
    _witness_rows,
)

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_canonical_index_merkle_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_CANONICAL_INDEX_MERKLE_CERTIFICATE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_child_frontier_canonical_index_merkle_packet.v1"
REPORT_SCHEMA = "zenodex.ab_child_frontier_canonical_index_merkle_report.v1"
SEARCH_SCHEMA = "zenodex/ab_child_frontier_canonical_index_merkle_search/v1"
SCOPE = "bounded_ab_child_frontier_canonical_index_merkle_certificate"
EXPECTED_NEGATIVE_CONTROL_COUNT = 10


def _ordered_merkle_levels(ordered_states: Sequence[Mapping[str, Any]]) -> list[list[str]]:
    leaf_hashes = [_leaf_hash(state) for state in ordered_states]
    if not leaf_hashes:
        return [[_sha256_json({"schema": "zenodex.ab_child_frontier_merkle_node.v1", "empty": True})]]
    levels: list[list[str]] = [leaf_hashes]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        next_level: list[str] = []
        for index in range(0, len(previous), 2):
            left_hash = previous[index]
            right_hash = previous[index + 1] if index + 1 < len(previous) else left_hash
            next_level.append(_node_hash(left_hash, right_hash))
        levels.append(next_level)
    return levels


def _ordered_merkle_root(ordered_states: Sequence[Mapping[str, Any]]) -> str:
    return _ordered_merkle_levels(ordered_states)[-1][0]


def _ordered_membership_proof(
    ordered_states: Sequence[Mapping[str, Any]],
    state: Mapping[str, Any],
) -> dict[str, Any]:
    key_to_index = {_state_key(row): index for index, row in enumerate(ordered_states)}
    state_key = _state_key(state)
    if state_key not in key_to_index:
        return {"child_state": dict(state), "leaf_index": None, "proof": []}

    leaf_index = key_to_index[state_key]
    levels = _ordered_merkle_levels(ordered_states)
    proof: list[dict[str, str]] = []
    index = leaf_index
    for level in levels[:-1]:
        if index % 2 == 0:
            sibling_index = index + 1 if index + 1 < len(level) else index
            proof.append({"side": "right", "hash": level[sibling_index]})
        else:
            proof.append({"side": "left", "hash": level[index - 1]})
        index //= 2
    return {"child_state": dict(state), "leaf_index": leaf_index, "proof": proof}


def _canonical_index_by_state(
    child_states: Iterable[Mapping[str, Any]],
) -> dict[tuple[int, int], int]:
    return {
        _state_key(state): index
        for index, state in enumerate(_sorted_state_rows(child_states))
    }


def build_canonical_index_packet(
    *,
    child_states: list[dict[str, int]] | None = None,
    generated_order: list[dict[str, int]] | None = None,
    canonical_leaf_index_bound: bool = True,
) -> dict[str, Any]:
    child_states = copy.deepcopy(child_states if child_states is not None else _child_states())
    generated_order = copy.deepcopy(
        generated_order if generated_order is not None else _sorted_state_rows(child_states)
    )
    membership_rows = [
        _ordered_membership_proof(generated_order, child_state)
        for child_state in child_states
    ]
    witness_rows = _witness_rows(child_states)
    packet = {
        "schema": PACKET_SCHEMA,
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "coverage_witness_bound": True,
        "generated_image_root_bound": True,
        "generated_count_bound": True,
        "count_aware_membership_bound": True,
        "canonical_leaf_index_bound": bool(canonical_leaf_index_bound),
        "child_states": child_states,
        "generated_state_count": len(generated_order),
        "generated_state_root": _ordered_merkle_root(generated_order),
        "membership_rows": membership_rows,
        "witness_rows": witness_rows,
        "child_state_digest": _state_set_digest(child_states),
        "membership_rows_digest": _sha256_json(membership_rows),
        "witness_rows_digest": _sha256_json(witness_rows),
    }
    return _with_packet_hash(packet)


def _shared_packet_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["packet_missing"]
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
    if packet.get("generated_image_root_bound") is not True:
        reasons.append("generated_image_root_bound_missing")
    if packet.get("generated_count_bound") is not True:
        reasons.append("generated_count_bound_missing")
    if packet.get("count_aware_membership_bound") is not True:
        reasons.append("count_aware_membership_bound_missing")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _coverage_reasons(packet: Mapping[str, Any]) -> tuple[list[str], dict[str, int]]:
    reasons: list[str] = []
    child_states = packet.get("child_states", [])
    witness_rows = packet.get("witness_rows", [])
    try:
        child_keys = {_state_key(row) for row in child_states}
        witness_child_keys = [_state_key(row["child_state"]) for row in witness_rows]
    except (KeyError, TypeError, ValueError):
        return ["packet_state_shape_malformed"], {
            "child_state_count": 0,
            "witness_count": 0,
            "covered_child_state_count": 0,
        }
    if len(child_keys) != len(child_states):
        reasons.append("duplicate_child_state")
    seen: set[tuple[int, int]] = set()
    for key in witness_child_keys:
        if key not in child_keys:
            reasons.append("witness_child_not_in_frontier")
        if key in seen:
            reasons.append("duplicate_witness_row")
        seen.add(key)
    if child_keys - seen:
        reasons.append("missing_child_state_witness")
    if packet.get("child_state_digest") != _state_set_digest(child_states):
        reasons.append("child_state_digest_mismatch")
    if packet.get("witness_rows_digest") != _sha256_json(witness_rows):
        reasons.append("witness_rows_digest_mismatch")
    return reasons, {
        "child_state_count": len(child_keys),
        "witness_count": len(witness_rows),
        "covered_child_state_count": len(child_keys & seen),
    }


def verify_count_aware_only(packet: Mapping[str, Any] | None) -> dict[str, Any]:
    if packet is None:
        return {"ok": False, "reasons": ["packet_missing"]}
    reasons = _shared_packet_reasons(packet)
    coverage_reasons, counts = _coverage_reasons(packet)
    reasons.extend(coverage_reasons)

    child_states = packet.get("child_states", [])
    membership_rows = packet.get("membership_rows", [])
    generated_root = packet.get("generated_state_root")
    generated_count = packet.get("generated_state_count")
    if not isinstance(generated_root, str):
        reasons.append("generated_state_root_malformed")
    if not isinstance(generated_count, int):
        reasons.append("generated_state_count_malformed")
        generated_count = -1
    if generated_count != counts["child_state_count"]:
        reasons.append("generated_state_count_mismatch")
    if packet.get("membership_rows_digest") != _sha256_json(membership_rows):
        reasons.append("membership_rows_digest_mismatch")

    try:
        child_keys = {_state_key(row) for row in child_states}
        membership_keys = [_state_key(row["child_state"]) for row in membership_rows]
    except (KeyError, TypeError, ValueError):
        reasons.append("membership_row_shape_malformed")
        child_keys = set()
        membership_keys = []

    invalid_count = 0
    seen_membership_keys: set[tuple[int, int]] = set()
    for row in membership_rows:
        try:
            child_state = row["child_state"]
            key = _state_key(child_state)
            leaf_index = row["leaf_index"]
            proof = row["proof"]
        except (KeyError, TypeError, ValueError):
            reasons.append("membership_row_shape_malformed")
            invalid_count += 1
            continue
        if key not in child_keys:
            reasons.append("membership_child_not_in_frontier")
        if key in seen_membership_keys:
            reasons.append("duplicate_membership_proof")
        seen_membership_keys.add(key)
        if not isinstance(leaf_index, int):
            reasons.append("membership_leaf_index_malformed")
            invalid_count += 1
            continue
        expected_sides = _expected_sides(leaf_index, generated_count)
        if expected_sides is None:
            reasons.append("membership_leaf_index_out_of_range")
            invalid_count += 1
            continue
        if [step.get("side") for step in proof] != expected_sides:
            reasons.append("membership_proof_shape_mismatch")
            invalid_count += 1
            continue
        if isinstance(generated_root, str) and not _verify_proof_naive(
            child_state,
            proof,
            generated_root,
        ):
            reasons.append("membership_proof_hash_mismatch")
            invalid_count += 1
    if child_keys - set(membership_keys):
        reasons.append("missing_membership_proof")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        **counts,
        "generated_state_count": generated_count,
        "membership_count": len(membership_rows),
        "valid_membership_count": len(membership_rows) - invalid_count,
    }


def verify_canonical_index(packet: Mapping[str, Any] | None) -> dict[str, Any]:
    if packet is None:
        return {"ok": False, "reasons": ["packet_missing"]}
    result = verify_count_aware_only(packet)
    reasons = list(result["reasons"])
    if packet.get("canonical_leaf_index_bound") is not True:
        reasons.append("canonical_leaf_index_bound_missing")

    child_states = packet.get("child_states", [])
    membership_rows = packet.get("membership_rows", [])
    try:
        expected_index_by_key = _canonical_index_by_state(child_states)
    except (KeyError, TypeError, ValueError):
        expected_index_by_key = {}
        reasons.append("canonical_child_state_shape_malformed")

    seen_leaf_indices: set[int] = set()
    for row in membership_rows:
        try:
            key = _state_key(row["child_state"])
            leaf_index = row["leaf_index"]
        except (KeyError, TypeError, ValueError):
            reasons.append("membership_row_shape_malformed")
            continue
        if isinstance(leaf_index, int):
            if leaf_index in seen_leaf_indices:
                reasons.append("duplicate_leaf_index")
            seen_leaf_indices.add(leaf_index)
        if expected_index_by_key.get(key) != leaf_index:
            reasons.append("canonical_leaf_index_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        **result,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
    }


def _negative_controls(packet: Mapping[str, Any]) -> list[dict[str, Any]]:
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    bad_root = copy.deepcopy(packet)
    bad_root["generated_state_root"] = "0" * 64
    controls.append(
        (
            "generated_state_root_stale",
            _with_packet_hash(bad_root),
            "membership_proof_hash_mismatch",
        )
    )

    permuted = build_canonical_index_packet(
        child_states=packet["child_states"],
        generated_order=list(reversed(packet["child_states"])),
    )
    controls.append(
        (
            "canonical_leaf_index_mismatch",
            permuted,
            "canonical_leaf_index_mismatch",
        )
    )

    duplicate_leaf_index = copy.deepcopy(packet)
    duplicate_leaf_index["membership_rows"][1]["leaf_index"] = duplicate_leaf_index[
        "membership_rows"
    ][0]["leaf_index"]
    duplicate_leaf_index["membership_rows_digest"] = _sha256_json(
        duplicate_leaf_index["membership_rows"]
    )
    controls.append(
        (
            "duplicate_leaf_index",
            _with_packet_hash(duplicate_leaf_index),
            "duplicate_leaf_index",
        )
    )

    missing_membership = copy.deepcopy(packet)
    missing_membership["membership_rows"] = missing_membership["membership_rows"][1:]
    missing_membership["membership_rows_digest"] = _sha256_json(
        missing_membership["membership_rows"]
    )
    controls.append(
        (
            "missing_membership_proof",
            _with_packet_hash(missing_membership),
            "missing_membership_proof",
        )
    )

    bad_proof = copy.deepcopy(packet)
    bad_proof["membership_rows"][0]["proof"][0]["hash"] = "0" * 64
    bad_proof["membership_rows_digest"] = _sha256_json(bad_proof["membership_rows"])
    controls.append(
        (
            "membership_proof_hash_mismatch",
            _with_packet_hash(bad_proof),
            "membership_proof_hash_mismatch",
        )
    )

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

    missing_canonical_bound = copy.deepcopy(packet)
    missing_canonical_bound["canonical_leaf_index_bound"] = False
    controls.append(
        (
            "canonical_leaf_index_bound_missing",
            _with_packet_hash(missing_canonical_bound),
            "canonical_leaf_index_bound_missing",
        )
    )

    missing_count_aware_bound = copy.deepcopy(packet)
    missing_count_aware_bound["count_aware_membership_bound"] = False
    controls.append(
        (
            "count_aware_membership_bound_missing",
            _with_packet_hash(missing_count_aware_bound),
            "count_aware_membership_bound_missing",
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
        result = verify_canonical_index(mutated_packet)
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
    child_states = _child_states()
    canonical_packet = build_canonical_index_packet(child_states=child_states)
    permuted_packet = build_canonical_index_packet(
        child_states=child_states,
        generated_order=list(reversed(child_states)),
    )
    no_canonical_bound_packet = copy.deepcopy(canonical_packet)
    no_canonical_bound_packet["canonical_leaf_index_bound"] = False
    no_canonical_bound_packet = _with_packet_hash(no_canonical_bound_packet)

    count_aware_canonical = verify_count_aware_only(canonical_packet)
    count_aware_permuted = verify_count_aware_only(permuted_packet)
    canonical_index_canonical = verify_canonical_index(canonical_packet)
    canonical_index_permuted = verify_canonical_index(permuted_packet)
    canonical_index_missing_bound = verify_canonical_index(no_canonical_bound_packet)
    negative_controls = _negative_controls(canonical_packet)

    root_malleability_countermodel_valid = bool(
        count_aware_canonical["ok"]
        and count_aware_permuted["ok"]
        and canonical_packet["generated_state_root"] != permuted_packet["generated_state_root"]
        and canonical_index_canonical["ok"]
        and not canonical_index_permuted["ok"]
        and "canonical_leaf_index_mismatch" in canonical_index_permuted["reasons"]
    )

    return {
        "schema": SEARCH_SCHEMA,
        "canonical_packet_hash": canonical_packet["packet_hash"],
        "canonical_generated_state_root": canonical_packet["generated_state_root"],
        "permuted_packet_hash": permuted_packet["packet_hash"],
        "permuted_generated_state_root": permuted_packet["generated_state_root"],
        "child_state_digest": canonical_packet["child_state_digest"],
        "canonical_membership_rows_digest": canonical_packet["membership_rows_digest"],
        "permuted_membership_rows_digest": permuted_packet["membership_rows_digest"],
        "witness_rows_digest": canonical_packet["witness_rows_digest"],
        "child_state_count": len(child_states),
        "count_aware_canonical": count_aware_canonical,
        "count_aware_permuted": count_aware_permuted,
        "canonical_index_canonical": canonical_index_canonical,
        "canonical_index_permuted": canonical_index_permuted,
        "canonical_index_missing_bound": canonical_index_missing_bound,
        "root_malleability_countermodel_valid": root_malleability_countermodel_valid,
        "count_aware_accepts_permuted_root": bool(count_aware_permuted["ok"]),
        "canonical_index_rejects_permuted_root": not canonical_index_permuted["ok"],
        "canonical_index_rejects_missing_bound": not canonical_index_missing_bound["ok"],
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(
            1 for control in negative_controls if control["accepted"]
        ),
        "negative_controls": negative_controls,
        "reason_classes": sorted(
            {
                reason
                for result in [
                    canonical_index_permuted,
                    canonical_index_missing_bound,
                ]
                for reason in result["reasons"]
            }
            | {reason for control in negative_controls for reason in control["reasons"]}
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
        search["root_malleability_countermodel_valid"]
        and search["count_aware_accepts_permuted_root"]
        and search["canonical_index_rejects_permuted_root"]
        and search["canonical_index_rejects_missing_bound"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded canonical-index Merkle verifier rejects root malleability "
            "that count-aware membership verification accepts for the same "
            "child-state set."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-CANONICAL-INDEX-MERKLE-CERTIFICATE-20260629",
            "mechanism_change": (
                "Bind each child-state membership proof to the canonical sorted "
                "leaf index before accepting a generated-image Merkle root."
            ),
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+rejects permuted-root certificate malleability",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+canonical index equality checks",
                "determinism_simplicity": "+single root per sorted child-state set",
            },
            "null_hypothesis": (
                "Count-aware membership proofs are enough to make a generated-image "
                "root canonical for a bounded child-state set."
            ),
            "falsification_recipe": (
                "Build two packets for the same child states: one sorted, one "
                "permuted. Count-aware membership accepts both roots; canonical "
                "index verification rejects the permuted root."
            ),
            "support_recipe": (
                "Accept the canonical packet, reject the permuted packet with "
                "canonical_leaf_index_mismatch, reject missing canonical-index "
                "binding, and reject all negative controls."
            ),
            "formal_obligations": (
                "A formal version should prove canonical sorted leaf-index binding "
                "gives a unique Merkle root for a scoped unique child-state set."
            ),
            "risk_modes": [
                "permuted root malleability",
                "leaf index replay",
                "duplicate leaf index",
                "missing canonical-index rail",
                "authority leakage",
            ],
            "status": "supported_bounded",
        },
        "design_recommendation": [
            "Use canonical sorted leaf-index binding with count-aware Merkle membership proofs.",
            "Reject permuted roots even when they contain the same child-state set.",
            "Treat count-aware membership alone as a no-extra check, not as a canonical-root check.",
        ],
        "replay_command": (
            "python3 tools/check_ab_child_frontier_canonical_index_merkle_certificate_20260629.py"
        ),
        "non_claims": [
            "Scope is limited to a bounded certificate-boundary countermodel and checker design.",
            "This artifact does not prove child-frontier generation in Lean.",
            "This artifact does not prove Python-to-Lean refinement.",
            "This artifact does not replace a deterministic generated-image producer.",
            "This artifact does not cover nonzero min_amount_out behavior.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB Canonical-Index Merkle Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Certificate Shape",
        "",
        "```text",
        "generated_state_root + generated_state_count + count-aware membership proofs + canonical leaf-index binding",
        "```",
        "",
        "The verifier checks that each child state's proof leaf index equals its sorted canonical index.",
        "",
        "## Replay Result",
        "",
        f"- Canonical packet hash: `{search['canonical_packet_hash']}`",
        f"- Canonical generated-state root: `{search['canonical_generated_state_root']}`",
        f"- Permuted packet hash: `{search['permuted_packet_hash']}`",
        f"- Permuted generated-state root: `{search['permuted_generated_state_root']}`",
        f"- Child-state digest: `{search['child_state_digest']}`",
        f"- Canonical membership rows digest: `{search['canonical_membership_rows_digest']}`",
        f"- Permuted membership rows digest: `{search['permuted_membership_rows_digest']}`",
        f"- Witness rows digest: `{search['witness_rows_digest']}`",
        f"- Child states: `{search['child_state_count']}`",
        f"- Count-aware accepts canonical root: `{search['count_aware_canonical']['ok']}`",
        f"- Count-aware accepts permuted root: `{search['count_aware_accepts_permuted_root']}`",
        f"- Canonical-index accepts canonical root: `{search['canonical_index_canonical']['ok']}`",
        f"- Canonical-index rejects permuted root: `{search['canonical_index_rejects_permuted_root']}`",
        f"- Canonical-index rejects missing bound: `{search['canonical_index_rejects_missing_bound']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Root-Malleability Countermodel",
        "",
        "```json",
        json.dumps(
            {
                "count_aware_permuted": search["count_aware_permuted"],
                "canonical_index_permuted": search["canonical_index_permuted"],
            },
            indent=2,
            sort_keys=True,
        ),
        "```",
        "",
        "## Negative Controls",
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
        print(
            json.dumps(
                {"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}
            )
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
