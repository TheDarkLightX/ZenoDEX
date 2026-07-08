#!/usr/bin/env python3
"""Check count-aware Merkle commitments for AB child-frontier equality.

This research-only checker refines the two-sided equality certificate. A naive
Merkle membership verifier can accept proofs from a hidden-extra generated image
when the packet lies about the generated-state count. A count-aware verifier
binds proof shape to the claimed count and rejects that replay.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_child_frontier_count_aware_merkle_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_COUNT_AWARE_MERKLE_CERTIFICATE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_child_frontier_count_aware_merkle_packet.v1"
REPORT_SCHEMA = "zenodex.ab_child_frontier_count_aware_merkle_report.v1"
SEARCH_SCHEMA = "zenodex/ab_child_frontier_count_aware_merkle_search/v1"
SCOPE = "bounded_ab_child_frontier_count_aware_merkle_certificate"
AUTHORITY_BOUNDARY = (
    "Research-only certificate-boundary evidence; no settlement, state-root, "
    "production, routing, matching, pool-mutation, or governance authority."
)
LEAF_SCHEMA = "zenodex.ab_child_frontier_merkle_leaf.v1"
NODE_SCHEMA = "zenodex.ab_child_frontier_merkle_node.v1"
EXPECTED_NEGATIVE_CONTROL_COUNT = 10


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
        return {key: _strip_timing(value) for key, value in payload.items() if key != "elapsed_ms"}
    if isinstance(payload, list):
        return [_strip_timing(value) for value in payload]
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


def _state_set_digest(states: Iterable[Mapping[str, Any]]) -> str:
    return _sha256_json(_sorted_state_rows(states))


def _child_states() -> list[dict[str, int]]:
    return [_state(100, 9900), _state(140, 9861)]


def _hidden_extra_state() -> dict[str, int]:
    return _state(170, 9830)


def _witness_rows(child_states: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "child_state": dict(child_states[0]),
            "parent_state": _state(0, 10000),
            "step_id": "swap_a",
        },
        {
            "child_state": dict(child_states[1]),
            "parent_state": _state(100, 9900),
            "step_id": "swap_b",
        },
    ]


def _leaf_hash(state: Mapping[str, Any]) -> str:
    return _sha256_json({"schema": LEAF_SCHEMA, "state": _state(*_state_key(state))})


def _node_hash(left_hash: str, right_hash: str) -> str:
    return _sha256_json(
        {"schema": NODE_SCHEMA, "left_hash": left_hash, "right_hash": right_hash}
    )


def _canonical_leaf_rows(
    states: Sequence[Mapping[str, Any]],
) -> tuple[list[dict[str, int]], list[str]]:
    state_rows = _sorted_state_rows(states)
    return state_rows, [_leaf_hash(state) for state in state_rows]


def _merkle_levels(leaf_hashes: Sequence[str]) -> list[list[str]]:
    if not leaf_hashes:
        return [[_sha256_json({"schema": NODE_SCHEMA, "empty": True})]]
    levels: list[list[str]] = [list(leaf_hashes)]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        next_level: list[str] = []
        for index in range(0, len(previous), 2):
            left_hash = previous[index]
            right_hash = previous[index + 1] if index + 1 < len(previous) else left_hash
            next_level.append(_node_hash(left_hash, right_hash))
        levels.append(next_level)
    return levels


def _merkle_root(states: Sequence[Mapping[str, Any]]) -> str:
    _, leaf_hashes = _canonical_leaf_rows(states)
    return _merkle_levels(leaf_hashes)[-1][0]


def _expected_sides(leaf_index: int, leaf_count: int) -> list[str] | None:
    if leaf_count <= 0 or leaf_index < 0 or leaf_index >= leaf_count:
        return None
    index = leaf_index
    count = leaf_count
    sides: list[str] = []
    while count > 1:
        sides.append("right" if index % 2 == 0 else "left")
        index //= 2
        count = (count + 1) // 2
    return sides


def _membership_proof(
    generated_states: Sequence[Mapping[str, Any]],
    state: Mapping[str, Any],
) -> dict[str, Any]:
    state_rows, leaf_hashes = _canonical_leaf_rows(generated_states)
    state_key = _state_key(state)
    index_by_key = {_state_key(row): index for index, row in enumerate(state_rows)}
    if state_key not in index_by_key:
        return {"child_state": dict(state), "leaf_index": None, "proof": []}

    leaf_index = index_by_key[state_key]
    levels = _merkle_levels(leaf_hashes)
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


def _verify_proof_naive(
    state: Mapping[str, Any],
    proof: Sequence[Mapping[str, Any]],
    expected_root_hash: str,
) -> bool:
    current_hash = _leaf_hash(state)
    for step in proof:
        side = step.get("side")
        sibling_hash = step.get("hash")
        if side == "right" and isinstance(sibling_hash, str):
            current_hash = _node_hash(current_hash, sibling_hash)
        elif side == "left" and isinstance(sibling_hash, str):
            current_hash = _node_hash(sibling_hash, current_hash)
        else:
            return False
    return current_hash == expected_root_hash


def _verify_proof_count_aware(
    state: Mapping[str, Any],
    *,
    leaf_index: Any,
    leaf_count: int,
    proof: Sequence[Mapping[str, Any]],
    expected_root_hash: str,
) -> tuple[bool, str | None]:
    if not isinstance(leaf_index, int):
        return False, "membership_leaf_index_malformed"
    expected_sides = _expected_sides(leaf_index, leaf_count)
    if expected_sides is None:
        return False, "membership_leaf_index_out_of_range"
    actual_sides = [step.get("side") for step in proof]
    if actual_sides != expected_sides:
        return False, "membership_proof_shape_mismatch"
    if not _verify_proof_naive(state, proof, expected_root_hash):
        return False, "membership_proof_hash_mismatch"
    return True, None


def build_merkle_packet(
    *,
    child_states: list[dict[str, int]] | None = None,
    generated_states: list[dict[str, int]] | None = None,
    claimed_generated_count: int | None = None,
    count_aware_membership_bound: bool = True,
) -> dict[str, Any]:
    child_states = copy.deepcopy(child_states if child_states is not None else _child_states())
    generated_states = copy.deepcopy(
        generated_states if generated_states is not None else child_states
    )
    generated_state_count = (
        len(_sorted_state_rows(generated_states))
        if claimed_generated_count is None
        else int(claimed_generated_count)
    )
    membership_rows = [
        _membership_proof(generated_states, child_state) for child_state in child_states
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
        "count_aware_membership_bound": bool(count_aware_membership_bound),
        "child_states": child_states,
        "generated_state_count": generated_state_count,
        "generated_state_root": _merkle_root(generated_states),
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


def verify_naive_membership(packet: Mapping[str, Any] | None) -> dict[str, Any]:
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

    seen_membership_keys: set[tuple[int, int]] = set()
    invalid_count = 0
    for row in membership_rows:
        try:
            child_state = row["child_state"]
            key = _state_key(child_state)
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


def verify_count_aware_membership(packet: Mapping[str, Any] | None) -> dict[str, Any]:
    if packet is None:
        return {"ok": False, "reasons": ["packet_missing"]}
    reasons = _shared_packet_reasons(packet)
    if packet.get("count_aware_membership_bound") is not True:
        reasons.append("count_aware_membership_bound_missing")
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

    seen_membership_keys: set[tuple[int, int]] = set()
    invalid_count = 0
    for row in membership_rows:
        try:
            child_state = row["child_state"]
            key = _state_key(child_state)
            proof = row["proof"]
            leaf_index = row["leaf_index"]
        except (KeyError, TypeError, ValueError):
            reasons.append("membership_row_shape_malformed")
            invalid_count += 1
            continue
        if key not in child_keys:
            reasons.append("membership_child_not_in_frontier")
        if key in seen_membership_keys:
            reasons.append("duplicate_membership_proof")
        seen_membership_keys.add(key)
        if isinstance(generated_root, str):
            ok, reason = _verify_proof_count_aware(
                child_state,
                leaf_index=leaf_index,
                leaf_count=generated_count,
                proof=proof,
                expected_root_hash=generated_root,
            )
            if not ok and reason is not None:
                reasons.append(reason)
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

    bad_count = copy.deepcopy(packet)
    bad_count["generated_state_count"] = 3
    controls.append(
        (
            "generated_state_count_mismatch",
            _with_packet_hash(bad_count),
            "generated_state_count_mismatch",
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

    duplicate_membership = copy.deepcopy(packet)
    duplicate_membership["membership_rows"].append(
        copy.deepcopy(duplicate_membership["membership_rows"][0])
    )
    duplicate_membership["membership_rows_digest"] = _sha256_json(
        duplicate_membership["membership_rows"]
    )
    controls.append(
        (
            "duplicate_membership_proof",
            _with_packet_hash(duplicate_membership),
            "duplicate_membership_proof",
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

    missing_count_bound = copy.deepcopy(packet)
    missing_count_bound["generated_count_bound"] = False
    controls.append(
        (
            "generated_count_bound_missing",
            _with_packet_hash(missing_count_bound),
            "generated_count_bound_missing",
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
        result = verify_count_aware_membership(mutated_packet)
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
    extra_generated_states = [*copy.deepcopy(child_states), _hidden_extra_state()]

    baseline_packet = build_merkle_packet(child_states=child_states)
    honest_extra_packet = build_merkle_packet(
        child_states=child_states,
        generated_states=extra_generated_states,
    )
    lying_count_packet = build_merkle_packet(
        child_states=child_states,
        generated_states=extra_generated_states,
        claimed_generated_count=len(child_states),
    )
    coverage_only_packet = build_merkle_packet(
        child_states=child_states,
        count_aware_membership_bound=False,
    )
    coverage_only_packet.pop("generated_state_root")
    coverage_only_packet.pop("membership_rows")
    coverage_only_packet.pop("membership_rows_digest")
    coverage_only_packet = _with_packet_hash(coverage_only_packet)

    naive_baseline = verify_naive_membership(baseline_packet)
    naive_honest_extra = verify_naive_membership(honest_extra_packet)
    naive_lying_count = verify_naive_membership(lying_count_packet)
    count_aware_baseline = verify_count_aware_membership(baseline_packet)
    count_aware_honest_extra = verify_count_aware_membership(honest_extra_packet)
    count_aware_lying_count = verify_count_aware_membership(lying_count_packet)
    count_aware_coverage_only = verify_count_aware_membership(coverage_only_packet)
    negative_controls = _negative_controls(baseline_packet)

    naive_countermodel_valid = bool(
        naive_baseline["ok"]
        and not naive_honest_extra["ok"]
        and naive_lying_count["ok"]
        and count_aware_baseline["ok"]
        and not count_aware_lying_count["ok"]
        and "membership_proof_shape_mismatch" in count_aware_lying_count["reasons"]
    )

    return {
        "schema": SEARCH_SCHEMA,
        "baseline_packet_hash": baseline_packet["packet_hash"],
        "baseline_generated_state_root": baseline_packet["generated_state_root"],
        "lying_count_generated_state_root": lying_count_packet["generated_state_root"],
        "child_state_digest": baseline_packet["child_state_digest"],
        "membership_rows_digest": baseline_packet["membership_rows_digest"],
        "witness_rows_digest": baseline_packet["witness_rows_digest"],
        "child_state_count": len(child_states),
        "hidden_extra_state": _hidden_extra_state(),
        "naive_baseline": naive_baseline,
        "naive_honest_extra": naive_honest_extra,
        "naive_lying_count": naive_lying_count,
        "count_aware_baseline": count_aware_baseline,
        "count_aware_honest_extra": count_aware_honest_extra,
        "count_aware_lying_count": count_aware_lying_count,
        "count_aware_coverage_only": count_aware_coverage_only,
        "naive_countermodel_valid": naive_countermodel_valid,
        "count_aware_rejects_lying_count": not count_aware_lying_count["ok"],
        "count_aware_rejects_honest_extra": not count_aware_honest_extra["ok"],
        "coverage_only_rejected": not count_aware_coverage_only["ok"],
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(
            1 for control in negative_controls if control["accepted"]
        ),
        "negative_controls": negative_controls,
        "reason_classes": sorted(
            {
                reason
                for result in [
                    naive_honest_extra,
                    count_aware_honest_extra,
                    count_aware_lying_count,
                    count_aware_coverage_only,
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
        search["naive_countermodel_valid"]
        and search["count_aware_rejects_lying_count"]
        and search["count_aware_rejects_honest_extra"]
        and search["coverage_only_rejected"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded count-aware Merkle verifier rejects a hidden-extra replay "
            "that a naive membership verifier accepts when the packet lies about "
            "the generated-state count."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-COUNT-AWARE-MERKLE-CERTIFICATE-20260629",
            "mechanism_change": (
                "Bind Merkle membership proof shape to generated_state_count before "
                "using root membership as a no-extra child-frontier certificate."
            ),
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+rejects false-count hidden-extra Merkle replay",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+membership proof shape checks",
                "determinism_simplicity": "+explicit count-aware root contract",
            },
            "null_hypothesis": (
                "A generated-state root plus naive membership proofs is sufficient "
                "to support bounded no-extra child-frontier equality."
            ),
            "falsification_recipe": (
                "Build a root over three generated states, claim count two, and "
                "supply valid naive proofs for the two advertised child states."
            ),
            "support_recipe": (
                "Require the count-aware verifier to accept baseline, reject the "
                "false-count replay, reject honest extra count, reject coverage-only "
                "packets, and reject all negative controls."
            ),
            "formal_obligations": (
                "A formal version should prove that count-aware proof shape plus "
                "unique child states and generated_count equality imply no hidden "
                "extra leaves for the committed Merkle tree."
            ),
            "risk_modes": [
                "naive membership verification ignores leaf_count",
                "false generated count",
                "hidden generated state",
                "stale root",
                "authority leakage",
            ],
            "status": "supported_bounded",
        },
        "design_recommendation": [
            "Use count-aware Merkle membership verification for generated-image roots.",
            "Reject packets where membership proof shape does not match the claimed generated_state_count.",
            "Treat root-only membership as insufficient for no-extra claims unless count-aware proof shape is checked.",
        ],
        "replay_command": (
            "python3 tools/check_ab_child_frontier_count_aware_merkle_certificate_20260629.py"
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
        "# ZenoDEX AB Count-Aware Merkle Certificate - 2026-06-29",
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
        "generated_state_root + generated_state_count + count-aware membership proofs",
        "```",
        "",
        "The verifier checks proof shape against the claimed generated-state count before accepting membership.",
        "",
        "## Replay Result",
        "",
        f"- Baseline packet hash: `{search['baseline_packet_hash']}`",
        f"- Baseline generated-state root: `{search['baseline_generated_state_root']}`",
        f"- Lying-count generated-state root: `{search['lying_count_generated_state_root']}`",
        f"- Child-state digest: `{search['child_state_digest']}`",
        f"- Membership rows digest: `{search['membership_rows_digest']}`",
        f"- Witness rows digest: `{search['witness_rows_digest']}`",
        f"- Child states: `{search['child_state_count']}`",
        f"- Naive baseline accepted: `{search['naive_baseline']['ok']}`",
        f"- Naive honest-extra rejected: `{not search['naive_honest_extra']['ok']}`",
        f"- Naive lying-count accepted: `{search['naive_lying_count']['ok']}`",
        f"- Count-aware baseline accepted: `{search['count_aware_baseline']['ok']}`",
        f"- Count-aware lying-count rejected: `{search['count_aware_rejects_lying_count']}`",
        f"- Count-aware honest-extra rejected: `{search['count_aware_rejects_honest_extra']}`",
        f"- Coverage-only rejected: `{search['coverage_only_rejected']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Naive Countermodel",
        "",
        "```json",
        json.dumps(
            {
                "hidden_extra_state": search["hidden_extra_state"],
                "naive_lying_count": search["naive_lying_count"],
                "count_aware_lying_count": search["count_aware_lying_count"],
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
