#!/usr/bin/env python3
"""Check a bounded two-sided equality certificate for AB child frontiers.

This research-only checker turns the one-witness no-extra refuter into a
positive certificate shape: witness coverage is paired with a generated-state
binding, and the verifier checks equality between advertised child states and
the generated image.
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
    / "zenodex_ab_child_frontier_two_sided_equality_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_CHILD_FRONTIER_TWO_SIDED_EQUALITY_CERTIFICATE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_child_frontier_two_sided_equality_packet.v1"
REPORT_SCHEMA = "zenodex.ab_child_frontier_two_sided_equality_report.v1"
SEARCH_SCHEMA = "zenodex/ab_child_frontier_two_sided_equality_search/v1"
SCOPE = "bounded_ab_child_frontier_two_sided_equality_certificate"
AUTHORITY_BOUNDARY = (
    "Research-only certificate-boundary evidence; no settlement, state-root, "
    "production, routing, matching, pool-mutation, or governance authority."
)
EXPECTED_NEGATIVE_CONTROL_COUNT = 8


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


def _witness_rows(child_states: list[dict[str, int]]) -> list[dict[str, Any]]:
    return [
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


def build_two_sided_packet(
    *,
    child_states: list[dict[str, int]] | None = None,
    generated_states: list[dict[str, int]] | None = None,
) -> dict[str, Any]:
    child_states = copy.deepcopy(child_states if child_states is not None else _child_states())
    generated_states = copy.deepcopy(
        generated_states if generated_states is not None else child_states
    )
    witness_rows = _witness_rows(child_states)
    packet = {
        "schema": PACKET_SCHEMA,
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "coverage_witness_bound": True,
        "frontier_equality_bound": True,
        "generated_state_binding_bound": True,
        "child_states": child_states,
        "generated_states": generated_states,
        "witness_rows": witness_rows,
        "child_state_digest": _state_set_digest(child_states),
        "generated_state_digest": _state_set_digest(generated_states),
        "witness_rows_digest": _sha256_json(witness_rows),
    }
    return _with_packet_hash(packet)


def build_coverage_only_packet() -> dict[str, Any]:
    child_states = _child_states()
    witness_rows = _witness_rows(child_states)
    packet = {
        "schema": PACKET_SCHEMA,
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "coverage_witness_bound": True,
        "frontier_equality_bound": False,
        "generated_state_binding_bound": False,
        "child_states": child_states,
        "witness_rows": witness_rows,
        "child_state_digest": _state_set_digest(child_states),
        "witness_rows_digest": _sha256_json(witness_rows),
    }
    return _with_packet_hash(packet)


def two_sided_verify(packet: Mapping[str, Any] | None) -> dict[str, Any]:
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
    if packet.get("frontier_equality_bound") is not True:
        reasons.append("frontier_equality_bound_missing")
    if packet.get("generated_state_binding_bound") is not True:
        reasons.append("generated_state_binding_missing")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")

    child_states = packet.get("child_states", [])
    generated_states = packet.get("generated_states", [])
    witness_rows = packet.get("witness_rows", [])
    try:
        child_keys = {_state_key(row) for row in child_states}
        generated_keys = {_state_key(row) for row in generated_states}
        witness_child_keys = [_state_key(row["child_state"]) for row in witness_rows]
    except (KeyError, TypeError, ValueError):
        return {"ok": False, "reasons": ["packet_state_shape_malformed"]}

    if len(child_keys) != len(child_states):
        reasons.append("duplicate_child_state")
    if len(generated_keys) != len(generated_states):
        reasons.append("duplicate_generated_state")

    seen_witness_keys: set[tuple[int, int]] = set()
    for key in witness_child_keys:
        if key not in child_keys:
            reasons.append("witness_child_not_in_frontier")
        if key in seen_witness_keys:
            reasons.append("duplicate_witness_row")
        seen_witness_keys.add(key)

    missing_witnesses = child_keys - seen_witness_keys
    if missing_witnesses:
        reasons.append("missing_child_state_witness")

    if packet.get("child_state_digest") != _state_set_digest(child_states):
        reasons.append("child_state_digest_mismatch")
    if packet.get("generated_state_digest") != _state_set_digest(generated_states):
        reasons.append("generated_state_digest_mismatch")
    if packet.get("witness_rows_digest") != _sha256_json(witness_rows):
        reasons.append("witness_rows_digest_mismatch")

    missing_generated = child_keys - generated_keys
    extra_generated = generated_keys - child_keys
    if missing_generated:
        reasons.append("generated_frontier_missing_child_state")
    if extra_generated:
        reasons.append("generated_frontier_extra_child_state")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "child_state_count": len(child_keys),
        "generated_state_count": len(generated_keys),
        "witness_count": len(witness_rows),
        "covered_child_state_count": len(child_keys & seen_witness_keys),
        "missing_witness_count": len(missing_witnesses),
        "missing_generated_state_count": len(missing_generated),
        "extra_generated_state_count": len(extra_generated),
        "extra_generated_states": _sorted_state_rows(
            _state(processed_reserve_in, reserve_out)
            for processed_reserve_in, reserve_out in extra_generated
        ),
        "missing_generated_states": _sorted_state_rows(
            _state(processed_reserve_in, reserve_out)
            for processed_reserve_in, reserve_out in missing_generated
        ),
    }


def _negative_controls(packet: Mapping[str, Any]) -> list[dict[str, Any]]:
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    bad_child_digest = copy.deepcopy(packet)
    bad_child_digest["child_state_digest"] = "0" * 64
    controls.append(
        (
            "child_state_digest_mismatch",
            _with_packet_hash(bad_child_digest),
            "child_state_digest_mismatch",
        )
    )

    bad_generated_digest = copy.deepcopy(packet)
    bad_generated_digest["generated_state_digest"] = "0" * 64
    controls.append(
        (
            "generated_state_digest_mismatch",
            _with_packet_hash(bad_generated_digest),
            "generated_state_digest_mismatch",
        )
    )

    missing_generated = copy.deepcopy(packet)
    missing_generated["generated_states"] = missing_generated["generated_states"][:1]
    missing_generated["generated_state_digest"] = _state_set_digest(
        missing_generated["generated_states"]
    )
    controls.append(
        (
            "generated_frontier_missing_child_state",
            _with_packet_hash(missing_generated),
            "generated_frontier_missing_child_state",
        )
    )

    extra_generated = copy.deepcopy(packet)
    extra_generated["generated_states"].append(_hidden_extra_state())
    extra_generated["generated_state_digest"] = _state_set_digest(
        extra_generated["generated_states"]
    )
    controls.append(
        (
            "generated_frontier_extra_child_state",
            _with_packet_hash(extra_generated),
            "generated_frontier_extra_child_state",
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

    missing_equality_bound = copy.deepcopy(packet)
    missing_equality_bound["frontier_equality_bound"] = False
    controls.append(
        (
            "frontier_equality_bound_missing",
            _with_packet_hash(missing_equality_bound),
            "frontier_equality_bound_missing",
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
        result = two_sided_verify(mutated_packet)
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
    hidden_extra_state = _hidden_extra_state()

    baseline_packet = build_two_sided_packet(child_states=child_states)
    extra_world_packet = build_two_sided_packet(
        child_states=child_states,
        generated_states=[*copy.deepcopy(child_states), hidden_extra_state],
    )

    stale_digest_packet = copy.deepcopy(baseline_packet)
    stale_digest_packet["generated_state_digest"] = "0" * 64
    stale_digest_packet = _with_packet_hash(stale_digest_packet)

    coverage_only_packet = build_coverage_only_packet()

    baseline = two_sided_verify(baseline_packet)
    extra_world = two_sided_verify(extra_world_packet)
    stale_digest = two_sided_verify(stale_digest_packet)
    coverage_only = two_sided_verify(coverage_only_packet)
    negative_controls = _negative_controls(baseline_packet)

    equality_certificate_valid = bool(
        baseline["ok"]
        and not extra_world["ok"]
        and "generated_frontier_extra_child_state" in extra_world["reasons"]
        and not stale_digest["ok"]
        and "generated_state_digest_mismatch" in stale_digest["reasons"]
        and not coverage_only["ok"]
        and "generated_state_binding_missing" in coverage_only["reasons"]
    )

    return {
        "schema": SEARCH_SCHEMA,
        "packet_hash": baseline_packet["packet_hash"],
        "child_state_digest": baseline_packet["child_state_digest"],
        "generated_state_digest": baseline_packet["generated_state_digest"],
        "witness_rows_digest": baseline_packet["witness_rows_digest"],
        "child_state_count": baseline["child_state_count"],
        "generated_state_count": baseline["generated_state_count"],
        "witness_count": baseline["witness_count"],
        "hidden_extra_state": hidden_extra_state,
        "baseline": baseline,
        "extra_world": extra_world,
        "stale_digest": stale_digest,
        "coverage_only": coverage_only,
        "baseline_ok": bool(baseline["ok"]),
        "extra_world_rejected": not extra_world["ok"],
        "stale_digest_rejected": not stale_digest["ok"],
        "coverage_only_rejected": not coverage_only["ok"],
        "equality_certificate_valid": equality_certificate_valid,
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(
            1 for control in negative_controls if control["accepted"]
        ),
        "negative_controls": negative_controls,
        "reason_classes": sorted(
            {
                reason
                for result in [extra_world, stale_digest, coverage_only]
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
        search["equality_certificate_valid"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded two-sided child-frontier certificate pairs one-witness "
            "coverage with generated-state binding and rejects the hidden-extra "
            "countermodel that coverage-only verification accepted."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-TWO-SIDED-EQUALITY-CERTIFICATE-20260629",
            "mechanism_change": (
                "Add generated-image binding to one-witness child-frontier packets "
                "so the verifier checks child_states == generated_states."
            ),
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+rejects hidden extra generated states in bounded model",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+one extra digest and generated-state set check",
                "determinism_simplicity": "+explicit equality obligation",
            },
            "null_hypothesis": (
                "A generated-state digest plus witness coverage can distinguish "
                "the bounded hidden-extra world from the baseline world."
            ),
            "falsification_recipe": (
                "Mutate generated states, state digests, witness rows, equality "
                "rails, packet hashes, and authority rails; any accepted negative "
                "control falsifies the certificate boundary."
            ),
            "support_recipe": (
                "Verify the baseline packet, reject the hidden-extra packet, reject "
                "coverage-only packets, and assert zero accepted negative controls."
            ),
            "formal_obligations": (
                "A production-grade theorem would need to prove that the generated "
                "state set is the complete transition image for the scoped domain."
            ),
            "risk_modes": [
                "generated-state digest not recomputed",
                "coverage witness overclaimed as equality",
                "hidden generated state",
                "authority leakage",
                "stale packet hash",
            ],
            "status": "supported_bounded",
        },
        "design_recommendation": [
            "Use coverage_witnesses + generated_state_digest as a compact bounded certificate shape for no-extra child-frontier claims.",
            "Reject coverage-only packets whenever the claim needs frontier equality rather than coverage.",
            "Keep the certificate research-only until a production verifier or Lean theorem checks complete generated-image construction.",
        ],
        "replay_command": (
            "python3 tools/check_ab_child_frontier_two_sided_equality_certificate_20260629.py"
        ),
        "non_claims": [
            "Scope is limited to a bounded certificate-boundary design; universal claims about all ZenoDEX frontier certificates are excluded.",
            "This artifact does not prove child-frontier generation in Lean.",
            "This artifact does not prove Python-to-Lean refinement.",
            "This artifact does not cover nonzero min_amount_out behavior.",
            "This artifact does not define canonical tie order or production verifier framing.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    lines = [
        "# ZenoDEX AB Two-Sided Child-Frontier Equality Certificate - 2026-06-29",
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
        "coverage_witnesses + generated_state_digest + child_state_digest -> bounded frontier equality check",
        "```",
        "",
        "The verifier accepts only when every advertised child state has a witness and the generated-state set equals the advertised child-state set.",
        "",
        "## Replay Result",
        "",
        f"- Packet hash: `{search['packet_hash']}`",
        f"- Child-state digest: `{search['child_state_digest']}`",
        f"- Generated-state digest: `{search['generated_state_digest']}`",
        f"- Witness rows digest: `{search['witness_rows_digest']}`",
        f"- Child states: `{search['child_state_count']}`",
        f"- Generated states: `{search['generated_state_count']}`",
        f"- Witness rows: `{search['witness_count']}`",
        f"- Baseline accepted: `{search['baseline_ok']}`",
        f"- Extra-world rejected: `{search['extra_world_rejected']}`",
        f"- Stale digest rejected: `{search['stale_digest_rejected']}`",
        f"- Coverage-only rejected: `{search['coverage_only_rejected']}`",
        f"- Equality certificate valid: `{search['equality_certificate_valid']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Hidden Extra Rejection",
        "",
        "```json",
        json.dumps(search["extra_world"], indent=2, sort_keys=True),
        "```",
        "",
        "## Coverage-Only Rejection",
        "",
        "```json",
        json.dumps(search["coverage_only"], indent=2, sort_keys=True),
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
