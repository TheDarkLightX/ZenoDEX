#!/usr/bin/env python3
from __future__ import annotations

import argparse
import glob
import json
import time
from collections import Counter
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]

try:
    from tools.krr_reasoner_engine import advise_candidate_krr, load_krr_kb
except Exception:
    try:
        from krr_reasoner_engine import advise_candidate_krr, load_krr_kb
    except Exception:
        advise_candidate_krr = None
        load_krr_kb = None


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_token(text: str, max_len: int = 72) -> str:
    out = []
    for ch in str(text):
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    token = "".join(out).strip("._").lower()
    if not token:
        token = "x"
    return token[:max_len]


def _uniq(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        key = str(item).strip()
        if not key or key in seen:
            continue
        seen.add(key)
        out.append(key)
    return out


# Bridge from ZAG operator IDs to concrete ZenoDEX check hooks and transforms.
OPERATOR_BRIDGE: dict[str, dict[str, Any]] = {
    "op_schema_switch_dc": {
        "representation_shift_used": "reduce",
        "check": "batch_greedy_invariants",
        "checks": [
            "batch_greedy_invariants",
            "route_exact_out_2hop_value",
            "batch_clearing_no_gap",
        ],
        "expected_metric_delta": [2, 1, 1, -1, 1],
        "mechanism_template": "Apply divide-and-conquer settlement decomposition with replayable merge invariants.",
        "null_template": "Decomposition introduces measurable objective gaps under bounded replay.",
    },
    "op_symmetry_quotient": {
        "representation_shift_used": "reduce",
        "check": "settlement_normal_form",
        "checks": [
            "settlement_normal_form",
            "state_root_determinism",
        ],
        "expected_metric_delta": [2, 0, 0, 0, 3],
        "mechanism_template": "Detect symmetries and quotient/canonicalize to reduce nondeterminism and search cost (normal-form and idempotence obligations).",
        "null_template": "Symmetry quotient/canonicalization is not semantics-preserving or introduces nondeterminism.",
    },
    "op_dualize_constraints": {
        "representation_shift_used": "relax",
        "check": "route_exact_out_2hop_value",
        "checks": [
            "route_exact_out_2hop_value",
            "split_routing_no_gap",
        ],
        "expected_metric_delta": [1, 2, 2, 0, 1],
        "mechanism_template": "Use dualization (constraints/shadow prices) to guide route or split selection, with a refinement certificate that the chosen action is optimal within a bounded candidate set.",
        "null_template": "Dual-guided selection does not improve route value or causes bounded-optimality gaps.",
    },
    "op_lift_project": {
        "representation_shift_used": "relax",
        "check": "split_routing_no_gap",
        "checks": [
            "split_routing_no_gap",
            "route_exact_out_2hop_value",
        ],
        "expected_metric_delta": [1, 1, 2, 1, 1],
        "mechanism_template": "Lift discrete optimization to a continuous/relaxed proxy, then project with deterministic multi-center refinement and bounded oracle checks.",
        "null_template": "Lift+project proxy misses optimal solutions (bounded gap exists) or hurts determinism.",
    },
    "op_invariant_mining_ice": {
        "representation_shift_used": "restrict",
        "check": "batch_greedy_invariants",
        "checks": [
            "batch_greedy_invariants",
            "esso_verify::src/kernels/dex/spec_quality_assessment_v1.yaml",
        ],
        "expected_metric_delta": [3, 0, 1, -1, 2],
        "mechanism_template": "Mine inductive invariants via ICE/CEGIS and enforce them fail-closed as guards/certificates on critical transitions.",
        "null_template": "Invariant mining does not produce a stable inductive guard under deterministic replay.",
    },
    "op_total_order_canonicalization": {
        "representation_shift_used": "restrict",
        "check": "settlement_normal_form",
        "checks": [
            "settlement_normal_form",
            "state_root_determinism",
        ],
        "expected_metric_delta": [2, 0, 1, 0, 3],
        "mechanism_template": "Canonicalize all choice points by selecting the unique winner under a total key (objective + tie-break) to harden determinism.",
        "null_template": "Total-order canonicalization is inconsistent with verifier semantics or is not replay-stable.",
    },
    "op_data_structure_array": {
        "representation_shift_used": "reduce",
        "check": "route_exact_out_2hop_value",
        "expected_metric_delta": [1, 1, 2, -1, 1],
        "mechanism_template": "Switch routing hot path to indexed/array representation with deterministic tie-break key.",
        "null_template": "Array/indexed representation does not improve route value without regressions.",
    },
    "op_invariant_chunking": {
        "representation_shift_used": "restrict",
        "check": "batch_greedy_invariants",
        "expected_metric_delta": [2, 0, 1, -1, 2],
        "mechanism_template": "Chunk settlement into bounded windows while preserving global conservation invariants.",
        "null_template": "Chunking violates or weakens bounded invariant checks.",
    },
    "op_algebraic_rewrite": {
        "representation_shift_used": "equiv",
        "check": "settlement_normal_form",
        "expected_metric_delta": [2, 0, 1, -1, 2],
        "mechanism_template": "Canonicalize settlement via algebraic rewrite to a deterministic normal form.",
        "null_template": "Rewrite canonicalization is not semantics-preserving under replay.",
    },
    "op_branch_reduction": {
        "representation_shift_used": "restrict",
        "check": "state_root_determinism",
        "expected_metric_delta": [2, 0, 1, -1, 2],
        "mechanism_template": "Reduce branch fan-out in deterministic agent transitions and state updates.",
        "null_template": "Branch reduction does not improve determinism or reproducibility.",
    },
    "op_partition_reduce": {
        "representation_shift_used": "reduce",
        "check": "route_exact_out_2hop_value",
        "checks": [
            "route_exact_out_2hop_value",
            "batch_greedy_invariants",
            "split_routing_no_gap",
        ],
        "expected_metric_delta": [1, 1, 2, -1, 1],
        "mechanism_template": "Partition intents by risk/liquidity class and reduce independently with verified recomposition.",
        "null_template": "Partition-then-reduce introduces routing or clearing quality gaps.",
    },
    "op_marginal_contribution_insertion": {
        "representation_shift_used": "restrict",
        "check": "batch_mci_vs_bruteforce",
        "checks": [
            "batch_clearing_no_gap",
            "batch_mci_vs_bruteforce",
            "batch_mci_vs_greedy",
        ],
        "expected_metric_delta": [3, 1, 2, 0, 2],
        "mechanism_template": "Replace brute-force batch ordering with marginal-contribution insertion (O(n^2 log n)). At each step, insert the swap whose marginal (A,B) improvement is maximal at the best position, with 2-opt refinement.",
        "null_template": "MCI gap exceeds 200bps vs optimal for N<=12, or greedy_ab dominates MCI for N>12.",
    },
    "op_golden_section_split": {
        "representation_shift_used": "equiv",
        "check": "dgstr_exact_match",
        "checks": [
            "split_routing_no_gap",
            "dgstr_exact_match",
            "dgstr_eval_count",
        ],
        "expected_metric_delta": [2, 2, 3, 0, 1],
        "mechanism_template": "Exploit CPMM quasi-concavity with discrete golden-section ternary refinement (DGSTR) to find optimal 2-pool split in O(log^2 D) evaluations instead of O(window * grid).",
        "null_template": "DGSTR gap exceeds 1 unit vs brute-force, or eval count exceeds O(log^2 D) budget.",
    },
    "op_adaptive_slippage": {
        "representation_shift_used": "restrict",
        "check": "slippage_never_reverts",
        "checks": [
            "slippage_never_reverts",
            "slippage_tightness",
            "slippage_revert_rate",
        ],
        "expected_metric_delta": [1, 0, 1, 0, 3],
        "mechanism_template": "Compute provably tight slippage bound from CPMM price impact, volatility tier, and settlement time. Reduces revert rate >50% vs static tiers while staying within 1.5x of theoretical minimum.",
        "null_template": "Adaptive slippage revert reduction <50% or tightness ratio exceeds 1.5x minimum.",
    },
    "op_graph_multihop_router": {
        "representation_shift_used": "reduce",
        "check": "graph_router_dominance",
        "checks": [
            "route_exact_out_2hop_value",
            "graph_router_dominance",
            "graph_router_conservation",
        ],
        "expected_metric_delta": [2, 2, 2, -1, 1],
        "mechanism_template": "Dijkstra-style graph router with CPMM-aware negative-log edge weights, hop limit of 4, and pool-reuse prevention. 3-hop routes improve output >5% for >20% of fragmented-liquidity scenarios.",
        "null_template": "2-hop always beats graph router, or 3-hop improvement rate <20% of fragmented scenarios.",
    },
    "op_predictive_liquidation": {
        "representation_shift_used": "restrict",
        "check": "predictive_liq_never_optimistic",
        "checks": [
            "predictive_liq_never_optimistic",
            "predictive_liq_tightness",
            "lean_proof::PredictiveLiqSafety",
        ],
        "expected_metric_delta": [3, 0, 1, 0, 3],
        "mechanism_template": "O(1) predictive liquidation prevention computing epochs_to_liquidation from convex margin structure and ESSO oracle move bounds. Never optimistic: if predicts N epochs, account survives at least N epochs under worst-case.",
        "null_template": "Predictive bound is optimistic (actual liquidation before predicted epoch) or Lean proof fails.",
    },
    "op_funding_bb_verifier": {
        "representation_shift_used": "restrict",
        "check": "funding_bb_checksum_bounds",
        "checks": [
            "funding_bb_checksum_bounds",
            "funding_bb_delta_range",
            "lean_proof::FundingBBVerifier",
        ],
        "expected_metric_delta": [3, 0, 1, 0, 3],
        "mechanism_template": "O(1) amortized funding budget-balance verifier maintaining a running checksum in [-N, 0] (from the Z gap theorem). Detects BB violations in constant time per funding application.",
        "null_template": "Checksum exits [-N, 0] bounds or Lean proof of checksum_bounded fails.",
    },
    "op_oracle_anomaly_detection": {
        "representation_shift_used": "restrict",
        "check": "oracle_pump_detection",
        "checks": [
            "oracle_pump_detection",
            "oracle_oscillation_detection",
            "oracle_staleness_detection",
        ],
        "expected_metric_delta": [2, 0, 1, 0, 2],
        "mechanism_template": "Temporal anomaly detection for oracle manipulation: pump sequences (consecutive near-max moves), oscillation extraction (alternating near-max), and staleness exploitation (clustering near deadline). Detection rate >95%, FPR <5%.",
        "null_template": "Detection rate <95% or false positive rate >5% for any of the three anomaly patterns.",
    },
    "op_keeper_liveness": {
        "representation_shift_used": "equiv",
        "check": "ltlf_scheduler_goal_family",
        "checks": [
            "ltlf_scheduler_goal_family",
            "pytest_pass::tests/formal/test_perp_epoch_scheduler_ltlf.py",
        ],
        "expected_metric_delta": [3, 0, 1, 0, 3],
        "mechanism_template": "Stateless keeper function with deterministic phase-to-action mapping. Multi-property LTLf synthesis must realize the required scheduler goals jointly (not just individually).",
        "null_template": "Required scheduler liveness goals are not jointly realizable under bounded LTLf synthesis.",
    },
}

SCHEMA_TO_OPERATOR_ID: dict[str, str] = {
    "algebraic_rewrite": "op_algebraic_rewrite",
    "divide_and_conquer": "op_schema_switch_dc",
    "bit_level_branchless": "op_branch_reduction",
    "search_prune": "op_partition_reduce",
}

INTENT_TO_OPERATOR_ID: dict[str, str] = {
    "array_fold": "op_data_structure_array",
    "array_index": "op_data_structure_array",
    "tailrec": "op_data_structure_array",
    "chunked_foldl": "op_invariant_chunking",
    "partition_even_odd": "op_partition_reduce",
    "filter_split": "op_partition_reduce",
    "divide_and_conquer": "op_schema_switch_dc",
    "foldr": "op_algebraic_rewrite",
    "foldl": "op_algebraic_rewrite",
    "reverse_fold": "op_algebraic_rewrite",
}

OPERATOR_DESCRIPTIONS: dict[str, str] = {
    "op_schema_switch_dc": "Switch from linear fold to divide-and-conquer reduction.",
    "op_symmetry_quotient": "Detect symmetries and quotient/canonicalize to reduce state-space and nondeterminism.",
    "op_dualize_constraints": "Dualize objective/constraints to expose shadow prices/bounds; refine deterministically.",
    "op_lift_project": "Lift to a proxy model then project with bounded discrete refinement.",
    "op_invariant_mining_ice": "Mine inductive invariants (ICE/CEGIS) and embed proof-carrying guards.",
    "op_total_order_canonicalization": "Define a total key and canonical winner selection to harden determinism.",
    "op_data_structure_array": "Switch core data structure from list traversal to array indexing/fold.",
    "op_invariant_chunking": "Introduce chunked accumulation invariant.",
    "op_algebraic_rewrite": "Apply algebraic rewrite pipeline before reduction.",
    "op_branch_reduction": "Reduce branch frequency with accumulator or branchless style updates.",
    "op_partition_reduce": "Partition input into semantic buckets then reduce independently.",
    "op_marginal_contribution_insertion": "Replace brute-force batch ordering with marginal-contribution insertion (O(n^2 log n)).",
    "op_golden_section_split": "Exploit CPMM quasi-concavity with discrete golden-section ternary refinement for split routing.",
    "op_adaptive_slippage": "Compute provably tight slippage bound from CPMM price impact and volatility tier.",
    "op_graph_multihop_router": "Dijkstra-style graph router with CPMM-aware edge weights, up to 4 hops.",
    "op_predictive_liquidation": "O(1) predictive liquidation prevention from convex margin structure and oracle move bounds.",
    "op_funding_bb_verifier": "O(1) amortized funding budget-balance verifier maintaining checksum in [-N, 0].",
    "op_oracle_anomaly_detection": "Temporal anomaly detection for oracle manipulation (pump, oscillation, staleness).",
    "op_keeper_liveness": "Stateless keeper function with provable deadlock-freedom and 3-action settlement.",
}


def _parse_float(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except Exception:
        return float(default)


def _status_weight(status: str) -> float:
    s = str(status or "").strip().upper()
    if s == "PROVED":
        return 1.0
    if s == "TESTED_ONLY":
        return 0.72
    if s in {"INCONCLUSIVE", "UNKNOWN"}:
        return 0.45
    return 0.35


def _expand_globs(patterns: list[str]) -> list[Path]:
    out: list[Path] = []
    seen: set[str] = set()
    for raw in patterns:
        pat = str(raw or "").strip()
        if not pat:
            continue
        glob_pat = pat if Path(pat).is_absolute() else str(ROOT / pat)
        for match in glob.glob(glob_pat, recursive=True):
            p = Path(match)
            if not p.is_file():
                continue
            key = str(p.resolve())
            if key in seen:
                continue
            seen.add(key)
            out.append(p)
    return sorted(out)


def _signature_key(*, operator_id: str, check: str, schema: str, intent_op: str, semantic_sig: str = "") -> str:
    return "|".join(
        [
            _safe_token(operator_id, max_len=64),
            _safe_token(check, max_len=64),
            _safe_token(schema, max_len=64),
            _safe_token(intent_op, max_len=64),
            _safe_token(semantic_sig or "", max_len=96),
        ]
    )


def _load_check_history(summary_globs: list[str]) -> dict[str, dict[str, float]]:
    rows = Counter()
    supported = Counter()
    for p in _expand_globs(summary_globs):
        try:
            obj = _read_json(p)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        for row in obj.get("rows", []):
            if not isinstance(row, dict):
                continue
            check = str(row.get("check", "")).strip()
            if not check:
                continue
            rows[check] += 1
            if str(row.get("final_status", "")).strip() == "supported":
                supported[check] += 1
    out: dict[str, dict[str, float]] = {}
    for check, total in rows.items():
        sup = int(supported.get(check, 0))
        out[check] = {
            "total": float(total),
            "supported": float(sup),
            "support_rate": float(sup) / float(total) if total > 0 else 0.0,
        }
    return out


def _load_signature_history(bridge_globs: list[str]) -> Counter[str]:
    out: Counter[str] = Counter()
    for p in _expand_globs(bridge_globs):
        try:
            obj = _read_json(p)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        for h in obj.get("hypotheses", []):
            if not isinstance(h, dict):
                continue
            explicit = str(h.get("bridge_signature", "")).strip()
            if explicit:
                out[explicit] += 1
                continue
            op = str(h.get("operator_id", "")).strip()
            check = str(h.get("support_recipe", "")).strip()
            schema = str(h.get("zag_schema", "")).strip()
            intent = str(h.get("descriptor_intent_op", "")).strip()
            semantic = str(h.get("zag_semantic_signature", "")).strip()
            if not op or not check:
                continue
            out[_signature_key(operator_id=op, check=check, schema=schema, intent_op=intent, semantic_sig=semantic)] += 1
    return out


def _bridge_checks(bridge: dict[str, Any]) -> list[str]:
    out: list[str] = []
    raw = bridge.get("checks")
    if isinstance(raw, list):
        for x in raw:
            check = str(x).strip()
            if check and check not in out:
                out.append(check)
    default_check = str(bridge.get("check", "")).strip()
    if default_check and default_check not in out:
        out.append(default_check)
    return out


def _select_check(
    *,
    bridge: dict[str, Any],
    check_choices_override: list[str] | None,
    history_check_stats: dict[str, dict[str, float]],
    min_check_support_rate: float,
    min_check_history_total: int,
) -> dict[str, Any]:
    choices = _uniq(check_choices_override or _bridge_checks(bridge))
    if not choices:
        return {"check": "", "check_total": 0, "check_rate": None, "signal_ok": True}
    ranked: list[tuple[tuple[int, float, int, int], dict[str, Any]]] = []
    for ix, check in enumerate(choices):
        hist = history_check_stats.get(check, {})
        check_total = int(_parse_float(hist.get("total", 0.0), 0.0))
        check_rate_obj = hist.get("support_rate")
        check_rate = float(check_rate_obj) if isinstance(check_rate_obj, (int, float)) else None
        signal_ok = not (
            check_total >= int(max(0, min_check_history_total))
            and check_rate is not None
            and check_rate < float(min_check_support_rate)
        )
        prior = check_rate if check_rate is not None else 0.5
        confidence = min(1.0, float(max(0, check_total)) / 12.0)
        score = prior + 0.08 * confidence
        ranked.append(
            (
                (
                    int(signal_ok),
                    score,
                    check_total,
                    -ix,  # prefer listed order on ties
                ),
                {
                    "check": check,
                    "check_total": check_total,
                    "check_rate": check_rate,
                    "signal_ok": signal_ok,
                },
            )
        )
    ranked.sort(key=lambda row: row[0], reverse=True)
    return ranked[0][1]


def _effective_min_speedup(*, base_min_speedup: float, check_support_rate: float | None, check_total: int) -> float:
    base = float(base_min_speedup)
    if check_support_rate is None:
        return max(0.75, base)
    confidence = min(1.0, float(max(0, check_total)) / 12.0)
    support_margin = max(0.0, float(check_support_rate) - 0.5)
    relaxed = base - (0.40 * support_margin * confidence)
    return max(0.75, relaxed)


def _selection_score(
    *,
    status: str,
    speedup: float,
    speedup_observed: bool,
    prior_signature_count: int,
    check_support_rate: float | None,
    check_total: int,
    proof_priority: int | None,
    candidate_hypothesis: str,
) -> float:
    status_term = 1.35 * _status_weight(status)
    speedup_term = 0.0
    if speedup_observed:
        speedup_term = min(1.5, max(0.0, speedup - 1.0))
    novelty_term = 0.25 / float(1 + max(0, prior_signature_count))
    history_term = 0.0
    if check_support_rate is not None:
        confidence = min(1.0, float(max(0, check_total)) / 12.0)
        history_term = (float(check_support_rate) - 0.5) * confidence
    priority_term = 0.0
    if isinstance(proof_priority, int):
        # In ZAG manifests lower `priority` is better.
        priority_term = max(0.0, (4 - int(proof_priority)) * 0.04)
    stub_penalty = -0.35 if "stub hypothesis" in candidate_hypothesis.lower() else 0.0
    return status_term + speedup_term + novelty_term + history_term + priority_term + stub_penalty


def _mk_hypothesis(*, cycle: int, idx: int, assignment: dict[str, Any], score_row: dict[str, Any]) -> dict[str, Any]:
    op_id = str(assignment.get("operator_id", ""))
    bridge = OPERATOR_BRIDGE.get(op_id)
    if bridge is None:
        return {}

    cand_id = str(assignment.get("candidate_id", "cand"))
    schema = str(score_row.get("schema", "unknown"))
    status = str(score_row.get("status", "TESTED_ONLY"))
    speedup = str(score_row.get("speedup", "1.000000"))
    semantic_sig = str(
        assignment.get("semantic_signature")
        or score_row.get("semantic_signature")
        or ""
    ).strip()
    operator_desc = str(assignment.get("operator_description", "")).strip()
    op_original = str(assignment.get("_operator_id_original", "")).strip()

    slug = _safe_token(f"{op_id}_{cand_id}")
    hid = f"H_cycle{cycle}_zag_bridge_{idx:03d}_{slug}_v1"
    check = str(assignment.get("_selected_check") or bridge["check"])

    obligations = [
        f"`{check}` must resolve deterministically (no timeout/error)",
        "UNKNOWN/TIMEOUT/ERROR remain inconclusive",
        "Bridge claim must preserve deterministic replay semantics",
    ]
    risks = [
        "Cross-domain transfer from list-sum benchmark can overgeneralize",
        "Local speedup in source domain may not transfer to DEX kernels",
    ]

    mech = (
        f"{bridge['mechanism_template']} "
        f"ZAG evidence: candidate `{cand_id}` (`schema={schema}`, `status={status}`, `speedup={speedup}`). "
        f"Operator note: {operator_desc}"
    )
    if op_original:
        mech = f"{mech} (operator_id_original={op_original})"
    candidate_hypothesis = str(assignment.get("candidate_hypothesis", "")).strip()
    if candidate_hypothesis:
        mech += f" Candidate hypothesis: {candidate_hypothesis}"
    null = (
        f"{bridge['null_template']} "
        f"ZAG transfer signal from `{cand_id}` is spurious for ZenoDEX."
    )

    return {
        "hypothesis_id": hid,
        "mechanism_change": mech,
        "representation_shift_used": str(bridge["representation_shift_used"]),
        "expected_metric_delta": list(bridge["expected_metric_delta"]),
        "null_hypothesis": null,
        "falsification_recipe": check,
        "support_recipe": check,
        "formal_obligations": obligations,
        "risk_modes": risks,
        "status": "proposed",
        "source": "zag_bridge_operator_transfer",
        "operator_id": op_id,
        "zag_candidate_id": cand_id,
        "zag_schema": schema,
        "zag_status": status,
        "zag_speedup": speedup,
        "descriptor_intent_op": str(assignment.get("descriptor_intent_op", "")),
        "candidate_hypothesis": candidate_hypothesis,
        "proposal_schema_version": str(assignment.get("proposal_schema_version", "")),
        "selection_score": round(_parse_float(assignment.get("_selection_score"), 0.0), 6),
        "krr_score_delta": round(_parse_float(assignment.get("_krr_score_delta"), 0.0), 6),
        "krr": assignment.get("_krr_advice", {}) if isinstance(assignment.get("_krr_advice"), dict) else {},
        "history_check_support_rate": assignment.get("_check_support_rate"),
        "history_check_total": int(_parse_float(assignment.get("_check_total"), 0)),
        "bridge_signature": str(assignment.get("_signature", "")),
        "zag_semantic_signature": semantic_sig,
        "timeout_s": 220,
        "category": "algo",
    }


def _median(values: list[float]) -> float:
    vals = sorted(float(x) for x in values)
    if not vals:
        return 0.0
    n = len(vals)
    m = n // 2
    if n % 2 == 1:
        return float(vals[m])
    return 0.5 * float(vals[m - 1] + vals[m])


def _semantic_signature(schema: str, ir: Any, fallback: str = "") -> str:
    explicit = str(fallback or "").strip()
    if explicit:
        return explicit
    ir_obj = ir if isinstance(ir, dict) else {}
    op = str(ir_obj.get("op", "unknown")).strip() or "unknown"
    parts = [str(schema or "unknown").strip() or "unknown", f"op={op}"]
    for key in sorted(ir_obj.keys()):
        if key == "op":
            continue
        value = ir_obj.get(key)
        if isinstance(value, (str, int, float, bool)) or value is None:
            parts.append(f"{key}={value}")
    return "|".join(parts)


def _operator_id_from_schema_intent(*, schema: str, intent_op: str) -> str | None:
    op = INTENT_TO_OPERATOR_ID.get(str(intent_op or "").strip())
    if op:
        return op
    return SCHEMA_TO_OPERATOR_ID.get(str(schema or "").strip())


def _extract_selected_details(manifest: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    details = manifest.get("selected_candidate_details")
    if not isinstance(details, list):
        return [], []
    assignments: list[dict[str, Any]] = []
    scores: list[dict[str, Any]] = []
    for row in details:
        if not isinstance(row, dict):
            continue
        cid = str(row.get("candidate_id", "")).strip()
        if not cid:
            continue
        schema = str(row.get("schema", "unknown")).strip()
        intent = row.get("descriptor_intent")
        intent_op = str(intent.get("op", "")) if isinstance(intent, dict) else ""
        operator_id = _operator_id_from_schema_intent(schema=schema, intent_op=intent_op)
        if operator_id is None:
            continue
        assignments.append(
            {
                "candidate_id": cid,
                "operator_id": operator_id,
                "operator_description": OPERATOR_DESCRIPTIONS.get(operator_id, "Schema/intent transfer from selected candidate details."),
                "descriptor_intent_op": intent_op,
                "candidate_hypothesis": str(row.get("hypothesis", "")).strip(),
                "proposal_schema_version": str(row.get("proposal_schema_version", "")).strip(),
                "semantic_signature": _semantic_signature(
                    schema,
                    row.get("ir"),
                    fallback=str(row.get("semantic_signature", "")),
                ),
                "proof_priority": int(row.get("proof_priority"))
                if isinstance(row.get("proof_priority"), int)
                else None,
            }
        )
        speedup_raw = row.get("speedup")
        speedup = _parse_float(speedup_raw, 1.0)
        speedup_observed = bool(row.get("speedup_observed", speedup_raw is not None))
        scores.append(
            {
                "candidate_id": cid,
                "schema": schema,
                "status": str(row.get("status", "TESTED_ONLY")),
                "semantic_signature": _semantic_signature(
                    schema,
                    row.get("ir"),
                    fallback=str(row.get("semantic_signature", "")),
                ),
                "speedup": f"{speedup:.6f}",
                "speedup_observed": bool(speedup_observed),
            }
        )
    return assignments, scores


def _extract_neuro_assignments(manifest_path: Path, manifest: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    selected = {str(x) for x in manifest.get("selected_candidates", []) if isinstance(x, str)}
    if not selected:
        return [], []

    status_by_id: dict[str, str] = {}
    for row in manifest.get("candidate_statuses", []):
        if not isinstance(row, dict):
            continue
        cid = str(row.get("candidate_id", ""))
        if not cid:
            continue
        st = str(row.get("status", "TESTED_ONLY")).strip()
        status_by_id[cid] = st

    timing_path = manifest_path.parent / "timings_train.json"
    baseline_median = 0.0
    candidate_medians: dict[str, float] = {}
    if timing_path.exists():
        t = _read_json(timing_path)
        if isinstance(t, dict):
            base = t.get("baseline", {})
            if isinstance(base, dict):
                baseline_median = _median(list(base.get("samples_ms", []) or []))
            for row in t.get("candidates", []):
                if not isinstance(row, dict):
                    continue
                cid = str(row.get("id", ""))
                if not cid:
                    continue
                candidate_medians[cid] = _median(list(row.get("samples_ms", []) or []))

    neural_response_path = manifest_path.parent / "neural" / "response.jsonl"
    if not neural_response_path.exists():
        return [], []

    assignments: list[dict[str, Any]] = []
    scores: list[dict[str, Any]] = []
    for line in neural_response_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        cid = str(obj.get("candidate_id", ""))
        if cid not in selected:
            continue
        schema = str(obj.get("schema", "unknown")).strip()
        intent = obj.get("descriptor_intent", {})
        intent_op = str(intent.get("op", "")) if isinstance(intent, dict) else ""
        operator_id = _operator_id_from_schema_intent(schema=schema, intent_op=intent_op)
        if operator_id is None:
            continue
        assignments.append(
            {
                "candidate_id": cid,
                "operator_id": operator_id,
                "operator_description": OPERATOR_DESCRIPTIONS.get(operator_id, "Schema/intent transfer from neuro campaign."),
                "descriptor_intent_op": intent_op,
                "candidate_hypothesis": str(obj.get("hypothesis", "")).strip(),
                "proposal_schema_version": str(obj.get("proposal_schema_version", "")).strip(),
                "semantic_signature": _semantic_signature(
                    schema,
                    obj.get("ir"),
                    fallback=str(obj.get("semantic_signature", "")),
                ),
                "proof_priority": int(obj.get("proof_plan", {}).get("priority", 0))
                if isinstance(obj.get("proof_plan"), dict)
                else None,
            }
        )
        c_med = float(candidate_medians.get(cid, 0.0))
        speedup = 1.0
        speedup_observed = False
        if baseline_median > 0.0 and c_med > 0.0:
            speedup = baseline_median / c_med
            speedup_observed = True
        scores.append(
            {
                "candidate_id": cid,
                "schema": schema,
                "status": status_by_id.get(cid, "TESTED_ONLY"),
                "semantic_signature": _semantic_signature(
                    schema,
                    obj.get("ir"),
                    fallback=str(obj.get("semantic_signature", "")),
                ),
                "speedup": f"{speedup:.6f}",
                "speedup_observed": bool(speedup_observed),
            }
        )
    return assignments, scores


def _build_bridge_pack(
    *,
    cycle: int,
    manifest: dict[str, Any],
    history_check_stats: dict[str, dict[str, float]],
    signature_history: Counter[str],
    max_per_operator: int,
    max_signature_repeats: int,
    min_speedup: float,
    min_check_support_rate: float,
    min_check_history_total: int,
    krr_kb: dict[str, Any] | None,
    krr_backend: str,
    krr_score_weight: float,
) -> dict[str, Any]:
    assignments = [dict(x) for x in manifest.get("innovation_assignments", []) if isinstance(x, dict)]
    score_rows = {str(x.get("candidate_id", "")): dict(x) for x in manifest.get("scores", []) if isinstance(x, dict)}

    # v2 neuro-campaign manifests may provide selected candidate details but no direct
    # innovation assignments.
    if not assignments:
        detail_assignments, detail_scores = _extract_selected_details(manifest)
        if detail_assignments:
            assignments = detail_assignments
            score_rows = {str(x.get("candidate_id", "")): dict(x) for x in detail_scores if isinstance(x, dict)}

    # Legacy/fallback: parse neural response payloads if manifest did not expose enough.
    manifest_path_raw = str(manifest.get("_manifest_path", "")).strip()
    if (not assignments) and manifest_path_raw:
        mpath = Path(manifest_path_raw)
        neuro_assignments, neuro_scores = _extract_neuro_assignments(mpath, manifest)
        assignments = neuro_assignments
        score_rows = {str(x.get("candidate_id", "")): dict(x) for x in neuro_scores if isinstance(x, dict)}

    staged: list[dict[str, Any]] = []
    signature_capped: list[dict[str, Any]] = []
    skipped_reasons: Counter[str] = Counter()
    skipped_examples: list[dict[str, Any]] = []
    krr_backend_counts: Counter[str] = Counter()
    krr_fallback_reasons: Counter[str] = Counter()
    for a in assignments:
        cand_id = str(a.get("candidate_id", "")).strip()
        row = score_rows.get(cand_id, {})
        schema = str(row.get("schema", "unknown")).strip()
        intent_op = str(a.get("descriptor_intent_op", "")).strip()

        op_id = str(a.get("operator_id", "")).strip()
        bridge = OPERATOR_BRIDGE.get(op_id)
        if bridge is None:
            # Compatibility: newer ZAG versions may emit operator IDs we don't explicitly map.
            # Degrade gracefully by mapping based on schema/intent operator families.
            fallback = _operator_id_from_schema_intent(schema=schema, intent_op=intent_op)
            bridge = OPERATOR_BRIDGE.get(fallback or "")
            if bridge is None:
                skipped_reasons["unknown_operator"] += 1
                continue
            a["_operator_id_original"] = op_id
            op_id = str(fallback)
            a["operator_id"] = op_id
            a["operator_description"] = OPERATOR_DESCRIPTIONS.get(op_id, str(a.get("operator_description", "")))

        semantic_sig = str(
            row.get("semantic_signature")
            or a.get("semantic_signature")
            or ""
        ).strip()
        base_check_options = _bridge_checks(bridge)
        krr_advice: dict[str, Any] = {}
        check_options = list(base_check_options)
        krr_min_speedup_override = None
        krr_score_delta = 0.0
        if callable(advise_candidate_krr):
            try:
                krr_advice = advise_candidate_krr(
                    operator_id=op_id,
                    schema=schema,
                    semantic_signature=semantic_sig,
                    check_options=list(base_check_options),
                    history_check_stats=history_check_stats,
                    kb=krr_kb if isinstance(krr_kb, dict) else {},
                    backend=str(krr_backend or "auto"),
                )
            except Exception as exc:
                krr_advice = {
                    "preferred_checks": list(base_check_options),
                    "confidence": 0.0,
                    "backend_used": "error",
                    "backend_fallback_reason": f"krr_error:{type(exc).__name__}",
                    "score_delta": 0.0,
                }
            preferred_checks = [
                str(x).strip()
                for x in list(krr_advice.get("preferred_checks", []) or [])
                if str(x).strip()
            ]
            if preferred_checks:
                check_options = _uniq(preferred_checks + list(base_check_options))
            krr_min_speedup_override = krr_advice.get("min_speedup_override")
            if krr_min_speedup_override is not None:
                krr_min_speedup_override = _parse_float(krr_min_speedup_override, float(min_speedup))
            krr_score_delta = _parse_float(krr_advice.get("score_delta", 0.0), 0.0)
            backend_used = str(krr_advice.get("backend_used", "none")).strip() or "none"
            krr_backend_counts[backend_used] += 1
            krr_fb_raw = krr_advice.get("backend_fallback_reason")
            krr_fb = str(krr_fb_raw).strip() if krr_fb_raw is not None else ""
            if krr_fb:
                krr_fallback_reasons[krr_fb] += 1

        check_pick = _select_check(
            bridge=bridge,
            check_choices_override=check_options,
            history_check_stats=history_check_stats,
            min_check_support_rate=min_check_support_rate,
            min_check_history_total=min_check_history_total,
        )
        check = str(check_pick.get("check", "")).strip()
        if not check:
            skipped_reasons["missing_check_mapping"] += 1
            continue
        semantic_sig = str(
            row.get("semantic_signature")
            or a.get("semantic_signature")
            or ""
        ).strip()
        check_total = int(_parse_float(check_pick.get("check_total", 0), 0.0))
        check_rate = check_pick.get("check_rate")
        if not bool(check_pick.get("signal_ok", True)):
            skipped_reasons["low_signal_check"] += 1
            skipped_examples.append(
                {
                    "candidate_id": cand_id,
                    "operator_id": op_id,
                    "check": check,
                    "check_options": check_options,
                    "reason": "low_signal_check",
                    "check_support_rate": float(check_rate),
                    "check_total": check_total,
                    "krr_backend_used": str(krr_advice.get("backend_used", "")),
                }
            )
            continue

        speedup = _parse_float(row.get("speedup", 1.0), 1.0)
        speedup_observed = bool(row.get("speedup_observed", False))
        speedup_base = float(min_speedup)
        if isinstance(krr_min_speedup_override, (int, float)):
            speedup_base = min(speedup_base, float(krr_min_speedup_override))
        effective_min_speedup = _effective_min_speedup(
            base_min_speedup=speedup_base,
            check_support_rate=float(check_rate) if isinstance(check_rate, (int, float)) else None,
            check_total=check_total,
        )
        if speedup_observed and speedup < float(effective_min_speedup):
            skipped_reasons["speedup_below_min"] += 1
            skipped_examples.append(
                {
                    "candidate_id": cand_id,
                    "operator_id": op_id,
                    "check": check,
                    "reason": "speedup_below_min",
                    "speedup": speedup,
                    "min_speedup": float(min_speedup),
                    "effective_min_speedup": float(effective_min_speedup),
                    "krr_min_speedup_override": krr_min_speedup_override,
                }
            )
            continue

        signature = _signature_key(
            operator_id=op_id,
            check=check,
            schema=schema,
            intent_op=intent_op,
            semantic_sig=semantic_sig,
        )
        prior_repeats = int(signature_history.get(signature, 0))
        score = _selection_score(
            status=str(row.get("status", "TESTED_ONLY")),
            speedup=speedup,
            speedup_observed=speedup_observed,
            prior_signature_count=prior_repeats,
            check_support_rate=float(check_rate) if isinstance(check_rate, (int, float)) else None,
            check_total=check_total,
            proof_priority=a.get("proof_priority") if isinstance(a.get("proof_priority"), int) else None,
            candidate_hypothesis=str(a.get("candidate_hypothesis", "")),
        )
        score += float(krr_score_weight) * float(krr_score_delta)
        staged_row = {
            "assignment": dict(a),
            "score_row": dict(row),
            "operator_id": op_id,
            "signature": signature,
            "semantic_signature": semantic_sig,
            "score": float(score),
            "check": check,
            "check_support_rate": float(check_rate) if isinstance(check_rate, (int, float)) else None,
            "check_total": check_total,
            "effective_min_speedup": float(effective_min_speedup),
            "prior_repeats": prior_repeats,
            "krr_advice": dict(krr_advice),
            "krr_score_delta": float(krr_score_delta),
        }
        if prior_repeats >= int(max(0, max_signature_repeats)):
            skipped_reasons["signature_repeat_cap"] += 1
            skipped_examples.append(
                {
                    "candidate_id": cand_id,
                    "operator_id": op_id,
                    "check": check,
                    "reason": "signature_repeat_cap",
                    "prior_repeats": prior_repeats,
                    "max_signature_repeats": int(max_signature_repeats),
                }
            )
            signature_capped.append(staged_row)
            continue
        staged.append(staged_row)

    # Degrade gracefully: if novelty cap eliminates everything, allow capped
    # candidates through (still ranked and operator-capped).
    fallback_relaxed_signature_cap = False
    if not staged and signature_capped:
        staged = list(signature_capped)
        fallback_relaxed_signature_cap = True
        skipped_reasons["fallback_relaxed_signature_cap"] += len(signature_capped)

    staged.sort(
        key=lambda x: (
            float(x.get("score", 0.0)),
            _parse_float((x.get("score_row") or {}).get("speedup", 1.0), 1.0),
        ),
        reverse=True,
    )

    hypotheses: list[dict[str, Any]] = []
    selected_signatures: set[str] = set()
    selected_by_operator: Counter[str] = Counter()
    idx = 1
    for row in staged:
        op_id = str(row.get("operator_id", ""))
        if selected_by_operator[op_id] >= int(max(1, max_per_operator)):
            skipped_reasons["operator_cap"] += 1
            continue
        signature = str(row.get("signature", ""))
        if signature in selected_signatures:
            skipped_reasons["duplicate_signature_in_pack"] += 1
            continue
        selected_signatures.add(signature)
        selected_by_operator[op_id] += 1

        a = dict(row.get("assignment", {}))
        a["_selected_check"] = str(row.get("check", ""))
        a["_selection_score"] = float(row.get("score", 0.0))
        a["_check_support_rate"] = row.get("check_support_rate")
        a["_check_total"] = int(row.get("check_total", 0))
        a["_effective_min_speedup"] = float(_parse_float(row.get("effective_min_speedup"), 0.0))
        a["_signature"] = signature
        a["_krr_advice"] = dict(row.get("krr_advice", {}))
        a["_krr_score_delta"] = float(_parse_float(row.get("krr_score_delta"), 0.0))
        score_row = dict(row.get("score_row", {}))
        h = _mk_hypothesis(cycle=cycle, idx=idx, assignment=a, score_row=score_row)
        if h:
            hypotheses.append(h)
            idx += 1

    return {
        "schema": "zenodex/zag-bridge-hypothesis-pack/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "source_manifest": manifest.get("run_path", ""),
        "count": len(hypotheses),
        "hypotheses": hypotheses,
        "selection_stats": {
            "input_assignments": len(assignments),
            "staged_after_filters": len(staged),
            "selected": len(hypotheses),
            "max_per_operator": int(max_per_operator),
            "max_signature_repeats": int(max_signature_repeats),
            "min_speedup": float(min_speedup),
            "min_check_support_rate": float(min_check_support_rate),
            "min_check_history_total": int(min_check_history_total),
            "selected_by_operator": dict(selected_by_operator),
            "fallback_relaxed_signature_cap": bool(fallback_relaxed_signature_cap),
            "krr_backend_counts": dict(krr_backend_counts),
            "krr_fallback_reasons": dict(krr_fallback_reasons),
            "krr_score_weight": float(krr_score_weight),
            "skip_reason_counts": dict(skipped_reasons),
            "skip_examples": skipped_examples[:32],
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Convert ZAG innovation assignments into ZenoDEX hypothesis seeds.")
    ap.add_argument("--cycle", type=int, required=True, help="Target cycle index for hypothesis IDs.")
    ap.add_argument("--zag-manifest", type=Path, required=True, help="Path to ZAG gen_k manifest.json.")
    ap.add_argument("--out-json", type=Path, required=True, help="Output JSON path for bridged hypotheses.")
    ap.add_argument(
        "--history-summary-glob",
        action="append",
        default=["runs/manual_morph_supervised/*zag*eval/summary.json"],
        help="Glob(s) to prior ZAG eval summary.json files for check reliability priors.",
    )
    ap.add_argument(
        "--prior-bridge-glob",
        action="append",
        default=["runs/manual_morph_supervised/**/zag_bridge_hypotheses*.json"],
        help="Glob(s) to prior bridge hypothesis packs for novelty/repetition filtering.",
    )
    ap.add_argument("--max-per-operator", type=int, default=2, help="Max selected hypotheses per operator family.")
    ap.add_argument(
        "--max-signature-repeats",
        type=int,
        default=3,
        help="Drop candidates when same signature appeared at least this many times in prior bridge packs.",
    )
    ap.add_argument(
        "--min-speedup",
        type=float,
        default=1.0,
        help="Minimum observed speedup to keep a candidate (ignored when speedup is unavailable).",
    )
    ap.add_argument(
        "--min-check-support-rate",
        type=float,
        default=0.15,
        help="Drop candidates whose mapped check has lower historical support rate once history is sufficient.",
    )
    ap.add_argument(
        "--min-check-history-total",
        type=int,
        default=6,
        help="Minimum historical check count before support-rate filter is applied.",
    )
    ap.add_argument(
        "--krr-kb",
        type=Path,
        default=Path("tools/krr_knowledge_base.json"),
        help="Knowledge base JSON for symbolic KRR advisor.",
    )
    ap.add_argument(
        "--krr-backend",
        type=str,
        default="auto",
        choices=["auto", "python", "prolog", "souffle", "off"],
        help="KRR backend selector (`prolog`/`souffle` use symbolic engines when installed).",
    )
    ap.add_argument(
        "--krr-score-weight",
        type=float,
        default=1.0,
        help="Multiplier for KRR score delta in candidate ranking.",
    )
    args = ap.parse_args()

    manifest_path = (ROOT / args.zag_manifest).resolve() if not args.zag_manifest.is_absolute() else args.zag_manifest
    out_path = (ROOT / args.out_json).resolve() if not args.out_json.is_absolute() else args.out_json

    manifest = _read_json(manifest_path)
    if isinstance(manifest, dict):
        manifest["_manifest_path"] = str(manifest_path)
    history_check_stats = _load_check_history(list(args.history_summary_glob or []))
    signature_history = _load_signature_history(list(args.prior_bridge_glob or []))
    kb_path = (ROOT / args.krr_kb).resolve() if not args.krr_kb.is_absolute() else args.krr_kb
    krr_kb = {}
    if callable(load_krr_kb):
        try:
            krr_kb = load_krr_kb(kb_path)
        except Exception:
            krr_kb = {}
    pack = _build_bridge_pack(
        cycle=int(args.cycle),
        manifest=manifest if isinstance(manifest, dict) else {},
        history_check_stats=history_check_stats,
        signature_history=signature_history,
        max_per_operator=int(max(1, args.max_per_operator)),
        max_signature_repeats=int(max(0, args.max_signature_repeats)),
        min_speedup=float(args.min_speedup),
        min_check_support_rate=float(args.min_check_support_rate),
        min_check_history_total=int(max(0, args.min_check_history_total)),
        krr_kb=krr_kb,
        krr_backend=str(args.krr_backend),
        krr_score_weight=float(args.krr_score_weight),
    )
    _write_json(out_path, pack)

    print(
        json.dumps(
            {
                "ok": True,
                "out": str(out_path),
                "count": int(pack.get("count", 0)),
                "selection_stats": pack.get("selection_stats", {}),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
