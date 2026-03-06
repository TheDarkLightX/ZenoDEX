#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]

try:
    from tools.zenodex_autonomous_checks import CHECK_DISPATCH  # type: ignore
except Exception:
    CHECK_DISPATCH = {}


# Fallback for environments where importing zenodex_autonomous_checks fails.
BASE_CHECK_FALLBACK = {
    "split_routing_gap",
    "split_routing_no_gap",
    "twap_staleness_effect",
    "perp_clamp_profit",
    "batch_greedy_invariants",
    "batch_clearing_gap_exists",
    "batch_clearing_no_gap",
    "esso_cpmm_verify",
    "lean_batch_canonical",
    "roundtrip_no_positive_profit",
    "roundtrip_positive_profit_exists",
    "lp_rounding_tests",
    "settlement_normal_form",
    "settlement_ordering_nondeterminism_exists",
    "il_insurance_vuln_presence",
    "il_insurance_status_quo_safe",
    "route_exact_out_2hop_value",
    "route_exact_out_no_2hop_value",
    "dgstr_exact_match",
    "dgstr_eval_count",
    "perp_lp_fee_share_guard",
    "perp_lp_fee_share_irrelevant",
    "perp_reserve_hardening_effect",
    "curve_sum_boost_exact_out_advantage",
    "cpmm_overdelivery_witness",
    "cpmm_no_overdelivery",
    "cpmm_no_overdelivery_guarded",
    "intent_normal_form_tests",
    "intent_normal_form_regression_exists",
    "state_root_determinism",
    "state_root_nondeterminism_exists",
    "cpmm_ref_parity",
    "cpmm_ref_parity_broken",
    "dex_v8_ref_parity",
    "dex_v8_ref_parity_broken",
    "perp_v2_invariants",
    "perp_v2_invariant_break_exists",
    "perp_v2_oracle_equiv",
    "perp_v2_oracle_divergence_exists",
    "curve_selection_safety",
    "curve_selection_unsafe_exists",
    "split_routing_regression",
    "split_routing_regression_exists",
    "batch_clearing_regression",
    "batch_clearing_invariant_break_exists",
}


REGEX_FAMILIES = [
    re.compile(r"^perp_oracle_lp_attack_(absent|exists)::.+$"),
    re.compile(r"^split_routing_case_(optimal|gap_exists)::[A-Za-z0-9_]+::.+$"),
    re.compile(r"^split_routing_tradeoff::[A-Za-z0-9_]+::.+$"),
    re.compile(r"^exact_out_split_tradeoff::[A-Za-z0-9_]+::.+$"),
    re.compile(r"^routing_split_case_(optimal|gap_exists)::[A-Za-z0-9_]+::.+$"),
    re.compile(r"^exact_out_gate_tradeoff::[A-Za-z0-9_]+::.+$"),
    re.compile(r"^cegis_preflight_expect::[A-Za-z0-9_]+::[A-Za-z0-9_,.\-]+::\d+::\d+::\d+::.+::.+$"),
    re.compile(r"^esso_synth_nontrivial::[A-Za-z0-9_,.\-]+::\d+::.+::.+::[A-Za-z0-9_*.\-]+::[A-Za-z0-9_.*+\-]+$"),
    re.compile(r"^esso_sygus_grammar_embedded::[A-Za-z0-9_,.\-]+::\d+::.+::.+$"),
    re.compile(r"^esso_qsygus_terms_min::[A-Za-z0-9_,.\-]+::\d+::.+::.+::\d+$"),
    re.compile(r"^esso_cpmm_quality_min_mean_ppm::[A-Za-z0-9_,.\-]+::\d+::.+::.+::\d+::\d+$"),
    re.compile(r"^esso_d16_static_expect::[A-Za-z0-9_]+::.+$"),
    re.compile(r"^esso_d16_regime_expect::[A-Za-z0-9_]+::[A-Za-z0-9_,.\-]+::\d+::.+::.+$"),
    re.compile(r"^pytest_repeat\d+::.+$"),
    re.compile(r"^lean_repeat\d+::.+$"),
    re.compile(r"^esso_verify_solver_timeout::[A-Za-z0-9_,.\-]+::\d+::.+$"),
    re.compile(r"^esso_synth_solver_timeout::[A-Za-z0-9_,.\-]+::\d+::.+::.+$"),
    re.compile(r"^esso_synth_solver::[A-Za-z0-9_,.\-]+::.+::.+$"),
    re.compile(r"^esso_synth_fail_solver_timeout::[A-Za-z0-9_,.\-]+::\d+::.+::.+$"),
    re.compile(r"^esso_synth_fail_solver::[A-Za-z0-9_,.\-]+::.+::.+$"),
    re.compile(r"^esso_spec_debug_class::[A-Za-z0-9_]+::.+::.+$"),
    re.compile(r"^esso_verify_solver::[A-Za-z0-9_,.\-]+::.+$"),
    re.compile(r"^esso_fail_solver_timeout::[A-Za-z0-9_,.\-]+::\d+::.+$"),
    re.compile(r"^esso_fail_solver::[A-Za-z0-9_,.\-]+::.+$"),
    re.compile(r"^esso_repeat\d+_solver_timeout::[A-Za-z0-9_,.\-]+::\d+::.+$"),
    re.compile(r"^esso_repeat\d+_solver::[A-Za-z0-9_,.\-]+::.+$"),
    re.compile(r"^esso_repeat\d+::.+$"),
]

PREFIX_FAMILIES = [
    "pytest_pass::",
    "pytest_fail::",
    "lean_pass::",
    "lean_fail::",
    "esso_synth::",
    "esso_synth_fail::",
    "esso_verify::",
    "esso_fail::",
]


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_hypotheses(path: Path, key: str) -> list[dict[str, Any]]:
    raw = _read_json(path)
    if isinstance(raw, list):
        rows = raw
    elif isinstance(raw, dict):
        if key and isinstance(raw.get(key), list):
            rows = raw.get(key, [])
        else:
            rows = raw.get("hypotheses", [])
    else:
        rows = []
    return [dict(x) for x in rows if isinstance(x, dict)]


def _check_recipe(recipe: str) -> tuple[str, str]:
    r = str(recipe or "").strip()
    if not r:
        return ("invalid", "empty_recipe")
    if r.startswith("UNMAPPABLE::"):
        return ("unmappable", "unmappable_prefix")
    known_dispatch = set(CHECK_DISPATCH.keys()) | set(BASE_CHECK_FALLBACK)
    if r in known_dispatch:
        return ("runnable", "dispatch")
    for pref in PREFIX_FAMILIES:
        if r.startswith(pref) and len(r) > len(pref):
            return ("runnable", f"prefix:{pref}")
    for pat in REGEX_FAMILIES:
        if pat.match(r):
            return ("runnable", f"regex:{pat.pattern}")
    return ("unknown", "unknown_check_id")


def _verdict(s_st: str, f_st: str) -> str:
    states = {s_st, f_st}
    if "unknown" in states:
        return "unknown"
    if "invalid" in states:
        return "invalid"
    if "unmappable" in states:
        return "unmappable"
    return "runnable"


def main() -> int:
    ap = argparse.ArgumentParser(description="Lint hypothesis recipes for runnable zenodex_autonomous_checks check IDs.")
    ap.add_argument("--hypotheses-json", type=Path, required=True)
    ap.add_argument("--key", default="hypotheses", help="Optional key to lint inside a JSON object (e.g., top20).")
    ap.add_argument("--json-out", type=Path, default=None)
    ap.add_argument("--strict", action="store_true", help="Exit nonzero when non-runnable recipes are detected.")
    ap.add_argument(
        "--allow-unmappable",
        action="store_true",
        help="With --strict, ignore UNMAPPABLE::* entries and only fail on unknown/invalid recipes.",
    )
    args = ap.parse_args()

    hyp_path = (ROOT / args.hypotheses_json).resolve() if not args.hypotheses_json.is_absolute() else args.hypotheses_json
    rows = _load_hypotheses(hyp_path, str(args.key))

    recs: list[dict[str, Any]] = []
    counts = {
        "runnable": 0,
        "unmappable": 0,
        "unknown": 0,
        "invalid": 0,
    }
    for h in rows:
        hid = str(h.get("hypothesis_id", ""))
        s = str(h.get("support_recipe", ""))
        f = str(h.get("falsification_recipe", ""))
        s_st, s_reason = _check_recipe(s)
        f_st, f_reason = _check_recipe(f)
        v = _verdict(s_st, f_st)
        counts[v] = int(counts.get(v, 0)) + 1
        recs.append(
            {
                "hypothesis_id": hid,
                "support_recipe": s,
                "support_status": s_st,
                "support_reason": s_reason,
                "falsification_recipe": f,
                "falsification_status": f_st,
                "falsification_reason": f_reason,
                "verdict": v,
            }
        )

    out = {
        "schema": "zenodex/design-recipe-lint/v1",
        "source": str(hyp_path),
        "key": str(args.key),
        "count": len(rows),
        "verdict_counts": counts,
        "rows": recs,
    }
    if args.json_out is not None:
        out_path = (ROOT / args.json_out).resolve() if not args.json_out.is_absolute() else args.json_out
        _write_json(out_path, out)
    print(json.dumps(out, sort_keys=True))

    if args.strict:
        if args.allow_unmappable:
            bad = counts.get("unknown", 0) + counts.get("invalid", 0)
        else:
            bad = counts.get("unknown", 0) + counts.get("invalid", 0) + counts.get("unmappable", 0)
        if bad > 0:
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
