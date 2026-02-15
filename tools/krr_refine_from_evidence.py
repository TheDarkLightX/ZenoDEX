#!/usr/bin/env python3
from __future__ import annotations

import argparse
import copy
import glob
import json
import re
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_KB_IN = ROOT / "tools" / "krr_knowledge_base.json"
DEFAULT_KB_OUT = ROOT / "tools" / "krr_knowledge_base.refined.json"

_PREDICATE_TOKEN_MAP: dict[str, set[str]] = {
    "canonicalization": {
        "canonical",
        "canonicalize",
        "lex",
        "lexicographic",
        "normal_form",
        "deterministic_order",
        "tie_break",
        "total_key",
    },
    "routing": {"route", "routing", "path", "hop", "2hop", "split", "pool"},
    "invariant_guard": {"invariant", "inductive", "guard", "safety", "conservation"},
    "decomposition": {"divide_and_conquer", "divide", "partition", "chunk", "merge", "reduce"},
    "dualization": {"dual", "dualize", "shadow_price", "lagrangian"},
    "lift_project": {"lift", "project", "projection", "relax", "relaxation"},
    "performance": {"array", "index", "branchless", "cache", "latency", "throughput"},
}


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_float(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except Exception:
        return float(default)


def _safe_token(text: str, max_len: int = 64) -> str:
    out: list[str] = []
    for ch in str(text):
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    token = "".join(out).strip("._").lower()
    if not token:
        token = "x"
    return token[:max_len]


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


def _load_kb(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {
            "schema": "zenodex/krr-kb/v1",
            "engine": {
                "backend": "auto",
                "prolog": {"binary": "swipl", "timeout_s": 2.0, "preferred_bonus": 0.03},
                "souffle": {"binary": "souffle", "timeout_s": 2.0, "preferred_bonus": 0.03},
            },
            "operator_priors": {},
            "semantic_rules": [],
            "check_priors": {},
            "check_family_priors": {},
        }
    try:
        obj = _read_json(path)
    except Exception:
        obj = {}
    if not isinstance(obj, dict):
        obj = {}
    obj.setdefault("schema", "zenodex/krr-kb/v1")
    obj.setdefault(
        "engine",
        {
            "backend": "auto",
            "prolog": {"binary": "swipl", "timeout_s": 2.0, "preferred_bonus": 0.03},
            "souffle": {"binary": "souffle", "timeout_s": 2.0, "preferred_bonus": 0.03},
        },
    )
    obj.setdefault("operator_priors", {})
    obj.setdefault("semantic_rules", [])
    obj.setdefault("check_priors", {})
    obj.setdefault("check_family_priors", {})
    return obj


def _status_label(text: str) -> str:
    s = str(text or "").strip().lower()
    if s in {"supported", "falsified", "inconclusive"}:
        return s
    return "other"


def _semantic_tokens(sig: str) -> list[str]:
    text = str(sig or "").lower()
    text = text.replace("|", " ")
    parts = re.split(r"[^a-z0-9_]+", text)
    stop = {
        "op",
        "schema",
        "true",
        "false",
        "none",
        "null",
        "unknown",
        "and",
        "or",
        "with",
        "from",
        "then",
        "else",
        "set",
        "get",
    }
    out: list[str] = []
    seen: set[str] = set()
    for tok in parts:
        t = tok.strip("_")
        if len(t) < 3:
            continue
        if t in stop:
            continue
        if t.isdigit():
            continue
        if t in seen:
            continue
        seen.add(t)
        out.append(t)
    return out[:24]


def _score_bias_from_rate(*, rate: float, total: int, gain: float) -> float:
    conf = min(1.0, float(max(0, total)) / 24.0)
    centered = float(rate) - 0.5
    return round(gain * centered * conf, 4)


def _check_family(check: str) -> str:
    c = str(check or "").strip()
    if not c:
        return ""
    if "::" in c:
        return c.split("::", 1)[0].strip()
    return c


def _token_predicates(token: str) -> set[str]:
    t = str(token or "").strip().lower()
    if not t:
        return set()
    out: set[str] = set()
    for pred, keys in _PREDICATE_TOKEN_MAP.items():
        if t in keys:
            out.add(pred)
    if t.startswith("route") or t.endswith("route"):
        out.add("routing")
    if t.startswith("canon") or "lex" in t:
        out.add("canonicalization")
    if t.startswith("invariant") or t.endswith("guard"):
        out.add("invariant_guard")
    if t.startswith("partition") or t.startswith("divide"):
        out.add("decomposition")
    if t.startswith("dual"):
        out.add("dualization")
    if t.startswith("lift") or t.startswith("project"):
        out.add("lift_project")
    return out


def _build_hypothesis_index(bridge_paths: list[Path]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for p in bridge_paths:
        try:
            obj = _read_json(p)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        for h in obj.get("hypotheses", []):
            if not isinstance(h, dict):
                continue
            hid = str(h.get("hypothesis_id", "")).strip()
            if not hid:
                continue
            out[hid] = {
                "operator_id": str(h.get("operator_id", "")).strip(),
                "support_recipe": str(h.get("support_recipe", "")).strip(),
                "semantic_signature": str(h.get("zag_semantic_signature", "")).strip(),
                "zag_schema": str(h.get("zag_schema", "")).strip(),
            }
    return out


def _collect_evidence(summary_paths: list[Path], hypothesis_index: dict[str, dict[str, Any]]) -> dict[str, Any]:
    check_total: Counter[str] = Counter()
    check_supported: Counter[str] = Counter()
    check_family_total: Counter[str] = Counter()
    check_family_supported: Counter[str] = Counter()

    op_total: Counter[str] = Counter()
    op_supported: Counter[str] = Counter()

    op_check_total: Counter[tuple[str, str]] = Counter()
    op_check_supported: Counter[tuple[str, str]] = Counter()

    tok_total: Counter[str] = Counter()
    tok_check_total: Counter[tuple[str, str]] = Counter()
    tok_check_supported: Counter[tuple[str, str]] = Counter()

    matched_rows = 0
    unmatched_rows = 0

    for p in summary_paths:
        try:
            obj = _read_json(p)
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        rows = obj.get("rows", [])
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            hid = str(row.get("hypothesis_id", "")).strip()
            if not hid:
                continue
            status = _status_label(str(row.get("final_status", "")))
            row_check = str(row.get("check", "")).strip()
            if row_check:
                check_total[row_check] += 1
                fam = _check_family(row_check)
                if fam:
                    check_family_total[fam] += 1
                if status == "supported":
                    check_supported[row_check] += 1
                    if fam:
                        check_family_supported[fam] += 1

            meta = hypothesis_index.get(hid)
            if not isinstance(meta, dict):
                unmatched_rows += 1
                continue
            matched_rows += 1
            check = str(row.get("check", "")).strip() or str(meta.get("support_recipe", "")).strip()
            op = str(meta.get("operator_id", "")).strip()
            sem = str(meta.get("semantic_signature", "")).strip()
            if not check:
                continue

            if op:
                op_total[op] += 1
                op_check_total[(op, check)] += 1
                if status == "supported":
                    op_supported[op] += 1
                    op_check_supported[(op, check)] += 1

            toks = _semantic_tokens(sem)
            for tok in toks:
                tok_total[tok] += 1
                tok_check_total[(tok, check)] += 1
                if status == "supported":
                    tok_check_supported[(tok, check)] += 1

    return {
        "check_total": check_total,
        "check_supported": check_supported,
        "op_total": op_total,
        "op_supported": op_supported,
        "op_check_total": op_check_total,
        "op_check_supported": op_check_supported,
        "tok_total": tok_total,
        "tok_check_total": tok_check_total,
        "tok_check_supported": tok_check_supported,
        "check_family_total": check_family_total,
        "check_family_supported": check_family_supported,
        "matched_rows": matched_rows,
        "unmatched_rows": unmatched_rows,
    }


def _refine_kb(
    *,
    kb: dict[str, Any],
    evidence: dict[str, Any],
    min_count: int,
    max_preferred_checks: int,
    token_min_count: int,
    max_auto_rules: int,
) -> dict[str, Any]:
    out = copy.deepcopy(kb)
    out.setdefault("operator_priors", {})
    out.setdefault("check_priors", {})
    out.setdefault("check_family_priors", {})
    out.setdefault("semantic_rules", [])

    check_total: Counter[str] = evidence["check_total"]
    check_supported: Counter[str] = evidence["check_supported"]
    op_total: Counter[str] = evidence["op_total"]
    op_supported: Counter[str] = evidence["op_supported"]
    op_check_total: Counter[tuple[str, str]] = evidence["op_check_total"]
    op_check_supported: Counter[tuple[str, str]] = evidence["op_check_supported"]
    tok_total: Counter[str] = evidence["tok_total"]
    tok_check_total: Counter[tuple[str, str]] = evidence["tok_check_total"]
    tok_check_supported: Counter[tuple[str, str]] = evidence["tok_check_supported"]
    check_family_total: Counter[str] = evidence["check_family_total"]
    check_family_supported: Counter[str] = evidence["check_family_supported"]

    check_priors = out.get("check_priors")
    if not isinstance(check_priors, dict):
        check_priors = {}
        out["check_priors"] = check_priors

    for check, total in check_total.items():
        if total < int(max(1, min_count)):
            continue
        sup = int(check_supported.get(check, 0))
        rate = float(sup) / float(total)
        bias = _score_bias_from_rate(rate=rate, total=total, gain=0.45)
        row = check_priors.get(check)
        if not isinstance(row, dict):
            row = {}
            check_priors[check] = row
        row["score_bias"] = float(bias)
        row["evidence_total"] = int(total)
        row["evidence_supported"] = int(sup)
        row["evidence_support_rate"] = round(rate, 6)
        row["source"] = "auto_refine_v1"

    check_family_priors = out.get("check_family_priors")
    if not isinstance(check_family_priors, dict):
        check_family_priors = {}
        out["check_family_priors"] = check_family_priors

    for family, total in check_family_total.items():
        if total < int(max(1, min_count)):
            continue
        sup = int(check_family_supported.get(family, 0))
        rate = float(sup) / float(total)
        bias = _score_bias_from_rate(rate=rate, total=total, gain=0.3)
        row = check_family_priors.get(family)
        if not isinstance(row, dict):
            row = {}
            check_family_priors[family] = row
        row["score_bias"] = float(bias)
        row["evidence_total"] = int(total)
        row["evidence_supported"] = int(sup)
        row["evidence_support_rate"] = round(rate, 6)
        row["source"] = "auto_refine_v1"

    operator_priors = out.get("operator_priors")
    if not isinstance(operator_priors, dict):
        operator_priors = {}
        out["operator_priors"] = operator_priors

    checks_by_op: dict[str, list[tuple[str, int, int, float]]] = defaultdict(list)
    for (op, check), total in op_check_total.items():
        sup = int(op_check_supported.get((op, check), 0))
        rate = float(sup) / float(total) if total > 0 else 0.0
        checks_by_op[op].append((check, int(total), int(sup), float(rate)))

    for op, total in op_total.items():
        if total < int(max(1, min_count)):
            continue
        sup = int(op_supported.get(op, 0))
        rate = float(sup) / float(total)
        row = operator_priors.get(op)
        if not isinstance(row, dict):
            row = {}
            operator_priors[op] = row

        row["score_bias"] = float(_score_bias_from_rate(rate=rate, total=total, gain=0.7))
        row["evidence_total"] = int(total)
        row["evidence_supported"] = int(sup)
        row["evidence_support_rate"] = round(rate, 6)
        row["source"] = "auto_refine_v1"

        ranked = []
        for check, c_total, c_sup, c_rate in checks_by_op.get(op, []):
            if c_total < int(max(1, min_count)):
                continue
            conf = min(1.0, float(c_total) / 16.0)
            score = c_rate + 0.1 * conf
            ranked.append((score, check, c_total, c_sup, c_rate))
        ranked.sort(key=lambda x: (x[0], x[2], x[1]), reverse=True)

        preferred_checks = [x[1] for x in ranked[: int(max(1, max_preferred_checks))]]
        if preferred_checks:
            row["check_preferences"] = preferred_checks

        avoid_checks = [x[1] for x in ranked if x[2] >= int(max(3, min_count)) and x[4] <= 0.2]
        if avoid_checks:
            row["avoid_checks"] = sorted(set(avoid_checks))

        if rate >= 0.55:
            row["min_speedup_override"] = round(max(0.85, 1.0 - 0.25 * (rate - 0.5)), 3)

    semantic_rules = out.get("semantic_rules")
    if not isinstance(semantic_rules, list):
        semantic_rules = []
    base_rules = [r for r in semantic_rules if isinstance(r, dict) and str(r.get("source", "")) != "auto_refine_v1"]

    auto_rules: list[dict[str, Any]] = []
    for tok, t_total in tok_total.items():
        if int(t_total) < int(max(1, token_min_count)):
            continue
        best = None
        for (tt, check), c_total in tok_check_total.items():
            if tt != tok:
                continue
            if int(c_total) < int(max(1, min_count)):
                continue
            c_sup = int(tok_check_supported.get((tt, check), 0))
            c_rate = float(c_sup) / float(c_total) if c_total > 0 else 0.0
            conf = min(1.0, float(c_total) / 12.0)
            score = c_rate + 0.08 * conf
            row = (score, check, int(c_total), int(c_sup), c_rate)
            if best is None or row > best:
                best = row
        if best is None:
            continue
        _, check, c_total, c_sup, c_rate = best
        if c_rate < 0.65:
            continue
        rule: dict[str, Any] = {
            "name": f"auto_tok_{_safe_token(tok, 40)}_{_safe_token(check, 48)}",
            "if_semantic_contains": [tok],
            "then_prefer_checks": [check],
            "score_bias": float(_score_bias_from_rate(rate=c_rate, total=c_total, gain=0.35)),
            "evidence_total": int(c_total),
            "evidence_supported": int(c_sup),
            "evidence_support_rate": round(c_rate, 6),
            "source": "auto_refine_v1",
        }
        preds = sorted(_token_predicates(tok))
        if preds:
            rule["if_semantic_predicates_any"] = preds
        auto_rules.append(rule)

    auto_rules.sort(
        key=lambda r: (
            _safe_float(r.get("evidence_support_rate"), 0.0),
            int(r.get("evidence_total", 0)),
            str(r.get("name", "")),
        ),
        reverse=True,
    )
    auto_rules = auto_rules[: int(max(0, max_auto_rules))]
    out["semantic_rules"] = base_rules + auto_rules

    # Adapt scoring posture from observed support landscape.
    total_events = sum(int(v) for v in check_total.values())
    supported_events = sum(int(v) for v in check_supported.values())
    support_rate_global = (float(supported_events) / float(total_events)) if total_events > 0 else 0.5
    engine = out.get("engine")
    if not isinstance(engine, dict):
        engine = {}
        out["engine"] = engine
    scoring = engine.get("scoring")
    if not isinstance(scoring, dict):
        scoring = {}
        engine["scoring"] = scoring
    # If pass-rate is near ceiling, push exploration and uncertainty terms upward.
    if support_rate_global >= 0.95:
        scoring["exploration_weight"] = round(max(0.24, _safe_float(scoring.get("exploration_weight"), 0.22) + 0.04), 4)
        scoring["uncertainty_weight"] = round(max(0.1, _safe_float(scoring.get("uncertainty_weight"), 0.08) + 0.03), 4)
        scoring["uncertainty_penalty_weight"] = round(max(0.04, _safe_float(scoring.get("uncertainty_penalty_weight"), 0.06) - 0.01), 4)
        scoring["exploitation_weight"] = round(max(0.55, _safe_float(scoring.get("exploitation_weight"), 0.72) - 0.04), 4)
    else:
        scoring.setdefault("exploration_weight", 0.22)
        scoring.setdefault("uncertainty_weight", 0.08)
        scoring.setdefault("uncertainty_penalty_weight", 0.06)
        scoring.setdefault("exploitation_weight", 0.72)
    scoring.setdefault("reliability_weight", 0.12)
    scoring.setdefault("backend_score_weight", 0.14)
    scoring.setdefault("prior_evidence_weight", 0.5)
    scoring.setdefault("pseudo_count", 1.0)
    scoring.setdefault("position_bonus_weight", 0.01)
    scoring.setdefault("preference_bonus", 0.03)
    scoring.setdefault("reliability_scale", 32.0)

    out["learning"] = {
        "source": "tools/krr_refine_from_evidence.py",
        "version": "v1",
        "updated_at": int(time.time()),
        "matched_rows": int(evidence.get("matched_rows", 0)),
        "unmatched_rows": int(evidence.get("unmatched_rows", 0)),
        "check_count": len(check_total),
        "operator_count": len(op_total),
        "check_family_count": len(check_family_total),
        "token_count": len(tok_total),
        "auto_rule_count": len(auto_rules),
        "min_count": int(min_count),
        "token_min_count": int(token_min_count),
        "global_support_rate": round(support_rate_global, 6),
    }

    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="Refine KRR knowledge base from supervised evidence artifacts.")
    ap.add_argument("--kb-in", type=Path, default=Path("tools/krr_knowledge_base.json"), help="Input KRR KB JSON.")
    ap.add_argument("--kb-out", type=Path, default=Path("tools/krr_knowledge_base.refined.json"), help="Output refined KB JSON.")
    ap.add_argument(
        "--summary-glob",
        action="append",
        default=["runs/manual_morph_supervised/*zag_bridge*eval*/summary.json"],
        help="Summary JSON glob(s) with rows containing hypothesis_id/check/final_status.",
    )
    ap.add_argument(
        "--bridge-glob",
        action="append",
        default=["runs/manual_morph_supervised/**/zag_bridge_hypotheses*.json"],
        help="Bridge hypothesis pack glob(s).",
    )
    ap.add_argument("--min-count", type=int, default=4, help="Minimum support for learning any prior.")
    ap.add_argument("--max-preferred-checks", type=int, default=3, help="Max preferred checks per operator.")
    ap.add_argument("--token-min-count", type=int, default=6, help="Minimum token evidence for auto semantic rule.")
    ap.add_argument("--max-auto-rules", type=int, default=24, help="Maximum auto semantic rules to emit.")
    args = ap.parse_args()

    kb_in = (ROOT / args.kb_in).resolve() if not args.kb_in.is_absolute() else args.kb_in
    kb_out = (ROOT / args.kb_out).resolve() if not args.kb_out.is_absolute() else args.kb_out

    kb = _load_kb(kb_in)
    summaries = _expand_globs(list(args.summary_glob or []))
    bridges = _expand_globs(list(args.bridge_glob or []))
    hypothesis_index = _build_hypothesis_index(bridges)
    evidence = _collect_evidence(summaries, hypothesis_index)
    refined = _refine_kb(
        kb=kb,
        evidence=evidence,
        min_count=int(max(1, args.min_count)),
        max_preferred_checks=int(max(1, args.max_preferred_checks)),
        token_min_count=int(max(1, args.token_min_count)),
        max_auto_rules=int(max(0, args.max_auto_rules)),
    )
    _write_json(kb_out, refined)

    print(
        json.dumps(
            {
                "ok": True,
                "kb_in": str(kb_in),
                "kb_out": str(kb_out),
                "summary_files": len(summaries),
                "bridge_files": len(bridges),
                "hypothesis_index_size": len(hypothesis_index),
                "matched_rows": int(evidence.get("matched_rows", 0)),
                "unmatched_rows": int(evidence.get("unmatched_rows", 0)),
                "learning": refined.get("learning", {}),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
