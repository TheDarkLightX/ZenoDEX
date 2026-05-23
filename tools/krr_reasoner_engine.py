#!/usr/bin/env python3
from __future__ import annotations

import json
import math
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_KB_PATH = ROOT / "tools" / "krr_knowledge_base.json"

_STOP_TOKENS = {
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
        "totalorder",
    },
    "routing": {
        "route",
        "routing",
        "path",
        "hop",
        "2hop",
        "split",
        "multihop",
        "pool",
    },
    "invariant_guard": {
        "invariant",
        "inductive",
        "guard",
        "safety",
        "conservation",
        "solvency",
    },
    "decomposition": {
        "divide_and_conquer",
        "divide",
        "partition",
        "chunk",
        "merge",
        "reduce",
    },
    "dualization": {
        "dual",
        "dualize",
        "shadow_price",
        "lagrangian",
        "constraint",
    },
    "lift_project": {
        "lift",
        "project",
        "projection",
        "relax",
        "relaxation",
        "round",
    },
    "performance": {
        "array",
        "index",
        "branchless",
        "cache",
        "latency",
        "throughput",
    },
    "execution_quality": {
        "slippage",
        "adverse",
        "selection",
        "mev",
        "sandwich",
        "adaptive",
        "volatility",
        "revert",
    },
    "batch_clearing": {
        "batch",
        "clearing",
        "marginal",
        "insertion",
        "mci",
        "ordering",
        "greedy",
        "optimal",
    },
    "liquidation_prevention": {
        "liquidation",
        "predictive",
        "epochs_to_liq",
        "drain",
        "margin",
        "collateral",
    },
    "funding_verification": {
        "funding",
        "budget",
        "balance",
        "checksum",
        "bb",
        "verifier",
    },
    "oracle_anomaly": {
        "oracle",
        "anomaly",
        "pump",
        "oscillation",
        "staleness",
        "temporal",
    },
    "keeper_liveness": {
        "keeper",
        "liveness",
        "deadlock",
        "epoch_phase",
        "settlement",
        "stateless",
    },
}


def _safe_float(value: Any, default: float) -> float:
    try:
        return float(value)
    except Exception:
        return float(default)


def _safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(float(value))
    except Exception:
        return int(default)


def _safe_token(text: str, max_len: int = 72) -> str:
    out: list[str] = []
    for ch in str(text):
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    token = "".join(out).strip("._")
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


def _clamp(value: float, lo: float, hi: float) -> float:
    if value < lo:
        return float(lo)
    if value > hi:
        return float(hi)
    return float(value)


def _binary_entropy(p: float) -> float:
    pp = _clamp(float(p), 1e-9, 1.0 - 1e-9)
    return -(pp * math.log2(pp) + (1.0 - pp) * math.log2(1.0 - pp))


def _extract_semantic_features(*, schema: str, semantic_signature: str) -> tuple[list[str], set[str]]:
    text = f"{schema}|{semantic_signature}".lower()
    text = text.replace("|", " ")
    parts = re.split(r"[^a-z0-9_]+", text)
    toks: list[str] = []
    seen: set[str] = set()
    for raw in parts:
        t = raw.strip("_")
        if len(t) < 2:
            continue
        if t in _STOP_TOKENS:
            continue
        if t.isdigit():
            continue
        if t in seen:
            continue
        seen.add(t)
        toks.append(t)

    token_set = set(toks)
    predicates: set[str] = set()
    for pred, keywords in _PREDICATE_TOKEN_MAP.items():
        if token_set.intersection(keywords):
            predicates.add(pred)

    # Lightweight substring heuristics for common compounds.
    for tok in token_set:
        if tok.startswith("route") or tok.endswith("route"):
            predicates.add("routing")
        if tok.startswith("canon") or "lex" in tok:
            predicates.add("canonicalization")
        if tok.startswith("invariant") or tok.endswith("guard"):
            predicates.add("invariant_guard")
        if tok.startswith("partition") or tok.startswith("divide"):
            predicates.add("decomposition")
        if tok.startswith("dual"):
            predicates.add("dualization")
        if tok.startswith("lift") or tok.startswith("project"):
            predicates.add("lift_project")
        if tok.startswith("batch") or tok.startswith("clearing") or "mci" in tok:
            predicates.add("batch_clearing")
        if tok.startswith("liquidat") or tok.startswith("predictive"):
            predicates.add("liquidation_prevention")
        if tok.startswith("funding") or "checksum" in tok:
            predicates.add("funding_verification")
        if tok.startswith("oracle") or tok.startswith("anomal"):
            predicates.add("oracle_anomaly")
        if tok.startswith("keeper") or tok.startswith("liveness") or "deadlock" in tok:
            predicates.add("keeper_liveness")

    return toks[:32], predicates


def load_krr_kb(path: Path | str | None = None) -> dict[str, Any]:
    kb_path = Path(path).resolve() if path else DEFAULT_KB_PATH
    if not kb_path.exists():
        return normalize_krr_kb_object(
            {
                "schema": "zenodex/krr-kb/v1",
                "operator_priors": {},
                "semantic_rules": [],
                "check_priors": {},
                "check_family_priors": {},
                "engine": {
                    "backend": "auto",
                    "prolog": {
                        "binary": "swipl",
                        "timeout_s": 2.0,
                        "preferred_bonus": 0.03,
                    },
                    "souffle": {
                        "binary": "souffle",
                        "timeout_s": 2.0,
                        "preferred_bonus": 0.03,
                    },
                    "scoring": {
                        "exploitation_weight": 0.72,
                        "exploration_weight": 0.22,
                        "uncertainty_weight": 0.08,
                        "uncertainty_penalty_weight": 0.06,
                        "reliability_weight": 0.12,
                        "backend_score_weight": 0.14,
                        "prior_evidence_weight": 0.5,
                        "pseudo_count": 1.0,
                        "position_bonus_weight": 0.01,
                        "preference_bonus": 0.03,
                        "reliability_scale": 32.0,
                    },
                },
            },
            kb_path=kb_path,
        )
    try:
        obj = json.loads(kb_path.read_text(encoding="utf-8"))
    except Exception:
        obj = {}
    if not isinstance(obj, dict):
        obj = {}
    return normalize_krr_kb_object(obj, kb_path=kb_path)


def normalize_krr_kb_object(obj: dict[str, Any], *, kb_path: Path | str | None = None) -> dict[str, Any]:
    """Fill optional KRR KB sections with deterministic defaults."""

    if not isinstance(obj, dict):
        raise ValueError("KRR knowledge base must be a JSON object")
    obj.setdefault("schema", "zenodex/krr-kb/v1")
    obj.setdefault("operator_priors", {})
    obj.setdefault("semantic_rules", [])
    obj.setdefault("check_priors", {})
    obj.setdefault("check_family_priors", {})

    engine = obj.get("engine")
    if not isinstance(engine, dict):
        engine = {}
        obj["engine"] = engine
    engine.setdefault("backend", "auto")

    prolog = engine.get("prolog")
    if not isinstance(prolog, dict):
        prolog = {}
        engine["prolog"] = prolog
    prolog.setdefault("binary", "swipl")
    prolog.setdefault("timeout_s", 2.0)
    prolog.setdefault("preferred_bonus", 0.03)

    souffle_cfg = engine.get("souffle")
    if not isinstance(souffle_cfg, dict):
        souffle_cfg = {}
        engine["souffle"] = souffle_cfg
    souffle_cfg.setdefault("binary", "souffle")
    souffle_cfg.setdefault("timeout_s", 2.0)
    souffle_cfg.setdefault("preferred_bonus", 0.03)

    scoring = engine.get("scoring")
    if not isinstance(scoring, dict):
        scoring = {}
        engine["scoring"] = scoring
    scoring.setdefault("exploitation_weight", 0.72)
    scoring.setdefault("exploration_weight", 0.22)
    scoring.setdefault("uncertainty_weight", 0.08)
    scoring.setdefault("uncertainty_penalty_weight", 0.06)
    scoring.setdefault("reliability_weight", 0.12)
    scoring.setdefault("backend_score_weight", 0.14)
    scoring.setdefault("prior_evidence_weight", 0.5)
    scoring.setdefault("pseudo_count", 1.0)
    scoring.setdefault("position_bonus_weight", 0.01)
    scoring.setdefault("preference_bonus", 0.03)
    scoring.setdefault("reliability_scale", 32.0)

    if kb_path is not None:
        obj["_kb_path"] = str(kb_path)
    return obj


def _match_rule(
    rule: dict[str, Any],
    *,
    operator_id: str,
    schema: str,
    semantic_signature: str,
    semantic_tokens: list[str],
    semantic_predicates: set[str],
) -> bool:
    op_filters = [str(x).strip() for x in list(rule.get("if_operator_ids", []) or [])]
    if op_filters and operator_id not in op_filters:
        return False

    schema_filters = [str(x).strip() for x in list(rule.get("if_schema_in", []) or [])]
    if schema_filters and schema not in schema_filters:
        return False

    token_set = {str(x).strip().lower() for x in semantic_tokens if str(x).strip()}
    hay = semantic_signature.lower()

    contains_any = [str(x).strip().lower() for x in list(rule.get("if_semantic_contains", []) or []) if str(x).strip()]
    if contains_any:
        if not any((tok in hay) or (tok in token_set) for tok in contains_any):
            return False

    token_all = [str(x).strip().lower() for x in list(rule.get("if_semantic_all", []) or []) if str(x).strip()]
    if token_all and any(tok not in token_set for tok in token_all):
        return False

    token_any = [str(x).strip().lower() for x in list(rule.get("if_semantic_any", []) or []) if str(x).strip()]
    if token_any and not any(tok in token_set for tok in token_any):
        return False

    token_absent = [str(x).strip().lower() for x in list(rule.get("if_semantic_absent", []) or []) if str(x).strip()]
    if token_absent and any(tok in token_set for tok in token_absent):
        return False

    pred_all = [str(x).strip() for x in list(rule.get("if_semantic_predicates_all", []) or []) if str(x).strip()]
    if pred_all and any(pred not in semantic_predicates for pred in pred_all):
        return False

    pred_any = [str(x).strip() for x in list(rule.get("if_semantic_predicates_any", []) or []) if str(x).strip()]
    if pred_any and not any(pred in semantic_predicates for pred in pred_any):
        return False

    pred_absent = [str(x).strip() for x in list(rule.get("if_semantic_predicates_absent", []) or []) if str(x).strip()]
    if pred_absent and any(pred in semantic_predicates for pred in pred_absent):
        return False

    return True


def _get_scoring_cfg(cfg: dict[str, Any]) -> dict[str, float]:
    engine = cfg.get("engine", {}) if isinstance(cfg, dict) else {}
    scoring = engine.get("scoring", {}) if isinstance(engine, dict) else {}

    def _g(name: str, default: float) -> float:
        return _safe_float(scoring.get(name), default) if isinstance(scoring, dict) else float(default)

    return {
        "exploitation_weight": _g("exploitation_weight", 0.72),
        "exploration_weight": _g("exploration_weight", 0.22),
        "uncertainty_weight": _g("uncertainty_weight", 0.08),
        "uncertainty_penalty_weight": _g("uncertainty_penalty_weight", 0.06),
        "reliability_weight": _g("reliability_weight", 0.12),
        "backend_score_weight": _g("backend_score_weight", 0.14),
        "prior_evidence_weight": _g("prior_evidence_weight", 0.5),
        "pseudo_count": max(0.01, _g("pseudo_count", 1.0)),
        "position_bonus_weight": _g("position_bonus_weight", 0.01),
        "preference_bonus": _g("preference_bonus", 0.03),
        "reliability_scale": max(1.0, _g("reliability_scale", 32.0)),
    }


def _check_family(check: str) -> str:
    c = str(check or "").strip()
    if not c:
        return ""
    if "::" in c:
        return c.split("::", 1)[0].strip()
    return c


def _expand_check_priors(
    *,
    candidate_checks: list[str],
    check_priors: dict[str, Any],
    check_family_priors: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for check in candidate_checks:
        key = str(check or "").strip()
        if not key:
            continue
        base = check_priors.get(key, {}) if isinstance(check_priors, dict) else {}
        fam_key = _check_family(key)
        fam = check_family_priors.get(fam_key, {}) if isinstance(check_family_priors, dict) else {}

        row: dict[str, Any] = {}
        if isinstance(base, dict):
            row.update(base)

        if isinstance(fam, dict) and fam:
            fam_bias = _safe_float(fam.get("score_bias"), 0.0)
            fam_total = max(0.0, _safe_float(fam.get("evidence_total"), 0.0))
            fam_sup = max(0.0, _safe_float(fam.get("evidence_supported"), fam_total * _safe_float(fam.get("evidence_support_rate"), 0.5)))
            if row:
                row["score_bias"] = _safe_float(row.get("score_bias"), 0.0) + (0.25 * fam_bias)
                base_total = max(0.0, _safe_float(row.get("evidence_total"), 0.0))
                if base_total <= 0.0 and fam_total > 0.0:
                    row["evidence_total"] = 0.5 * fam_total
                    row["evidence_supported"] = 0.5 * fam_sup
                    row["evidence_support_rate"] = round((fam_sup / fam_total), 6)
                row.setdefault("source", "auto_refine_v1+family")
            else:
                # Family-level fallback lets non-bridge manual evidence steer ranking.
                row["score_bias"] = 0.7 * fam_bias
                row["evidence_total"] = 0.7 * fam_total
                row["evidence_supported"] = 0.7 * fam_sup
                if fam_total > 0.0:
                    row["evidence_support_rate"] = round((fam_sup / fam_total), 6)
                row["source"] = "family_fallback_v1"
            row["check_family"] = fam_key

        if row:
            out[key] = row

    return out


def _check_posterior(
    *,
    check: str,
    history_check_stats: dict[str, dict[str, float]],
    check_priors: dict[str, Any],
    scoring_cfg: dict[str, float],
) -> dict[str, float]:
    hist = history_check_stats.get(check, {}) if isinstance(history_check_stats, dict) else {}
    hist_rate = _safe_float(hist.get("support_rate"), 0.5)
    hist_total = max(0.0, _safe_float(hist.get("total"), 0.0))
    hist_supported = _clamp(hist_rate, 0.0, 1.0) * hist_total

    cp = check_priors.get(check, {}) if isinstance(check_priors, dict) else {}
    prior_bias = _safe_float(cp.get("score_bias"), 0.0) if isinstance(cp, dict) else 0.0
    prior_total_raw = max(0.0, _safe_float(cp.get("evidence_total"), 0.0)) if isinstance(cp, dict) else 0.0
    prior_supported_raw = _safe_float(cp.get("evidence_supported"), 0.0) if isinstance(cp, dict) else 0.0
    if prior_total_raw <= 0.0 and isinstance(cp, dict):
        prior_rate_hint = cp.get("evidence_support_rate")
        if isinstance(prior_rate_hint, (int, float)):
            prior_total_raw = 1.0
            prior_supported_raw = _clamp(_safe_float(prior_rate_hint, 0.5), 0.0, 1.0)

    prior_rate = _clamp((prior_supported_raw / prior_total_raw), 0.0, 1.0) if prior_total_raw > 0.0 else 0.5
    prior_weight = max(0.0, _safe_float(scoring_cfg.get("prior_evidence_weight"), 0.5))
    eff_prior_total = prior_total_raw * prior_weight
    eff_prior_supported = prior_rate * eff_prior_total

    pseudo = max(0.01, _safe_float(scoring_cfg.get("pseudo_count"), 1.0))
    alpha = pseudo + hist_supported + eff_prior_supported
    beta = pseudo + max(0.0, hist_total - hist_supported) + max(0.0, eff_prior_total - eff_prior_supported)

    total = max(1e-9, alpha + beta)
    mean = alpha / total
    variance = (alpha * beta) / (total * total * (total + 1.0))
    std = math.sqrt(max(0.0, variance))
    entropy = _binary_entropy(mean)
    info_gain = entropy * std
    rel_scale = max(1.0, _safe_float(scoring_cfg.get("reliability_scale"), 32.0))
    reliability = 1.0 - math.exp(-total / rel_scale)

    return {
        "posterior_mean": mean,
        "posterior_std": std,
        "posterior_entropy": entropy,
        "information_gain": info_gain,
        "effective_total": total,
        "prior_bias": prior_bias,
        "reliability": reliability,
        "hist_total": hist_total,
    }


def _normalize_backend_scores(base_rows: list[dict[str, Any]]) -> dict[str, float]:
    vals = [float(row.get("rank_score", 0.0)) for row in base_rows if isinstance(row, dict)]
    if not vals:
        return {}
    lo = min(vals)
    hi = max(vals)
    denom = max(1e-9, hi - lo)
    out: dict[str, float] = {}
    for row in base_rows:
        if not isinstance(row, dict):
            continue
        check = str(row.get("check", "")).strip()
        if not check:
            continue
        s = float(row.get("rank_score", 0.0))
        out[check] = (s - lo) / denom
    return out


def _advanced_rank_rows(
    *,
    candidate_checks: list[str],
    avoid_checks: set[str],
    preferred_set: set[str],
    history_check_stats: dict[str, dict[str, float]],
    check_priors: dict[str, Any],
    cfg: dict[str, Any],
    base_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    scoring_cfg = _get_scoring_cfg(cfg)
    pref_bonus_value = _safe_float(scoring_cfg.get("preference_bonus"), 0.03)
    pos_bonus_w = _safe_float(scoring_cfg.get("position_bonus_weight"), 0.01)
    backend_w = _safe_float(scoring_cfg.get("backend_score_weight"), 0.14)

    backend_norm = _normalize_backend_scores(base_rows)
    out: list[dict[str, Any]] = []
    for ix, check in enumerate(candidate_checks):
        if check in avoid_checks:
            continue
        stats = _check_posterior(
            check=check,
            history_check_stats=history_check_stats,
            check_priors=check_priors if isinstance(check_priors, dict) else {},
            scoring_cfg=scoring_cfg,
        )

        p = float(stats["posterior_mean"])
        std = float(stats["posterior_std"])
        info = float(stats["information_gain"])
        reliability = float(stats["reliability"])
        prior_bias = float(stats["prior_bias"])

        pref_bonus = pref_bonus_value if check in preferred_set else 0.0
        pos_bonus = pos_bonus_w * float(max(0, len(candidate_checks) - ix))
        backend_bonus = backend_w * float(backend_norm.get(check, 0.0))

        model = (
            _safe_float(scoring_cfg.get("exploitation_weight"), 0.72) * p
            + _safe_float(scoring_cfg.get("exploration_weight"), 0.22) * info
            + _safe_float(scoring_cfg.get("uncertainty_weight"), 0.08) * std
            + _safe_float(scoring_cfg.get("reliability_weight"), 0.12) * reliability * (p - 0.5)
            - _safe_float(scoring_cfg.get("uncertainty_penalty_weight"), 0.06) * max(0.0, p - 0.5) * std
        )

        rank_score = model + prior_bias + pref_bonus + pos_bonus + backend_bonus
        out.append(
            {
                "check": check,
                "rank_score": rank_score,
                "support_rate": p,
                "support_total": max(0, _safe_int(round(float(stats["effective_total"]), 0), 0)),
                "prior_bias": prior_bias,
                "components": {
                    "posterior_mean": p,
                    "posterior_std": std,
                    "information_gain": info,
                    "reliability": reliability,
                    "prior_bias": prior_bias,
                    "preferred_bonus": pref_bonus,
                    "position_bonus": pos_bonus,
                    "backend_bonus": backend_bonus,
                },
            }
        )

    out.sort(key=lambda row: (-float(row.get("rank_score", 0.0)), str(row.get("check", ""))))
    return out


def _rank_checks_python(
    *,
    candidate_checks: list[str],
    avoid_checks: set[str],
    preferred_set: set[str],
    history_check_stats: dict[str, dict[str, float]],
    check_priors: dict[str, Any],
    cfg: dict[str, Any],
) -> list[dict[str, Any]]:
    # Seed ranking used as backend signal; final ranking is done by _advanced_rank_rows.
    scoring_cfg = _get_scoring_cfg(cfg)
    pref_bonus = _safe_float(scoring_cfg.get("preference_bonus"), 0.03)
    pos_bonus_w = _safe_float(scoring_cfg.get("position_bonus_weight"), 0.01)

    ranked_rows: list[dict[str, Any]] = []
    for ix, check in enumerate(candidate_checks):
        if check in avoid_checks:
            continue
        hist = history_check_stats.get(check, {}) if isinstance(history_check_stats, dict) else {}
        support_rate = hist.get("support_rate")
        support_rate_f = _safe_float(support_rate, 0.5) if isinstance(support_rate, (int, float)) else 0.5
        support_total = _safe_int(hist.get("total"), 0)
        confidence = min(1.0, max(0.0, float(support_total) / 12.0))
        check_prior = check_priors.get(check, {}) if isinstance(check_priors, dict) else {}
        prior_bias = _safe_float(check_prior.get("score_bias"), 0.0) if isinstance(check_prior, dict) else 0.0
        pref_b = pref_bonus if check in preferred_set else 0.0
        rank_score = support_rate_f + (0.1 * confidence) + prior_bias + pref_b + (pos_bonus_w * float(max(0, len(candidate_checks) - ix)))
        ranked_rows.append(
            {
                "check": check,
                "rank_score": rank_score,
                "support_rate": support_rate_f,
                "support_total": support_total,
                "prior_bias": prior_bias,
            }
        )
    ranked_rows.sort(key=lambda row: (-float(row.get("rank_score", 0.0)), str(row.get("check", ""))))
    return ranked_rows


def _resolve_backend(*, backend: str, kb: dict[str, Any]) -> str:
    req = str(backend or "").strip().lower()
    if req in {"python", "prolog", "souffle", "off"}:
        return req
    engine = kb.get("engine", {}) if isinstance(kb, dict) else {}
    kb_backend = str(engine.get("backend", "auto")).strip().lower() if isinstance(engine, dict) else "auto"
    if kb_backend in {"python", "prolog", "souffle", "off"}:
        return kb_backend
    return "auto"


def _resolve_binary(binary: str) -> str | None:
    b = str(binary or "").strip()
    if not b:
        return None
    if Path(b).is_absolute():
        if Path(b).exists():
            return b
        return None
    return shutil.which(b)


def _rank_checks_prolog(
    *,
    candidate_checks: list[str],
    avoid_checks: set[str],
    preferred_set: set[str],
    history_check_stats: dict[str, dict[str, float]],
    check_priors: dict[str, Any],
    kb: dict[str, Any],
) -> tuple[list[dict[str, Any]] | None, str | None]:
    engine = kb.get("engine", {}) if isinstance(kb, dict) else {}
    prolog_cfg = engine.get("prolog", {}) if isinstance(engine, dict) else {}
    prolog_bin = str(prolog_cfg.get("binary", "swipl")).strip() or "swipl"
    timeout_s = max(0.2, _safe_float(prolog_cfg.get("timeout_s"), 2.0))
    fallback_scoring = _get_scoring_cfg(kb)
    preferred_bonus = _safe_float(prolog_cfg.get("preferred_bonus"), _safe_float(fallback_scoring.get("preference_bonus"), 0.03))

    resolved_bin = _resolve_binary(prolog_bin)
    if not resolved_bin:
        return None, f"prolog_binary_missing:{prolog_bin}"

    check_to_id: dict[str, int] = {}
    id_to_check: dict[int, str] = {}
    for ix, check in enumerate(candidate_checks):
        cid = ix + 1
        check_to_id[check] = cid
        id_to_check[cid] = check

    fact_lines: list[str] = []
    for ix, check in enumerate(candidate_checks):
        cid = int(check_to_id[check])
        fact_lines.append(f"check_option({cid}).")
        if check in avoid_checks:
            fact_lines.append(f"avoid_check({cid}).")
        if check in preferred_set:
            fact_lines.append(f"preferred_check({cid}).")
        hist = history_check_stats.get(check, {}) if isinstance(history_check_stats, dict) else {}
        support_rate = _safe_float(hist.get("support_rate"), 0.5)
        support_total = max(0, _safe_int(hist.get("total"), 0))
        check_prior = check_priors.get(check, {}) if isinstance(check_priors, dict) else {}
        prior_bias = _safe_float(check_prior.get("score_bias"), 0.0) if isinstance(check_prior, dict) else 0.0
        fact_lines.append(f"hist({cid}, {support_rate:.16f}, {support_total}).")
        fact_lines.append(f"prior_bias({cid}, {prior_bias:.16f}).")
        fact_lines.append(f"position({cid}, {ix + 1}).")

    prolog_program = "\n".join(
        [
            ":- dynamic check_option/1.",
            ":- dynamic avoid_check/1.",
            ":- dynamic preferred_check/1.",
            ":- dynamic hist/3.",
            ":- dynamic prior_bias/2.",
            ":- dynamic position/2.",
            "",
        ]
        + fact_lines
        + [
            "",
            "confidence(Tot, Conf) :-",
            "  Raw is Tot / 12.0,",
            "  (Raw < 1.0 -> Conf = Raw ; Conf = 1.0).",
            "",
            "position_bonus(Pos, Bonus) :-",
            "  Raw is 64 - Pos,",
            "  (Raw > 0 -> Bonus is 0.01 * Raw ; Bonus = 0.0).",
            "",
            f"preferred_bonus(Id, Bonus) :- preferred_check(Id), !, Bonus is {preferred_bonus:.16f}.",
            "preferred_bonus(_, 0.0).",
            "",
            "score(Id, Score, Rate, Tot, Bias) :-",
            "  check_option(Id),",
            "  \\+ avoid_check(Id),",
            "  hist(Id, Rate, Tot),",
            "  prior_bias(Id, Bias),",
            "  position(Id, Pos),",
            "  confidence(Tot, Conf),",
            "  position_bonus(Pos, PosB),",
            "  preferred_bonus(Id, PrefB),",
            "  Score is Rate + (0.1 * Conf) + Bias + PosB + PrefB.",
            "",
            "emit(Id, Score, Rate, Tot, Bias) :-",
            "  format('scored\\t~w\\t~16f\\t~16f\\t~w\\t~16f~n', [Id, Score, Rate, Tot, Bias]).",
            "",
            "main :-",
            "  forall(score(Id, Score, Rate, Tot, Bias), emit(Id, Score, Rate, Tot, Bias)).",
        ]
    )

    try:
        with tempfile.TemporaryDirectory(prefix="krr_prolog_") as tmp_dir:
            prog = Path(tmp_dir) / "krr_rank.pl"
            prog.write_text(prolog_program, encoding="utf-8")
            proc = subprocess.run(
                [str(resolved_bin), "-q", "-f", str(prog), "-g", "main", "-t", "halt"],
                capture_output=True,
                text=True,
                timeout=timeout_s,
                check=False,
            )
    except subprocess.TimeoutExpired:
        return None, f"prolog_timeout:{timeout_s:.2f}s"
    except Exception as exc:
        return None, f"prolog_exec_error:{type(exc).__name__}"

    if int(proc.returncode) != 0:
        stderr = str(proc.stderr or "").strip()
        short_err = stderr.splitlines()[0] if stderr else f"code={proc.returncode}"
        return None, f"prolog_failed:{short_err}"

    ranked_rows: list[dict[str, Any]] = []
    for raw_line in str(proc.stdout or "").splitlines():
        line = raw_line.strip()
        if not line.startswith("scored\t"):
            continue
        parts = line.split("\t")
        if len(parts) != 6:
            continue
        cid = _safe_int(parts[1], 0)
        check = id_to_check.get(cid)
        if not check:
            continue
        ranked_rows.append(
            {
                "check": check,
                "rank_score": _safe_float(parts[2], 0.0),
                "support_rate": _safe_float(parts[3], 0.5),
                "support_total": max(0, _safe_int(parts[4], 0)),
                "prior_bias": _safe_float(parts[5], 0.0),
            }
        )
    ranked_rows.sort(key=lambda row: (-float(row.get("rank_score", 0.0)), str(row.get("check", ""))))
    if not ranked_rows:
        return None, "prolog_empty_output"
    return ranked_rows, None


def _rank_checks_souffle(
    *,
    candidate_checks: list[str],
    avoid_checks: set[str],
    preferred_set: set[str],
    history_check_stats: dict[str, dict[str, float]],
    check_priors: dict[str, Any],
    kb: dict[str, Any],
) -> tuple[list[dict[str, Any]] | None, str | None]:
    engine = kb.get("engine", {}) if isinstance(kb, dict) else {}
    souffle_cfg = engine.get("souffle", {}) if isinstance(engine, dict) else {}
    souffle_bin = str(souffle_cfg.get("binary", "souffle")).strip() or "souffle"
    timeout_s = max(0.2, _safe_float(souffle_cfg.get("timeout_s"), 2.0))
    fallback_scoring = _get_scoring_cfg(kb)
    preferred_bonus = _safe_float(souffle_cfg.get("preferred_bonus"), _safe_float(fallback_scoring.get("preference_bonus"), 0.03))

    resolved_bin = _resolve_binary(souffle_bin)
    if not resolved_bin:
        return None, f"souffle_binary_missing:{souffle_bin}"

    check_to_id: dict[str, int] = {}
    id_to_check: dict[int, str] = {}
    for ix, check in enumerate(candidate_checks):
        cid = ix + 1
        check_to_id[check] = cid
        id_to_check[cid] = check

    program = "\n".join(
        [
            ".decl check_option(id:number)",
            ".decl avoid_check(id:number)",
            ".decl preferred_check(id:number)",
            ".decl hist(id:number, rate:float, total:number)",
            ".decl prior_bias(id:number, bias:float)",
            ".decl position(id:number, pos:number)",
            ".decl confidence(id:number, c:float)",
            ".decl position_bonus(id:number, b:float)",
            ".decl preferred_bonus(id:number, b:float)",
            ".decl scored(id:number, score:float, rate:float, total:number, bias:float)",
            "",
            ".input check_option",
            ".input avoid_check",
            ".input preferred_check",
            ".input hist",
            ".input prior_bias",
            ".input position",
            "",
            ".output scored(delimiter=\"\\t\")",
            "",
            "confidence(id, c) :-",
            "  hist(id, _, total),",
            "  c = to_float(total) / 12.0,",
            "  c <= 1.0.",
            "confidence(id, 1.0) :-",
            "  hist(id, _, total),",
            "  to_float(total) / 12.0 > 1.0.",
            "",
            "position_bonus(id, b) :-",
            "  position(id, pos),",
            "  pos < 64,",
            "  b = 0.01 * to_float(64 - pos).",
            "position_bonus(id, 0.0) :-",
            "  position(id, pos),",
            "  pos >= 64.",
            "",
            f"preferred_bonus(id, {preferred_bonus:.16f}) :- preferred_check(id).",
            "preferred_bonus(id, 0.0) :- check_option(id), !preferred_check(id).",
            "",
            "scored(id, score, rate, total, bias) :-",
            "  check_option(id),",
            "  !avoid_check(id),",
            "  hist(id, rate, total),",
            "  prior_bias(id, bias),",
            "  confidence(id, conf),",
            "  position_bonus(id, posb),",
            "  preferred_bonus(id, prefb),",
            "  score = rate + (0.1 * conf) + bias + posb + prefb.",
            "",
        ]
    )

    try:
        with tempfile.TemporaryDirectory(prefix="krr_souffle_") as tmp_dir:
            tmp = Path(tmp_dir)
            facts_dir = tmp / "facts"
            out_dir = tmp / "out"
            facts_dir.mkdir(parents=True, exist_ok=True)
            out_dir.mkdir(parents=True, exist_ok=True)
            program_path = tmp / "krr_rank.dl"
            program_path.write_text(program, encoding="utf-8")

            def _write_facts(name: str, rows: list[tuple[Any, ...]]) -> None:
                path = facts_dir / f"{name}.facts"
                with path.open("w", encoding="utf-8") as fh:
                    for row in rows:
                        fh.write("\t".join(str(x) for x in row) + "\n")

            check_rows: list[tuple[int]] = []
            avoid_rows: list[tuple[int]] = []
            preferred_rows: list[tuple[int]] = []
            hist_rows: list[tuple[int, float, int]] = []
            prior_rows: list[tuple[int, float]] = []
            pos_rows: list[tuple[int, int]] = []

            for ix, check in enumerate(candidate_checks):
                cid = int(check_to_id[check])
                check_rows.append((cid,))
                if check in avoid_checks:
                    avoid_rows.append((cid,))
                if check in preferred_set:
                    preferred_rows.append((cid,))
                hist = history_check_stats.get(check, {}) if isinstance(history_check_stats, dict) else {}
                support_rate = _safe_float(hist.get("support_rate"), 0.5)
                support_total = max(0, _safe_int(hist.get("total"), 0))
                check_prior = check_priors.get(check, {}) if isinstance(check_priors, dict) else {}
                prior_bias = _safe_float(check_prior.get("score_bias"), 0.0) if isinstance(check_prior, dict) else 0.0
                hist_rows.append((cid, support_rate, support_total))
                prior_rows.append((cid, prior_bias))
                pos_rows.append((cid, ix + 1))

            _write_facts("check_option", check_rows)
            _write_facts("avoid_check", avoid_rows)
            _write_facts("preferred_check", preferred_rows)
            _write_facts("hist", hist_rows)
            _write_facts("prior_bias", prior_rows)
            _write_facts("position", pos_rows)

            proc = subprocess.run(
                [str(resolved_bin), "-F", str(facts_dir), "-D", str(out_dir), str(program_path)],
                capture_output=True,
                text=True,
                timeout=timeout_s,
                check=False,
            )

            if int(proc.returncode) != 0:
                stderr = str(proc.stderr or "").strip()
                short_err = stderr.splitlines()[0] if stderr else f"code={proc.returncode}"
                return None, f"souffle_failed:{short_err}"

            scored_path = out_dir / "scored.csv"
            if not scored_path.exists():
                return None, "souffle_empty_output"
            lines = scored_path.read_text(encoding="utf-8").splitlines()

    except subprocess.TimeoutExpired:
        return None, f"souffle_timeout:{timeout_s:.2f}s"
    except Exception as exc:
        return None, f"souffle_exec_error:{type(exc).__name__}"

    ranked_rows: list[dict[str, Any]] = []
    for raw in lines:
        line = str(raw or "").strip()
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) != 5:
            parts = line.split(",")
        if len(parts) != 5:
            continue
        cid = _safe_int(parts[0], 0)
        check = id_to_check.get(cid)
        if not check:
            continue
        ranked_rows.append(
            {
                "check": check,
                "rank_score": _safe_float(parts[1], 0.0),
                "support_rate": _safe_float(parts[2], 0.5),
                "support_total": max(0, _safe_int(parts[3], 0)),
                "prior_bias": _safe_float(parts[4], 0.0),
            }
        )
    ranked_rows.sort(key=lambda row: (-float(row.get("rank_score", 0.0)), str(row.get("check", ""))))
    if not ranked_rows:
        return None, "souffle_empty_rows"
    return ranked_rows, None


def advise_candidate_krr(
    *,
    operator_id: str,
    schema: str,
    semantic_signature: str,
    check_options: list[str],
    history_check_stats: dict[str, dict[str, float]],
    kb: dict[str, Any] | None,
    backend: str = "auto",
) -> dict[str, Any]:
    cfg = kb if isinstance(kb, dict) else {}
    operator_priors = cfg.get("operator_priors", {})
    op_prior = operator_priors.get(operator_id, {}) if isinstance(operator_priors, dict) else {}
    check_priors = cfg.get("check_priors", {})
    check_family_priors = cfg.get("check_family_priors", {})

    semantic_tokens, semantic_predicates = _extract_semantic_features(
        schema=str(schema or "").strip(),
        semantic_signature=str(semantic_signature or "").strip(),
    )

    preferred_checks: list[str] = [str(x).strip() for x in list(op_prior.get("check_preferences", []) or [])]
    avoid_checks: set[str] = {str(x).strip() for x in list(op_prior.get("avoid_checks", []) or []) if str(x).strip()}
    score_delta = _safe_float(op_prior.get("score_bias"), 0.0)
    min_speedup_override = op_prior.get("min_speedup_override")
    if min_speedup_override is not None:
        min_speedup_override = _safe_float(min_speedup_override, 1.0)

    rule_hits: list[dict[str, Any]] = []
    semantic_rules = cfg.get("semantic_rules", [])
    if isinstance(semantic_rules, list):
        for rule in semantic_rules:
            if not isinstance(rule, dict):
                continue
            if not _match_rule(
                rule,
                operator_id=operator_id,
                schema=schema,
                semantic_signature=semantic_signature,
                semantic_tokens=semantic_tokens,
                semantic_predicates=semantic_predicates,
            ):
                continue
            preferred_checks.extend(str(x).strip() for x in list(rule.get("then_prefer_checks", []) or []))
            avoid_checks.update(str(x).strip() for x in list(rule.get("then_avoid_checks", []) or []) if str(x).strip())
            score_delta += _safe_float(rule.get("score_bias"), 0.0)
            rule_floor = rule.get("min_speedup_override")
            if rule_floor is not None:
                floor_v = _safe_float(rule_floor, 1.0)
                if min_speedup_override is None:
                    min_speedup_override = floor_v
                else:
                    min_speedup_override = min(min_speedup_override, floor_v)
            rule_hits.append(
                {
                    "name": str(rule.get("name", "unnamed_rule")),
                    "score_bias": _safe_float(rule.get("score_bias"), 0.0),
                }
            )

    candidate_checks = _uniq(preferred_checks + list(check_options))
    effective_check_priors = _expand_check_priors(
        candidate_checks=candidate_checks,
        check_priors=check_priors if isinstance(check_priors, dict) else {},
        check_family_priors=check_family_priors if isinstance(check_family_priors, dict) else {},
    )
    preferred_set = {str(x).strip() for x in preferred_checks if str(x).strip()}
    backend_requested = _resolve_backend(backend=backend, kb=cfg)
    backend_used = "none"
    backend_fallback_reason: str | None = None

    if not candidate_checks:
        return {
            "preferred_checks": [],
            "score_delta": float(score_delta),
            "min_speedup_override": min_speedup_override,
            "rule_hits": rule_hits,
            "confidence": 0.0,
            "explain": ["no candidate checks available"],
            "semantic_tokens": semantic_tokens,
            "semantic_predicates": sorted(semantic_predicates),
            "backend_requested": backend_requested,
            "backend_used": backend_used,
            "backend_fallback_reason": backend_fallback_reason,
        }

    ranked_rows: list[dict[str, Any]] = []
    if backend_requested == "off":
        backend_used = "none"
    elif backend_requested == "python":
        ranked_rows = _rank_checks_python(
            candidate_checks=candidate_checks,
            avoid_checks=avoid_checks,
            preferred_set=preferred_set,
            history_check_stats=history_check_stats,
            check_priors=effective_check_priors,
            cfg=cfg,
        )
        backend_used = "python"
    elif backend_requested == "prolog":
        prolog_rows, prolog_reason = _rank_checks_prolog(
            candidate_checks=candidate_checks,
            avoid_checks=avoid_checks,
            preferred_set=preferred_set,
            history_check_stats=history_check_stats,
            check_priors=effective_check_priors,
            kb=cfg,
        )
        if prolog_rows is not None and prolog_rows:
            ranked_rows = prolog_rows
            backend_used = "prolog"
        else:
            ranked_rows = _rank_checks_python(
                candidate_checks=candidate_checks,
                avoid_checks=avoid_checks,
                preferred_set=preferred_set,
                history_check_stats=history_check_stats,
                check_priors=effective_check_priors,
                cfg=cfg,
            )
            backend_used = "python"
            backend_fallback_reason = prolog_reason or "prolog_unavailable"
    elif backend_requested == "souffle":
        souffle_rows, souffle_reason = _rank_checks_souffle(
            candidate_checks=candidate_checks,
            avoid_checks=avoid_checks,
            preferred_set=preferred_set,
            history_check_stats=history_check_stats,
            check_priors=effective_check_priors,
            kb=cfg,
        )
        if souffle_rows is not None and souffle_rows:
            ranked_rows = souffle_rows
            backend_used = "souffle"
        else:
            ranked_rows = _rank_checks_python(
                candidate_checks=candidate_checks,
                avoid_checks=avoid_checks,
                preferred_set=preferred_set,
                history_check_stats=history_check_stats,
                check_priors=effective_check_priors,
                cfg=cfg,
            )
            backend_used = "python"
            backend_fallback_reason = souffle_reason or "souffle_unavailable"
    else:
        prolog_rows, prolog_reason = _rank_checks_prolog(
            candidate_checks=candidate_checks,
            avoid_checks=avoid_checks,
            preferred_set=preferred_set,
            history_check_stats=history_check_stats,
            check_priors=effective_check_priors,
            kb=cfg,
        )
        if prolog_rows is not None and prolog_rows:
            ranked_rows = prolog_rows
            backend_used = "prolog"
        else:
            souffle_rows, souffle_reason = _rank_checks_souffle(
                candidate_checks=candidate_checks,
                avoid_checks=avoid_checks,
                preferred_set=preferred_set,
                history_check_stats=history_check_stats,
                check_priors=effective_check_priors,
                kb=cfg,
            )
            if souffle_rows is not None and souffle_rows:
                ranked_rows = souffle_rows
                backend_used = "souffle"
                backend_fallback_reason = prolog_reason or None
            else:
                ranked_rows = _rank_checks_python(
                    candidate_checks=candidate_checks,
                    avoid_checks=avoid_checks,
                    preferred_set=preferred_set,
                    history_check_stats=history_check_stats,
                    check_priors=effective_check_priors,
                    cfg=cfg,
                )
                backend_used = "python"
                chain = []
                if prolog_reason:
                    chain.append(prolog_reason)
                if souffle_reason:
                    chain.append(souffle_reason)
                backend_fallback_reason = ";".join(chain) if chain else "symbolic_unavailable"

    # Bayesian + information-gain reranking is applied after backend scoring.
    if ranked_rows:
        ranked_rows = _advanced_rank_rows(
            candidate_checks=candidate_checks,
            avoid_checks=avoid_checks,
            preferred_set=preferred_set,
            history_check_stats=history_check_stats,
            check_priors=effective_check_priors,
            cfg=cfg,
            base_rows=ranked_rows,
        )

    ranked_checks = [str(row.get("check", "")) for row in ranked_rows if str(row.get("check", "")).strip()]
    top_row = ranked_rows[0] if ranked_rows else {}
    top_support = float(top_row.get("support_rate", 0.5)) if isinstance(top_row, dict) else 0.5
    top_comp = top_row.get("components", {}) if isinstance(top_row, dict) else {}
    top_reliability = _safe_float(top_comp.get("reliability"), 0.0) if isinstance(top_comp, dict) else 0.0
    top_info = _safe_float(top_comp.get("information_gain"), 0.0) if isinstance(top_comp, dict) else 0.0
    krr_confidence = _clamp((0.65 * top_support) + (0.35 * top_reliability), 0.0, 1.0)

    explain = [
        f"operator={_safe_token(operator_id)} schema={_safe_token(schema)}",
        f"semantic_sig={_safe_token(semantic_signature, max_len=96)}",
        f"top_check={_safe_token(ranked_checks[0] if ranked_checks else 'none')}",
        f"backend={_safe_token(backend_used)}",
        f"predicates={','.join(sorted(_safe_token(x,32) for x in semantic_predicates)[:6]) or 'none'}",
    ]
    if rule_hits:
        explain.append("rules=" + ",".join(str(x.get("name", "")) for x in rule_hits if str(x.get("name", "")).strip()))
    if backend_fallback_reason:
        explain.append(f"fallback={_safe_token(backend_fallback_reason, max_len=96)}")
    if ranked_rows:
        explain.append(f"top_p={top_support:.4f}")
        explain.append(f"top_info={top_info:.4f}")

    return {
        "preferred_checks": ranked_checks,
        "score_delta": float(score_delta),
        "min_speedup_override": min_speedup_override,
        "rule_hits": rule_hits,
        "confidence": krr_confidence,
        "predicted_support_rate": top_support,
        "predicted_information_gain": top_info,
        "semantic_tokens": semantic_tokens,
        "semantic_predicates": sorted(semantic_predicates),
        "top_components": top_comp if isinstance(top_comp, dict) else {},
        "explain": explain,
        "backend_requested": backend_requested,
        "backend_used": backend_used,
        "backend_fallback_reason": backend_fallback_reason,
    }


def advise_pack_krr(
    *,
    assignments: list[dict[str, Any]],
    score_rows: dict[str, dict[str, Any]],
    history_check_stats: dict[str, dict[str, float]],
    kb: dict[str, Any] | None,
    default_check_options: dict[str, list[str]],
    backend: str = "auto",
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for assignment in assignments:
        if not isinstance(assignment, dict):
            continue
        cid = str(assignment.get("candidate_id", "")).strip()
        if not cid:
            continue
        score = score_rows.get(cid, {})
        op = str(assignment.get("operator_id", "")).strip()
        schema = str(score.get("schema", "")).strip()
        semantic_sig = str(score.get("semantic_signature") or assignment.get("semantic_signature") or "").strip()
        check_options = list(default_check_options.get(op, []))
        advice = advise_candidate_krr(
            operator_id=op,
            schema=schema,
            semantic_signature=semantic_sig,
            check_options=check_options,
            history_check_stats=history_check_stats,
            kb=kb,
            backend=backend,
        )
        rows.append(
            {
                "candidate_id": cid,
                "operator_id": op,
                "schema": schema,
                "semantic_signature": semantic_sig,
                "advice": advice,
            }
        )
    return {
        "schema": "zenodex/krr-pack-advice/v1",
        "rows": rows,
        "count": len(rows),
    }
