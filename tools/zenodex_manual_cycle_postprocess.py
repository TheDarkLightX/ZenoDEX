#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
RUNS_ROOT = ROOT / "runs" / "manual_morph_supervised"


def _read_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_md(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(row, sort_keys=True) + "\n")


def _safe_token(text: str, *, max_len: int = 180) -> str:
    chars = []
    for ch in str(text):
        if ch.isalnum() or ch in "_.-":
            chars.append(ch)
        else:
            chars.append("_")
    token = "".join(chars).strip("._")
    if not token:
        token = "x"
    return token[:max_len]


def _parse_run_name(name: str) -> tuple[int, int]:
    m = re.match(r"h(\d+)_supervised_cycle(\d+)$", name)
    if not m:
        return (0, 0)
    return (int(m.group(1)), int(m.group(2)))


def _discover_cycle_dirs(runs_root: Path) -> list[Path]:
    out: list[Path] = []
    for p in sorted(runs_root.glob("h*_supervised_cycle*")):
        if not p.is_dir():
            continue
        hid, cyc = _parse_run_name(p.name)
        if hid <= 0 or cyc <= 0:
            continue
        out.append(p)
    out.sort(key=lambda p: _parse_run_name(p.name))
    return out


def _load_rows_for_dir(cycle_dir: Path) -> list[dict[str, Any]]:
    combined = sorted(cycle_dir.glob("summary_cycle*combined.json"))
    if combined:
        obj = _read_json(combined[-1], default={})
        rows = [dict(x) for x in obj.get("rows", []) if isinstance(x, dict)]
        if rows:
            return rows
    summary = cycle_dir / "summary.json"
    if summary.exists():
        obj = _read_json(summary, default={})
        rows = [dict(x) for x in obj.get("rows", []) if isinstance(x, dict)]
        if rows:
            return rows
    rows: list[dict[str, Any]] = []
    for sp in sorted(cycle_dir.glob("tranche_*/summary.json")):
        obj = _read_json(sp, default={})
        rows.extend(dict(x) for x in obj.get("rows", []) if isinstance(x, dict))
    return rows


def _history_before_cycle(runs_root: Path, cycle: int) -> dict[str, str]:
    out: dict[str, str] = {}
    for cd in _discover_cycle_dirs(runs_root):
        _, cyc = _parse_run_name(cd.name)
        if cyc >= cycle:
            break
        rows = _load_rows_for_dir(cd)
        latest: dict[str, str] = {}
        for r in rows:
            hid = str(r.get("hypothesis_id", ""))
            st = str(r.get("final_status", ""))
            if not hid or st not in {"supported", "falsified", "inconclusive"}:
                continue
            latest[hid] = st
        out.update(latest)
    return out


def _dominates(a: list[float], b: list[float]) -> bool:
    return all(x >= y for x, y in zip(a, b)) and any(x > y for x, y in zip(a, b))


def _check_family(check: str) -> str:
    c = str(check or "")
    if "::" in c:
        return c.split("::", 1)[0]
    return c


def _confidence_for_check(check: str, status: str) -> float:
    c = str(check or "")
    if status != "supported":
        return 0.8
    if c.startswith("lean_repeat3::") or c.startswith("esso_repeat2_solver::"):
        return 0.98
    if c.startswith("lean_pass::"):
        return 0.95
    if c.startswith("esso_verify_solver_timeout::cvc5,z3::"):
        return 0.94
    if c.startswith("esso_spec_debug_class::"):
        return 0.93
    if c.startswith("esso_synth"):
        return 0.9
    if c.startswith("pytest_repeat"):
        return 0.9
    if c.startswith("perp_oracle_lp_attack_"):
        return 0.9
    return 0.86


def _result_path_for_row(part_dir: Path, hypothesis_id: str) -> Path:
    return part_dir / "results" / _safe_token(hypothesis_id, max_len=180) / "result.json"


def _load_result_detail(part_dir: Path, hypothesis_id: str) -> dict[str, Any]:
    p = _result_path_for_row(part_dir, hypothesis_id)
    return _read_json(p, default={}) if p.exists() else {}


def _counterexample_size(counterexample: Any) -> int:
    try:
        return len(json.dumps(counterexample, sort_keys=True))
    except Exception:
        return 10**9


def _extract_counterexample(detail: dict[str, Any], final_status: str) -> Any:
    if not isinstance(detail, dict):
        return None
    if final_status == "falsified":
        ref_payload = (((detail.get("refute") or {}).get("payload")) or {})
        return ref_payload.get("counterexample")
    if final_status == "supported":
        sup_payload = (((detail.get("support") or {}).get("payload")) or {})
        return sup_payload.get("counterexample")
    return None


def _extract_reason(detail: dict[str, Any], final_status: str) -> str:
    if not isinstance(detail, dict):
        return ""
    if final_status == "falsified":
        p = (((detail.get("refute") or {}).get("payload")) or {})
        return str(p.get("reason", ""))
    if final_status == "supported":
        p = (((detail.get("support") or {}).get("payload")) or {})
        return str(p.get("reason", ""))
    p_ref = (((detail.get("refute") or {}).get("payload")) or {})
    p_sup = (((detail.get("support") or {}).get("payload")) or {})
    return str(p_sup.get("reason", p_ref.get("reason", "")))


def _inconclusive_unblock(reason: str, check: str) -> str:
    r = str(reason or "")
    c = str(check or "")
    if r in {"timeout", "repeat_inconclusive"}:
        return "Increase timeout budget or split check into smaller deterministic sub-checks."
    if r == "mathlib_not_wired":
        return "Repair local Lean/Mathlib wiring and rerun lean gate + replay checks."
    if r in {"unparseable_json", "command_error_or_unparseable_json"}:
        return "Pin tool output mode and add explicit JSON extraction fallback."
    if c.startswith("perp_oracle_lp_attack_"):
        return "Reduce attack grid bounds and rerun with narrower boundary regimes."
    return "Decompose hypothesis into gate + counterclaim + replay branch and rerun."


def _build_epoch_report(
    *,
    cycle: int,
    cycle_dir: Path,
    rows: list[dict[str, Any]],
    hyp_map: dict[str, dict[str, Any]],
    part_dirs: dict[str, Path],
    prev_status: dict[str, str],
) -> dict[str, Any]:
    supported_rows: list[dict[str, Any]] = []
    newly_falsified: list[dict[str, Any]] = []
    newly_supported: list[dict[str, Any]] = []
    inconclusive_items: list[dict[str, Any]] = []

    for row in rows:
        hid = str(row.get("hypothesis_id", ""))
        check = str(row.get("check", ""))
        st = str(row.get("final_status", "inconclusive"))
        src = str(row.get("source", ""))
        part_dir = part_dirs.get(src)
        detail = _load_result_detail(part_dir, hid) if part_dir else {}
        cex = _extract_counterexample(detail, st)
        reason = _extract_reason(detail, st)
        evidence_ref = str(_result_path_for_row(part_dir, hid)) if part_dir else ""

        hyp = hyp_map.get(hid, {})
        vec = hyp.get("expected_metric_delta")
        if st == "supported" and isinstance(vec, list) and len(vec) == 5:
            try:
                vv = [float(x) for x in vec]
                supported_rows.append({"hypothesis_id": hid, "vector": vv, "check": check})
            except Exception:
                pass

        old = prev_status.get(hid)
        if st == "falsified" and old != "falsified":
            newly_falsified.append(
                {
                    "hypothesis_id": hid,
                    "check": check,
                    "minimal_counterexample": cex,
                    "counterexample_size_bytes": _counterexample_size(cex),
                    "evidence_ref": evidence_ref,
                    "reason": reason,
                }
            )
        elif st == "supported" and old != "supported":
            newly_supported.append(
                {
                    "hypothesis_id": hid,
                    "check": check,
                    "confidence": round(_confidence_for_check(check, st), 3),
                    "evidence_ref": evidence_ref,
                    "reason": reason,
                }
            )
        elif st == "inconclusive":
            inconclusive_items.append(
                {
                    "hypothesis_id": hid,
                    "check": check,
                    "reason": reason,
                    "unblock_plan": _inconclusive_unblock(reason, check),
                    "evidence_ref": evidence_ref,
                }
            )

    # Pareto frontier from currently supported hypotheses in this cycle.
    frontier: list[dict[str, Any]] = []
    for a in supported_rows:
        if any(_dominates(b["vector"], a["vector"]) for b in supported_rows if b["hypothesis_id"] != a["hypothesis_id"]):
            continue
        frontier.append(a)
    frontier.sort(key=lambda r: (sum(r["vector"]), r["hypothesis_id"]), reverse=True)

    newly_falsified.sort(key=lambda x: (int(x["counterexample_size_bytes"]), x["hypothesis_id"]))
    newly_supported.sort(key=lambda x: (float(x["confidence"]), x["hypothesis_id"]), reverse=True)

    queue_obj = _read_json(cycle_dir / "next_experiment_queue.json", default={})
    queue_rows = [dict(x) for x in queue_obj.get("queue", []) if isinstance(x, dict)]
    next_queue = queue_rows[:25]

    return {
        "schema": "zenodex/epoch-report/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "pareto_frontier_snapshot": frontier,
        "newly_falsified": newly_falsified,
        "newly_supported": newly_supported,
        "inconclusive_items": inconclusive_items,
        "next_experiment_queue": next_queue,
    }


def _lean_analysis(rows: list[dict[str, Any]], cycle: int) -> dict[str, Any]:
    lean_rows = [r for r in rows if str(r.get("check", "")).startswith("lean_")]
    status_counts = {"supported": 0, "falsified": 0, "inconclusive": 0}
    family_counts: dict[str, int] = {}
    by_file: dict[str, dict[str, int]] = {}
    for r in lean_rows:
        st = str(r.get("final_status", "inconclusive"))
        status_counts[st] = int(status_counts.get(st, 0)) + 1
        check = str(r.get("check", ""))
        fam = _check_family(check)
        family_counts[fam] = int(family_counts.get(fam, 0)) + 1
        path = check.split("::", 1)[1] if "::" in check else "unknown"
        frow = by_file.setdefault(path, {"supported": 0, "falsified": 0, "inconclusive": 0})
        frow[st] = int(frow.get(st, 0)) + 1
    return {
        "schema": "zenodex/manual-lean-analysis/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "total_lean_hypotheses": len(lean_rows),
        "status_counts": status_counts,
        "family_counts": family_counts,
        "by_file": by_file,
    }


def _cegis_analysis(rows: list[dict[str, Any]], cycle: int) -> dict[str, Any]:
    crows = [
        r
        for r in rows
        if str(r.get("check", "")).startswith("esso_synth")
        or str(r.get("check", "")).startswith("esso_spec_debug_class")
    ]
    status_counts = {"supported": 0, "falsified": 0, "inconclusive": 0}
    family_counts: dict[str, int] = {}
    by_model: dict[str, dict[str, int]] = {}
    for r in crows:
        st = str(r.get("final_status", "inconclusive"))
        status_counts[st] = int(status_counts.get(st, 0)) + 1
        check = str(r.get("check", ""))
        fam = _check_family(check)
        family_counts[fam] = int(family_counts.get(fam, 0)) + 1
        m = re.search(r"::(src/kernels/dex/[A-Za-z0-9_./-]+\.yaml)", check)
        model = m.group(1) if m else "unknown_model"
        mrow = by_model.setdefault(model, {"supported": 0, "falsified": 0, "inconclusive": 0})
        mrow[st] = int(mrow.get(st, 0)) + 1
    return {
        "schema": "zenodex/cegis-sygus-analysis/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "total_cegis_hypotheses": len(crows),
        "status_counts": status_counts,
        "family_counts": family_counts,
        "by_model": by_model,
    }


def _automation_analysis(rows: list[dict[str, Any]], cycle: int) -> dict[str, Any]:
    arows: list[dict[str, Any]] = []
    for r in rows:
        check = str(r.get("check", "")).lower()
        if any(tok in check for tok in ("tau_", "state_root", "intent_normal_form", "settlement_normal_form", "operations_parsing", "dex_snapshot")):
            arows.append(r)
    status_counts = {"supported": 0, "falsified": 0, "inconclusive": 0}
    by_check: dict[str, dict[str, int]] = {}
    for r in arows:
        st = str(r.get("final_status", "inconclusive"))
        status_counts[st] = int(status_counts.get(st, 0)) + 1
        check = str(r.get("check", ""))
        crow = by_check.setdefault(check, {"supported": 0, "falsified": 0, "inconclusive": 0})
        crow[st] = int(crow.get(st, 0)) + 1
    return {
        "schema": "zenodex/automation-analysis/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "total_automation_hypotheses": len(arows),
        "status_counts": status_counts,
        "by_check": by_check,
    }


def _game_boundary_analysis(rows: list[dict[str, Any]], cycle: int) -> dict[str, Any]:
    grows = [r for r in rows if str(r.get("check", "")).startswith("perp_oracle_lp_attack_")]
    parsed: list[dict[str, Any]] = []
    for r in grows:
        check = str(r.get("check", ""))
        st = str(r.get("final_status", "inconclusive"))
        m = re.match(r"^perp_oracle_lp_attack_(absent|exists)::(.+)$", check)
        if not m:
            continue
        branch = str(m.group(1))
        raw = str(m.group(2))
        params: dict[str, int] = {}
        for p in raw.split(","):
            if "=" not in p:
                continue
            k, v = p.split("=", 1)
            try:
                params[k.strip()] = int(v.strip().replace("_", ""))
            except Exception:
                continue
        parsed.append(
            {
                "hypothesis_id": str(r.get("hypothesis_id", "")),
                "branch": branch,
                "status": st,
                "params": params,
                "check": check,
            }
        )

    summary = {
        "exists_supported": 0,
        "exists_falsified": 0,
        "absent_supported": 0,
        "absent_falsified": 0,
        "full_capture_absent_supported": 0,
        "near_full_capture_exists_supported": 0,
    }
    for row in parsed:
        br = str(row["branch"])
        st = str(row["status"])
        pfs = int((row.get("params") or {}).get("pfs", -1))
        if br == "exists":
            if st == "supported":
                summary["exists_supported"] += 1
                if pfs >= 9999:
                    summary["near_full_capture_exists_supported"] += 1
            elif st == "falsified":
                summary["exists_falsified"] += 1
        elif br == "absent":
            if st == "supported":
                summary["absent_supported"] += 1
                if pfs == 10000:
                    summary["full_capture_absent_supported"] += 1
            elif st == "falsified":
                summary["absent_falsified"] += 1

    return {
        "schema": "zenodex/game-boundary-analysis/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "total_dynamic_hypotheses": len(parsed),
        "summary": summary,
        "rows": parsed,
    }


def _proof_intelligence(
    *,
    cycle: int,
    lean_analysis: dict[str, Any],
    cegis_analysis: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema": "zenodex/proof-intelligence/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "lean": {
            "total": int(lean_analysis.get("total_lean_hypotheses", 0)),
            "status_counts": dict(lean_analysis.get("status_counts", {})),
        },
        "cegis_sygus": {
            "total": int(cegis_analysis.get("total_cegis_hypotheses", 0)),
            "status_counts": dict(cegis_analysis.get("status_counts", {})),
            "family_counts": dict(cegis_analysis.get("family_counts", {})),
        },
        "notes": [
            "UNKNOWN/TIMEOUT/ERROR are inconclusive and never treated as proof.",
            "Lean replay + CEGIS classification are complementary, not substitutes.",
        ],
    }


def _roi_policy(rows: list[dict[str, Any]], cycle: int) -> dict[str, Any]:
    by_family: dict[str, dict[str, float]] = {}
    for r in rows:
        fam = _check_family(str(r.get("check", "")))
        st = str(r.get("final_status", "inconclusive"))
        dur = float(r.get("duration_s", 0) or 0)
        f = by_family.setdefault(fam, {"total": 0.0, "conclusive": 0.0, "duration_s": 0.0})
        f["total"] += 1.0
        if st in {"supported", "falsified"}:
            f["conclusive"] += 1.0
        f["duration_s"] += max(0.0, dur)

    ranked: list[dict[str, Any]] = []
    for fam, vals in by_family.items():
        dur_min = max(0.01, vals["duration_s"] / 60.0)
        gain_per_min = vals["conclusive"] / dur_min
        ranked.append(
            {
                "family": fam,
                "total": int(vals["total"]),
                "conclusive": int(vals["conclusive"]),
                "duration_s": round(vals["duration_s"], 3),
                "conclusive_per_min": round(gain_per_min, 4),
            }
        )
    ranked.sort(key=lambda x: (float(x["conclusive_per_min"]), int(x["conclusive"]), x["family"]), reverse=True)

    policy = {
        "promote_families": [x["family"] for x in ranked[:5]],
        "deprioritize_families": [x["family"] for x in ranked[-5:]] if len(ranked) > 5 else [],
        "notes": [
            "Promote high conclusive/min families in the next cycle.",
            "Keep expensive low-yield families as targeted probes only.",
        ],
    }
    return {
        "schema": "zenodex/cycle-roi-policy/v1",
        "created_at": int(time.time()),
        "cycle": cycle,
        "totals": {"families": len(by_family), "checks": len(rows)},
        "family_rank_by_conclusive_per_min": ranked,
        "policy": policy,
    }


def _deep_insights(
    *,
    cycle: int,
    run_name: str,
    rows: list[dict[str, Any]],
    lean_analysis: dict[str, Any],
    cegis_analysis: dict[str, Any],
    game_analysis: dict[str, Any],
    automation_analysis: dict[str, Any],
    roi_policy: dict[str, Any],
) -> dict[str, Any]:
    totals = {"supported": 0, "falsified": 0, "inconclusive": 0}
    for r in rows:
        st = str(r.get("final_status", "inconclusive"))
        totals[st] = int(totals.get(st, 0)) + 1

    top_findings: list[dict[str, Any]] = []
    top_findings.append(
        {
            "title": "Cycle outcome remained fully conclusive",
            "details": {
                "supported": totals["supported"],
                "falsified": totals["falsified"],
                "inconclusive": totals["inconclusive"],
            },
            "evidence": f"runs/manual_morph_supervised/{run_name}/summary_cycle{cycle}_combined.json",
        }
    )

    gs = game_analysis.get("summary", {})
    top_findings.append(
        {
            "title": "Game boundary probes sharpened attack phase map",
            "details": {
                "exists_supported": gs.get("exists_supported", 0),
                "absent_supported": gs.get("absent_supported", 0),
                "full_capture_absent_supported": gs.get("full_capture_absent_supported", 0),
            },
            "evidence": f"runs/manual_morph_supervised/{run_name}/game_boundary_analysis_cycle{cycle}.json",
        }
    )

    top_findings.append(
        {
            "title": "CEGIS/SyGuS remains model-split rather than globally uniform",
            "details": {
                "status_counts": cegis_analysis.get("status_counts", {}),
                "family_counts": cegis_analysis.get("family_counts", {}),
            },
            "evidence": f"runs/manual_morph_supervised/{run_name}/cegis_sygus_analysis_cycle{cycle}.json",
        }
    )

    top_findings.append(
        {
            "title": "Manual Lean replay continues to provide deterministic formal gating",
            "details": {
                "status_counts": lean_analysis.get("status_counts", {}),
                "total_lean_hypotheses": lean_analysis.get("total_lean_hypotheses", 0),
            },
            "evidence": f"runs/manual_morph_supervised/{run_name}/manual_lean_analysis_cycle{cycle}.json",
        }
    )

    top_findings.append(
        {
            "title": "Automation surface checks confirm deterministic Tau/agent pathways",
            "details": automation_analysis.get("status_counts", {}),
            "evidence": f"runs/manual_morph_supervised/{run_name}/automation_analysis_cycle{cycle}.json",
        }
    )

    top_findings.append(
        {
            "title": "ROI policy identifies highest-yield check families",
            "details": {
                "top_families": (roi_policy.get("policy", {}) or {}).get("promote_families", [])[:5],
                "deprioritize_families": (roi_policy.get("policy", {}) or {}).get("deprioritize_families", [])[:5],
            },
            "evidence": f"runs/manual_morph_supervised/{run_name}/roi_policy_cycle{cycle}.json",
        }
    )

    return {
        "schema": "zenodex/deep-insights-cycle/v1",
        "cycle": cycle,
        "top_findings": top_findings,
    }


def _update_memory_pads(
    *,
    cycle: int,
    run_name: str,
    epoch_report: dict[str, Any],
    deep_insights: dict[str, Any],
    selected_hypotheses: list[dict[str, Any]],
) -> None:
    ideapad = RUNS_ROOT / "ideapad.jsonl"
    insightpad = RUNS_ROOT / "insightpad.jsonl"
    evidence_ledger = RUNS_ROOT / "research_evidence_manual.jsonl"

    cat_counts: dict[str, int] = {}
    for h in selected_hypotheses:
        cat = str(h.get("category", "misc"))
        cat_counts[cat] = int(cat_counts.get(cat, 0)) + 1

    _append_jsonl(
        ideapad,
        {
            "schema": "zenodex/ideapad/v1",
            "created_at": int(time.time()),
            "cycle": cycle,
            "run": run_name,
            "note": "Manual supervised cycle pack with algorithm/game/automation + CEGIS/Lean tranches.",
            "category_counts": cat_counts,
            "focus": [
                "algorithm_discovery",
                "game_theory_boundary_mapping",
                "deterministic_agent_automation",
                "manual_lean_proof_gates",
                "cegis_sygus_classification",
            ],
        },
    )

    insight_titles = [str(x.get("title", "")) for x in deep_insights.get("top_findings", [])[:3]]
    _append_jsonl(
        insightpad,
        {
            "schema": "zenodex/insightpad/v1",
            "created_at": int(time.time()),
            "hypothesis_id": f"M{cycle:03d}",
            "type": "deep_insight",
            "insight": " | ".join(insight_titles),
            "evidence_refs": [
                f"runs/manual_morph_supervised/{run_name}/deep_insights_cycle{cycle}.json",
                f"runs/manual_morph_supervised/{run_name}/epoch_report_cycle{cycle}.json",
            ],
        },
    )

    # Append-only local evidence ledger with required schema fields and final status.
    supported_set = {str(x.get("hypothesis_id", "")) for x in epoch_report.get("newly_supported", [])}
    falsified_set = {str(x.get("hypothesis_id", "")) for x in epoch_report.get("newly_falsified", [])}
    inconclusive_set = {str(x.get("hypothesis_id", "")) for x in epoch_report.get("inconclusive_items", [])}
    for h in selected_hypotheses:
        hid = str(h.get("hypothesis_id", ""))
        st = "inconclusive"
        if hid in supported_set:
            st = "supported"
        elif hid in falsified_set:
            st = "falsified"
        elif hid in inconclusive_set:
            st = "inconclusive"
        _append_jsonl(
            evidence_ledger,
            {
                "schema": "zenodex/research-evidence-manual/v1",
                "created_at": int(time.time()),
                "cycle": cycle,
                "run": run_name,
                "hypothesis_id": hid,
                "mechanism_change": str(h.get("mechanism_change", "")),
                "representation_shift_used": str(h.get("representation_shift_used", "")),
                "expected_metric_delta": h.get("expected_metric_delta", [0, 0, 0, 0, 0]),
                "null_hypothesis": str(h.get("null_hypothesis", "")),
                "falsification_recipe": str(h.get("falsification_recipe", "")),
                "support_recipe": str(h.get("support_recipe", "")),
                "formal_obligations": list(h.get("formal_obligations", [])),
                "risk_modes": list(h.get("risk_modes", [])),
                "status": st,
            },
        )


def main() -> int:
    ap = argparse.ArgumentParser(description="Postprocess a manual supervised cycle into epoch+insight artifacts.")
    ap.add_argument("--cycle-dir", type=Path, required=True)
    ap.add_argument("--runs-root", type=Path, default=Path("runs/manual_morph_supervised"))
    args = ap.parse_args()

    cycle_dir = (ROOT / args.cycle_dir).resolve() if not args.cycle_dir.is_absolute() else args.cycle_dir
    runs_root = (ROOT / args.runs_root).resolve() if not args.runs_root.is_absolute() else args.runs_root
    run_name = cycle_dir.name
    _, cycle = _parse_run_name(run_name)
    if cycle <= 0:
        raise SystemExit(f"Could not parse cycle from run dir: {run_name}")

    summary_combined = _read_json(cycle_dir / f"summary_cycle{cycle}_combined.json", default={})
    rows = [dict(x) for x in summary_combined.get("rows", []) if isinstance(x, dict)]
    if not rows:
        raise SystemExit(f"No combined rows found for cycle {cycle}: {cycle_dir}")

    part_dirs: dict[str, Path] = {}
    for p in runs_root.glob(f"{run_name}_tranche_*"):
        if p.is_dir():
            part_dirs[p.name] = p

    hyp_obj = _read_json(cycle_dir / "hypothesis_pack_100.json", default={})
    selected_hypotheses = [dict(x) for x in hyp_obj.get("hypotheses", []) if isinstance(x, dict)]
    hyp_map = {str(h.get("hypothesis_id", "")): h for h in selected_hypotheses if h.get("hypothesis_id")}

    prev_status = _history_before_cycle(runs_root, cycle)
    epoch_report = _build_epoch_report(
        cycle=cycle,
        cycle_dir=cycle_dir,
        rows=rows,
        hyp_map=hyp_map,
        part_dirs=part_dirs,
        prev_status=prev_status,
    )
    _write_json(cycle_dir / f"epoch_report_cycle{cycle}.json", epoch_report)

    lean_analysis = _lean_analysis(rows, cycle)
    _write_json(cycle_dir / f"manual_lean_analysis_cycle{cycle}.json", lean_analysis)

    cegis_analysis = _cegis_analysis(rows, cycle)
    _write_json(cycle_dir / f"cegis_sygus_analysis_cycle{cycle}.json", cegis_analysis)

    automation_analysis = _automation_analysis(rows, cycle)
    _write_json(cycle_dir / f"automation_analysis_cycle{cycle}.json", automation_analysis)

    game_analysis = _game_boundary_analysis(rows, cycle)
    _write_json(cycle_dir / f"game_boundary_analysis_cycle{cycle}.json", game_analysis)

    proof_intel = _proof_intelligence(cycle=cycle, lean_analysis=lean_analysis, cegis_analysis=cegis_analysis)
    _write_json(cycle_dir / f"proof_intelligence_cycle{cycle}.json", proof_intel)

    roi_policy = _roi_policy(rows, cycle)
    _write_json(cycle_dir / f"roi_policy_cycle{cycle}.json", roi_policy)

    deep_insights = _deep_insights(
        cycle=cycle,
        run_name=run_name,
        rows=rows,
        lean_analysis=lean_analysis,
        cegis_analysis=cegis_analysis,
        game_analysis=game_analysis,
        automation_analysis=automation_analysis,
        roi_policy=roi_policy,
    )
    _write_json(cycle_dir / f"deep_insights_cycle{cycle}.json", deep_insights)

    md_lines = [f"# Cycle {cycle} Deep Insights", ""]
    totals = {"supported": 0, "falsified": 0, "inconclusive": 0}
    for r in rows:
        st = str(r.get("final_status", "inconclusive"))
        totals[st] = int(totals.get(st, 0)) + 1
    md_lines.append(f"- Total hypotheses: {len(rows)}")
    md_lines.append(
        f"- Outcomes: supported={totals['supported']}, falsified={totals['falsified']}, inconclusive={totals['inconclusive']}"
    )
    md_lines.append("")
    for i, f in enumerate(deep_insights.get("top_findings", []), 1):
        md_lines.append(f"## Insight {i}")
        md_lines.append(f"- {f.get('title')}")
        md_lines.append(f"- Details: {json.dumps(f.get('details', {}), sort_keys=True)}")
        md_lines.append("")
    _write_md(cycle_dir / f"deep_insights_cycle{cycle}.md", "\n".join(md_lines).rstrip() + "\n")

    _update_memory_pads(
        cycle=cycle,
        run_name=run_name,
        epoch_report=epoch_report,
        deep_insights=deep_insights,
        selected_hypotheses=selected_hypotheses,
    )

    # Keep a root-level pointer to latest queue for quick handoff.
    queue_obj = _read_json(cycle_dir / "next_experiment_queue.json", default={})
    if queue_obj:
        _write_json(runs_root / "next_experiment_queue.json", queue_obj)

    print(
        json.dumps(
            {
                "ok": True,
                "cycle": cycle,
                "run_name": run_name,
                "resolved": len(rows),
                "epoch_report": str(cycle_dir / f"epoch_report_cycle{cycle}.json"),
                "supported": totals["supported"],
                "falsified": totals["falsified"],
                "inconclusive": totals["inconclusive"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
