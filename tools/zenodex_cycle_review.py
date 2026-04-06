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


def _parse_cycle_info(name: str) -> tuple[int, int]:
    m = re.match(r"h(\d+)_supervised_cycle(\d+)", name)
    if not m:
        return (0, 0)
    return (int(m.group(1)), int(m.group(2)))


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


def _load_hyp_map(cycle_dir: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    pack = cycle_dir / "hypothesis_pack_100.json"
    if not pack.exists():
        return out
    obj = _read_json(pack, default={})
    for h in obj.get("hypotheses", []):
        if not isinstance(h, dict):
            continue
        hid = str(h.get("hypothesis_id", ""))
        if hid:
            out[hid] = h
    return out


def _extract_kernel(check: str) -> str | None:
    m = re.search(r"(src/kernels/[A-Za-z0-9_./-]+\.yaml)", str(check or ""))
    if not m:
        return None
    return str(m.group(1))


def _check_family(check: str) -> str:
    c = str(check or "")
    if c.startswith("lean_pass::"):
        return "lean_gate"
    if c.startswith("lean_fail::"):
        return "lean_counterclaim"
    if c.startswith("lean_repeat"):
        return "lean_replay"
    if c.startswith("esso_verify"):
        return "esso_gate"
    if c.startswith("esso_fail"):
        return "esso_counterclaim"
    if c.startswith("esso_repeat"):
        return "esso_replay"
    if c.startswith("pytest_pass"):
        return "pytest_gate"
    if c.startswith("pytest_fail"):
        return "pytest_counterclaim"
    if c.startswith("pytest_repeat"):
        return "pytest_replay"
    return c.split("::", 1)[0] if "::" in c else c


def _is_esso_check(check: str) -> bool:
    c = str(check or "")
    return c.startswith("esso")


def _is_dual_solver_check(check: str) -> bool:
    m = re.search(r"solver(?:_timeout)?::([A-Za-z0-9_,.-]+)::", str(check or ""))
    if not m:
        return False
    return "," in str(m.group(1))


def _is_single_solver_check(check: str) -> bool:
    m = re.search(r"solver(?:_timeout)?::([A-Za-z0-9_,.-]+)::", str(check or ""))
    if not m:
        return False
    return "," not in str(m.group(1))


def _dominates(a: list[float], b: list[float]) -> bool:
    return all(x >= y for x, y in zip(a, b)) and any(x > y for x, y in zip(a, b))


def _sum_vec(vec: Any) -> float:
    if not isinstance(vec, list):
        return 0.0
    out = 0.0
    for x in vec:
        try:
            out += float(x)
        except Exception:
            continue
    return out


def _gather_history(runs_root: Path, current_cycle_name: str) -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    cycle_dirs = [p for p in sorted(runs_root.glob("h*_supervised_cycle*")) if p.is_dir()]
    cycle_dirs.sort(key=lambda p: _parse_cycle_info(p.name))

    latest_status: dict[str, str] = {}
    latest_meta: dict[str, dict[str, Any]] = {}
    for cd in cycle_dirs:
        if cd.name == current_cycle_name:
            break
        hmap = _load_hyp_map(cd)
        rows = _load_rows_for_dir(cd)
        for r in rows:
            hid = str(r.get("hypothesis_id", ""))
            st = str(r.get("final_status", ""))
            if not hid or st not in {"supported", "falsified", "inconclusive"}:
                continue
            latest_status[hid] = st
            latest_meta[hid] = hmap.get(hid, {})
    return latest_status, latest_meta


def _collect_all_latest(runs_root: Path) -> tuple[dict[str, str], dict[str, dict[str, Any]], list[str]]:
    cycle_dirs = [p for p in sorted(runs_root.glob("h*_supervised_cycle*")) if p.is_dir()]
    cycle_dirs.sort(key=lambda p: _parse_cycle_info(p.name))

    latest_status: dict[str, str] = {}
    latest_meta: dict[str, dict[str, Any]] = {}
    run_names: list[str] = []
    for cd in cycle_dirs:
        rows = _load_rows_for_dir(cd)
        if not rows:
            continue
        run_names.append(cd.name)
        hmap = _load_hyp_map(cd)
        for r in rows:
            hid = str(r.get("hypothesis_id", ""))
            st = str(r.get("final_status", ""))
            if not hid or st not in {"supported", "falsified", "inconclusive"}:
                continue
            latest_status[hid] = st
            latest_meta[hid] = hmap.get(hid, latest_meta.get(hid, {}))
    return latest_status, latest_meta, run_names


def _frontier_from_latest(latest_status: dict[str, str], latest_meta: dict[str, dict[str, Any]]) -> tuple[list[dict[str, Any]], int]:
    supported: list[dict[str, Any]] = []
    supported_without_vector = 0
    for hid, st in latest_status.items():
        if st != "supported":
            continue
        h = latest_meta.get(hid, {})
        vec = h.get("expected_metric_delta")
        if not isinstance(vec, list) or len(vec) != 5:
            supported_without_vector += 1
            continue
        try:
            v = [float(x) for x in vec]
        except Exception:
            supported_without_vector += 1
            continue
        supported.append({"hypothesis_id": hid, "vector": v})

    frontier: list[dict[str, Any]] = []
    for a in supported:
        if any(_dominates(b["vector"], a["vector"]) for b in supported if b["hypothesis_id"] != a["hypothesis_id"]):
            continue
        frontier.append(a)
    frontier.sort(key=lambda r: (sum(r["vector"]), r["hypothesis_id"]), reverse=True)
    return frontier, supported_without_vector


def _rank_eig(rows: list[dict[str, Any]], hyp_map: dict[str, dict[str, Any]], flips: set[str]) -> list[dict[str, Any]]:
    ranked: list[dict[str, Any]] = []
    for r in rows:
        hid = str(r.get("hypothesis_id", ""))
        status = str(r.get("final_status", "inconclusive"))
        check = str(r.get("check", ""))
        h = hyp_map.get(hid, {})
        tr = str(h.get("representation_shift_used", "unknown"))
        dur = float(r.get("duration_s", 0) or 0)
        eig = 1.0
        if status == "falsified":
            eig += 2.0
        elif status == "inconclusive":
            eig += 1.5
        else:
            eig += 0.8
        if tr == "reduce":
            eig += 0.35
        elif tr == "restrict":
            eig += 0.25
        elif tr == "relax":
            eig += 0.15
        if check.startswith("esso_verify_solver::cvc5,z3::") and status in {"falsified", "inconclusive"}:
            eig += 0.5
        if check.startswith("esso_repeat2_solver::cvc5,z3::") and status in {"falsified", "inconclusive"}:
            eig += 0.4
        if check.startswith("lean_repeat3::") and status == "supported":
            eig += 0.2
        if dur > 60:
            eig -= 0.3
        elif dur < 3:
            eig += 0.15
        if hid in flips:
            eig += 0.5
        ranked.append(
            {
                "hypothesis_id": hid,
                "status": status,
                "check": check,
                "duration_s": int(dur),
                "transform": tr,
                "expected_information_gain": round(eig, 3),
            }
        )
    ranked.sort(key=lambda x: (float(x["expected_information_gain"]), -int(x["duration_s"]), x["hypothesis_id"]), reverse=True)
    return ranked


def _load_detail_for_row(part_dir: Path, hypothesis_id: str) -> dict[str, Any]:
    result_path = part_dir / "results" / _safe_token(hypothesis_id, max_len=180) / "result.json"
    if not result_path.exists():
        return {}
    obj = _read_json(result_path, default={})
    return obj if isinstance(obj, dict) else {}


def _extract_phase_payloads(detail: dict[str, Any]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for phase in ("refute", "support"):
        p = (((detail.get(phase) or {}).get("payload")) or {}) if isinstance(detail, dict) else {}
        if not isinstance(p, dict) or not p:
            continue
        metrics = p.get("metrics") or {}
        verdict = str(metrics.get("verdict", "")) if isinstance(metrics, dict) else ""
        reason = str(p.get("reason", ""))
        status = str(p.get("status", ""))
        counterexample = p.get("counterexample")
        rep = (((counterexample or {}).get("verify_report") or {}).get("report") or {}) if isinstance(counterexample, dict) else {}
        solvers_agreed = rep.get("solvers_agreed") if isinstance(rep, dict) else None
        events.append(
            {
                "phase": phase,
                "verdict": verdict,
                "reason": reason,
                "status": status,
                "counterexample_present": counterexample is not None,
                "solvers_agreed": solvers_agreed,
            }
        )
    return events


def _recommend_for_label(label: str) -> str:
    if label == "verified_anchor":
        return "Use as calibration anchor; avoid spending heavy replay budget unless behavior flips."
    if label == "semantic_failure":
        return "Prioritize mechanism/invariant redesign; solver posture is not the limiting factor."
    if label == "mixed_semantic_plus_posture":
        return "Run single-solver decomposition first, then targeted redesign with replay only after semantic split is resolved."
    if label == "representation_intractable_candidate":
        return "Apply representation shift (decomposition/restriction), shrink domains, and avoid dual-replay escalation until posture stabilizes."
    return "Collect one gate + one counterclaim + one decomposition check before heavy replay."


def _representation_intractability(
    *,
    rows: list[dict[str, Any]],
    part_dirs: dict[str, Path],
) -> dict[str, Any]:
    kernel_agg: dict[str, dict[str, Any]] = {}

    for row in rows:
        check = str(row.get("check", ""))
        if not _is_esso_check(check):
            continue
        kernel = _extract_kernel(check)
        if not kernel:
            continue

        ka = kernel_agg.setdefault(
            kernel,
            {
                "kernel": kernel,
                "total_checks": 0,
                "duration_s_total": 0.0,
                "dual_checks": 0,
                "single_solver_checks": 0,
                "final_supported": 0,
                "final_falsified": 0,
                "final_inconclusive": 0,
                "verdict_verified": 0,
                "verdict_failed": 0,
                "verdict_inconclusive": 0,
                "verdict_review_needed": 0,
                "timeout_events": 0,
                "payload_inconclusive_events": 0,
                "counterexample_events": 0,
                "solver_disagreement_events": 0,
                "event_count": 0,
            },
        )

        ka["total_checks"] += 1
        ka["duration_s_total"] += float(row.get("duration_s", 0) or 0)
        if _is_dual_solver_check(check):
            ka["dual_checks"] += 1
        if _is_single_solver_check(check):
            ka["single_solver_checks"] += 1

        st = str(row.get("final_status", "inconclusive"))
        if st == "supported":
            ka["final_supported"] += 1
        elif st == "falsified":
            ka["final_falsified"] += 1
        else:
            ka["final_inconclusive"] += 1

        src = str(row.get("source", ""))
        part_dir = part_dirs.get(src)
        detail = _load_detail_for_row(part_dir, str(row.get("hypothesis_id", ""))) if part_dir else {}
        events = _extract_phase_payloads(detail)

        for ev in events:
            ka["event_count"] += 1
            verdict = str(ev.get("verdict", ""))
            reason = str(ev.get("reason", ""))
            status = str(ev.get("status", ""))
            if verdict == "VERIFIED":
                ka["verdict_verified"] += 1
            elif verdict == "FAILED":
                ka["verdict_failed"] += 1
            elif verdict == "INCONCLUSIVE":
                ka["verdict_inconclusive"] += 1
            elif verdict == "REVIEW_NEEDED":
                ka["verdict_review_needed"] += 1

            if reason in {"timeout", "repeat_inconclusive"}:
                ka["timeout_events"] += 1
            if status == "inconclusive":
                ka["payload_inconclusive_events"] += 1
            if bool(ev.get("counterexample_present")):
                ka["counterexample_events"] += 1
            if ev.get("solvers_agreed") is False or verdict == "REVIEW_NEEDED":
                ka["solver_disagreement_events"] += 1

    rows_out: list[dict[str, Any]] = []
    for kernel, ka in kernel_agg.items():
        total = max(1, int(ka["total_checks"]))
        events = max(1, int(ka["event_count"]))
        mean_duration_s = float(ka["duration_s_total"]) / total
        dual_ratio = float(ka["dual_checks"]) / total
        single_ratio = float(ka["single_solver_checks"]) / total

        semantic_evidence_rate = min(
            1.0,
            float(ka["verdict_failed"] + ka["verdict_verified"] + ka["counterexample_events"]) / events,
        )
        posture_problem_rate = min(
            1.0,
            float(
                ka["verdict_review_needed"]
                + ka["verdict_inconclusive"]
                + ka["timeout_events"]
                + ka["payload_inconclusive_events"]
                + ka["solver_disagreement_events"]
            )
            / events,
        )
        cost_penalty = min(1.0, mean_duration_s / 90.0)
        decomposition_gap = max(0.0, dual_ratio - single_ratio)

        score = 100.0 * (
            0.45 * posture_problem_rate
            + 0.25 * cost_penalty
            + 0.20 * decomposition_gap
            - 0.40 * semantic_evidence_rate
        )
        score = max(0.0, min(100.0, score))

        verified_rate = float(ka["verdict_verified"]) / events
        failed_rate = float(ka["verdict_failed"]) / events

        if verified_rate >= 0.60 and posture_problem_rate < 0.30:
            label = "verified_anchor"
        elif semantic_evidence_rate >= 0.50 and posture_problem_rate < 0.45 and failed_rate >= verified_rate:
            label = "semantic_failure"
        elif semantic_evidence_rate >= 0.35 and posture_problem_rate >= 0.35:
            label = "mixed_semantic_plus_posture"
        elif semantic_evidence_rate < 0.25 and posture_problem_rate >= 0.50:
            label = "representation_intractable_candidate"
        else:
            label = "mixed"

        rows_out.append(
            {
                "kernel": kernel,
                "representation_intractability_score": round(score, 3),
                "label": label,
                "recommended_action": _recommend_for_label(label),
                "stats": {
                    **ka,
                    "mean_duration_s": round(mean_duration_s, 3),
                    "dual_ratio": round(dual_ratio, 4),
                    "single_solver_ratio": round(single_ratio, 4),
                    "semantic_evidence_rate": round(semantic_evidence_rate, 4),
                    "posture_problem_rate": round(posture_problem_rate, 4),
                    "cost_penalty": round(cost_penalty, 4),
                    "decomposition_gap": round(decomposition_gap, 4),
                    "verified_rate": round(verified_rate, 4),
                    "failed_rate": round(failed_rate, 4),
                },
            }
        )

    rows_out.sort(
        key=lambda r: (
            float(r["representation_intractability_score"]),
            float((r.get("stats") or {}).get("posture_problem_rate", 0.0)),
            r["kernel"],
        ),
        reverse=True,
    )

    label_counts: dict[str, int] = {}
    for r in rows_out:
        label = str(r.get("label", "mixed"))
        label_counts[label] = int(label_counts.get(label, 0)) + 1

    return {
        "schema": "zenodex/representation-intractability/v1",
        "created_at": int(time.time()),
        "kernel_count": len(rows_out),
        "label_counts": label_counts,
        "rows": rows_out,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Build supervised cycle review + combined frontier summary.")
    ap.add_argument("--cycle-dir", type=Path, required=True)
    ap.add_argument("--part", dest="parts", action="append", default=[])
    ap.add_argument("--runs-root", type=Path, default=Path("runs/manual_morph_supervised"))
    ap.add_argument("--manual-prefix", type=str, default="")
    ap.add_argument("--review-json", type=Path, required=True)
    ap.add_argument("--review-md", type=Path, required=True)
    ap.add_argument("--next-queue-json", type=Path, required=True)
    ap.add_argument("--summary-combined-json", type=Path, required=True)
    ap.add_argument("--combined-out", type=Path, required=True)
    ap.add_argument("--intractability-json", type=Path, default=None)
    args = ap.parse_args()

    cycle_dir = (ROOT / args.cycle_dir).resolve() if not args.cycle_dir.is_absolute() else args.cycle_dir
    runs_root = (ROOT / args.runs_root).resolve() if not args.runs_root.is_absolute() else args.runs_root
    parts = [((ROOT / Path(p)).resolve() if not Path(p).is_absolute() else Path(p)) for p in args.parts]
    if not parts:
        parts = [cycle_dir]
    part_dirs = {p.name: p for p in parts}

    cycle_name = cycle_dir.name
    _, cycle_number = _parse_cycle_info(cycle_name)
    manual_prefix = args.manual_prefix or f"H_cycle{cycle_number}_manual_"

    rows: list[dict[str, Any]] = []
    for p in parts:
        sobj = _read_json(p / "summary.json", default={})
        for r in sobj.get("rows", []):
            if not isinstance(r, dict):
                continue
            rr = dict(r)
            rr["source"] = p.name
            rows.append(rr)

    rows.sort(key=lambda r: str(r.get("hypothesis_id", "")))
    _write_json(
        (ROOT / args.summary_combined_json).resolve() if not args.summary_combined_json.is_absolute() else args.summary_combined_json,
        {
            "created_at": int(time.time()),
            "parts": [p.name for p in parts],
            "resolved": len(rows),
            "rows": rows,
        },
    )

    hyp_map = _load_hyp_map(cycle_dir)
    totals = {"supported": 0, "falsified": 0, "inconclusive": 0}
    transform_breakdown: dict[str, dict[str, int]] = {}
    falsified_kernel: dict[str, int] = {}
    expensive: list[dict[str, Any]] = []

    for r in rows:
        st = str(r.get("final_status", "inconclusive"))
        if st not in totals:
            st = "inconclusive"
        totals[st] += 1

        hid = str(r.get("hypothesis_id", ""))
        h = hyp_map.get(hid, {})
        tr = str(h.get("representation_shift_used", "unknown"))
        tb = transform_breakdown.setdefault(tr, {"total": 0, "supported": 0, "falsified": 0, "inconclusive": 0})
        tb["total"] += 1
        tb[st] += 1

        check = str(r.get("check", ""))
        k = _extract_kernel(check)
        if st == "falsified" and k:
            falsified_kernel[k] = int(falsified_kernel.get(k, 0)) + 1

        expensive.append(
            {
                "hypothesis_id": hid,
                "check": check,
                "status": st,
                "duration_s": int(float(r.get("duration_s", 0) or 0)),
                "family": _check_family(check),
            }
        )

    expensive.sort(key=lambda x: x["duration_s"], reverse=True)

    prev_status, _ = _gather_history(runs_root, cycle_name)
    novel = 0
    overlap = 0
    flips = 0
    flip_rows: list[dict[str, Any]] = []
    for r in rows:
        hid = str(r.get("hypothesis_id", ""))
        st = str(r.get("final_status", ""))
        old = prev_status.get(hid)
        if old is None:
            novel += 1
        else:
            overlap += 1
            if old != st:
                flips += 1
                flip_rows.append({"hypothesis_id": hid, "from": old, "to": st})

    flip_ids = {x["hypothesis_id"] for x in flip_rows}
    ranked = _rank_eig(rows, hyp_map, flip_ids)
    next_queue = ranked[:25]

    manual_rows = [r for r in rows if str(r.get("hypothesis_id", "")).startswith(manual_prefix)]
    manual_status = {str(r.get("hypothesis_id", "")): str(r.get("final_status", "")) for r in manual_rows}
    manual_lp_status = {k: v for k, v in manual_status.items() if "_lp_" in k or "lp_" in k}
    manual_rebalancer_status = {k: v for k, v in manual_status.items() if "rebal" in k}
    manual_lean_status = {k: v for k, v in manual_status.items() if "_lean_" in k}

    latest_status, latest_meta, run_names = _collect_all_latest(runs_root)
    frontier, supported_without_vector = _frontier_from_latest(latest_status, latest_meta)
    status_counts = {"supported": 0, "falsified": 0, "inconclusive": 0}
    for st in latest_status.values():
        if st in status_counts:
            status_counts[st] += 1

    combined_payload = {
        "schema": "zenodex/supervised-combined-analysis/v1",
        "created_at": int(time.time()),
        "runs": run_names,
        "unique_hypotheses": len(latest_status),
        "status_counts": status_counts,
        "frontier_size": len(frontier),
        "pareto_frontier": frontier,
        "supported_without_vector": supported_without_vector,
    }
    _write_json((ROOT / args.combined_out).resolve() if not args.combined_out.is_absolute() else args.combined_out, combined_payload)

    precheck_summary = _read_json(cycle_dir / "pre_checks_summary.json", default={})
    precheck_inference = precheck_summary.get("inference", {}) if isinstance(precheck_summary, dict) else {}

    intractability = _representation_intractability(rows=rows, part_dirs=part_dirs)
    intractability_top = intractability.get("rows", [])[:8]

    intractability_json_path = None
    if args.intractability_json is not None:
        intractability_json_path = (ROOT / args.intractability_json).resolve() if not args.intractability_json.is_absolute() else args.intractability_json
        _write_json(intractability_json_path, intractability)

    deep_insights: list[dict[str, Any]] = []
    relax = transform_breakdown.get("relax", {})
    reduce = transform_breakdown.get("reduce", {})
    restrict = transform_breakdown.get("restrict", {})
    if relax:
        relax_total = max(1, int(relax.get("total", 0)))
        deep_insights.append(
            {
                "title": "Transform-role asymmetry persists",
                "details": {
                    "relax_falsify_rate": round(float(relax.get("falsified", 0)) / relax_total, 4),
                    "reduce_support": int(reduce.get("supported", 0)),
                    "restrict_support": int(restrict.get("supported", 0)),
                },
            }
        )

    if precheck_inference:
        deep_insights.append(
            {
                "title": "Solver decomposition sharpens bottleneck diagnosis",
                "details": precheck_inference,
            }
        )

    if intractability_top:
        deep_insights.append(
            {
                "title": "Representation intractability is now explicitly scored",
                "details": {
                    "top_kernels": [
                        {
                            "kernel": r.get("kernel"),
                            "score": r.get("representation_intractability_score"),
                            "label": r.get("label"),
                        }
                        for r in intractability_top[:5]
                    ],
                    "label_counts": intractability.get("label_counts", {}),
                },
            }
        )

    top_kernels = sorted(falsified_kernel.items(), key=lambda x: x[1], reverse=True)[:8]
    deep_insights.append(
        {
            "title": "Falsification clusters remain kernel-family concentrated",
            "details": {"top_falsified_kernel_families": [{"kernel": k, "count": c} for k, c in top_kernels]},
        }
    )

    if rows:
        mean_dur = sum(int(float(r.get("duration_s", 0) or 0)) for r in rows) / max(1, len(rows))
        deep_insights.append(
            {
                "title": "Cost-aware sequencing still matters",
                "details": {
                    "mean_duration_s": round(mean_dur, 2),
                    "heavy_checks_ge_60s": len([r for r in expensive if int(r["duration_s"]) >= 60]),
                    "conclusive_rate": round((totals["supported"] + totals["falsified"]) / max(1, len(rows)), 4),
                },
            }
        )

    review = {
        "created_at": int(time.time()),
        "cycle": cycle_name,
        "cycle_parts": [p.name for p in parts],
        "resolved": len(rows),
        "totals": totals,
        "novel": novel,
        "overlap": overlap,
        "flips": flips,
        "flip_rows": flip_rows,
        "transform_breakdown": transform_breakdown,
        "expensive_checks": expensive[:20],
        "falsified_kernel_family_cluster": [{"kernel": k, "count": c} for k, c in top_kernels],
        "manual_status": manual_status,
        "manual_lp_status": manual_lp_status,
        "manual_rebalancer_status": manual_rebalancer_status,
        "manual_lean_status": manual_lean_status,
        "precheck_inference": precheck_inference,
        "representation_intractability": intractability,
        "representation_intractability_top": intractability_top,
        "deep_insights": deep_insights,
        "next_queue_preview": next_queue[:12],
        "latest_combined": {
            "unique_hypotheses": combined_payload["unique_hypotheses"],
            "status_counts": combined_payload["status_counts"],
            "frontier_size": combined_payload["frontier_size"],
        },
    }

    review_json = (ROOT / args.review_json).resolve() if not args.review_json.is_absolute() else args.review_json
    review_md = (ROOT / args.review_md).resolve() if not args.review_md.is_absolute() else args.review_md
    queue_json = (ROOT / args.next_queue_json).resolve() if not args.next_queue_json.is_absolute() else args.next_queue_json

    _write_json(review_json, review)
    _write_json(
        queue_json,
        {
            "schema": "zenodex/next-experiment-queue/v1",
            "created_at": int(time.time()),
            "cycle": cycle_name,
            "queue": next_queue,
        },
    )

    md_lines = [
        f"# {cycle_name} Review",
        "",
        f"- Resolved: `{len(rows)}`",
        f"- Totals: `supported={totals['supported']}`, `falsified={totals['falsified']}`, `inconclusive={totals['inconclusive']}`",
        f"- Novel/Overlap/Flips: `{novel}` / `{overlap}` / `{flips}`",
        "",
        "## Deep Insights",
    ]
    for d in deep_insights:
        md_lines.append(f"- {d['title']}: {json.dumps(d['details'], sort_keys=True)}")

    md_lines += ["", "## Representation Intractability (Top 8)"]
    for r in intractability_top:
        md_lines.append(
            f"- `{r['kernel']}` | score={r['representation_intractability_score']} | label=`{r['label']}` | action={r['recommended_action']}"
        )

    md_lines += ["", "## Top Expensive Checks"]
    for r in expensive[:15]:
        md_lines.append(f"- `{r['hypothesis_id']}` | `{r['check']}` | `{r['status']}` | `{r['duration_s']}s`")

    md_lines += ["", "## Next Queue (Top 12)"]
    for r in next_queue[:12]:
        md_lines.append(f"- `{r['hypothesis_id']}` | `{r['status']}` | `EIG={r['expected_information_gain']}`")
    md_lines.append("")
    _write_md(review_md, "\n".join(md_lines) + "\n")

    print(
        json.dumps(
            {
                "ok": True,
                "cycle": cycle_name,
                "resolved": len(rows),
                "totals": totals,
                "frontier_size": combined_payload["frontier_size"],
                "intractability_kernels": int(intractability.get("kernel_count", 0)),
                "intractability_json": str(intractability_json_path) if intractability_json_path else None,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
