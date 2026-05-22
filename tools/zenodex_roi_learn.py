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


def _load_rows_for_cycle(cycle_dir: Path) -> list[dict[str, Any]]:
    combined = sorted(cycle_dir.glob("summary_cycle*combined.json"))
    if combined:
        obj = _read_json(combined[-1], default={})
        return [dict(x) for x in obj.get("rows", []) if isinstance(x, dict)]

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


def _load_hypothesis_map(cycle_dir: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    pack = cycle_dir / "hypothesis_pack_100.json"
    if not pack.exists():
        return out
    obj = _read_json(pack, default={})
    for row in obj.get("hypotheses", []):
        if not isinstance(row, dict):
            continue
        hid = str(row.get("hypothesis_id", ""))
        if not hid:
            continue
        out[hid] = row
    return out


def _is_dual_solver(check: str) -> bool:
    m = re.search(r"solver(?:_timeout)?::([A-Za-z0-9_,.-]+)::", check)
    if not m:
        return False
    return "," in str(m.group(1))


def _family_for_check(check: str) -> str:
    c = str(check or "")
    if c.startswith("esso_verify_solver_timeout::"):
        return "esso_gate_solver_timeout_dual" if _is_dual_solver(c) else "esso_gate_solver_timeout_single"
    if c.startswith("esso_verify_solver::"):
        return "esso_gate_solver_dual" if _is_dual_solver(c) else "esso_gate_solver_single"
    if c.startswith("esso_fail_solver_timeout::"):
        return "esso_counterclaim_solver_timeout_dual" if _is_dual_solver(c) else "esso_counterclaim_solver_timeout_single"
    if c.startswith("esso_fail_solver::"):
        return "esso_counterclaim_solver_dual" if _is_dual_solver(c) else "esso_counterclaim_solver_single"
    if c.startswith("esso_repeat"):
        if "_solver_timeout::" in c:
            return "esso_replay_solver_timeout_dual" if _is_dual_solver(c) else "esso_replay_solver_timeout_single"
        if "_solver::" in c:
            return "esso_replay_solver_dual" if _is_dual_solver(c) else "esso_replay_solver_single"
        return "esso_replay_default"
    if c.startswith("esso_verify::"):
        return "esso_gate_default"
    if c.startswith("esso_fail::"):
        return "esso_counterclaim_default"
    if c.startswith("lean_pass::"):
        return "lean_gate"
    if c.startswith("lean_fail::"):
        return "lean_counterclaim"
    if c.startswith("lean_repeat"):
        return "lean_replay"
    if c.startswith("pytest_pass::"):
        return "pytest_gate"
    if c.startswith("pytest_fail::"):
        return "pytest_counterclaim"
    if c.startswith("pytest_repeat"):
        return "pytest_replay"
    return c.split("::", 1)[0] if "::" in c else c


def _extract_kernel_path(check: str) -> str | None:
    m = re.search(r"(src/kernels/[A-Za-z0-9_./-]+\.yaml)", str(check or ""))
    if not m:
        return None
    return str(m.group(1))


def _status_bucket(st: str) -> str:
    s = str(st or "")
    if s in {"supported", "falsified", "inconclusive"}:
        return s
    return "inconclusive"


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


def _default_agg() -> dict[str, Any]:
    return {
        "total": 0,
        "supported": 0,
        "falsified": 0,
        "inconclusive": 0,
        "duration_s_total": 0.0,
        "support_gain_sum": 0.0,
    }


def _finalize_agg(rows: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for key, v in rows.items():
        total = int(v["total"])
        dur = float(v["duration_s_total"])
        mins = dur / 60.0 if dur > 0 else 0.0
        conclusive = int(v["supported"]) + int(v["falsified"])
        out[key] = {
            **v,
            "conclusive": conclusive,
            "conclusive_rate": (conclusive / total) if total else 0.0,
            "support_rate": (int(v["supported"]) / total) if total else 0.0,
            "falsify_rate": (int(v["falsified"]) / total) if total else 0.0,
            "inconclusive_rate": (int(v["inconclusive"]) / total) if total else 0.0,
            "mean_duration_s": (dur / total) if total else 0.0,
            "conclusive_per_min": (conclusive / mins) if mins > 0 else 0.0,
            "support_gain_per_min": (float(v["support_gain_sum"]) / mins) if mins > 0 else 0.0,
        }
    return out


def _rank_table(rows: dict[str, dict[str, Any]], metric: str, *, min_total: int = 5) -> list[dict[str, Any]]:
    vals = [dict(name=k, **v) for k, v in rows.items() if int(v.get("total", 0)) >= int(min_total)]
    vals.sort(key=lambda r: (float(r.get(metric, 0.0)), int(r.get("total", 0))), reverse=True)
    return vals


def _policy_recommendations(family_stats: dict[str, dict[str, Any]]) -> list[dict[str, str]]:
    top_conclusive = _rank_table(family_stats, "conclusive_per_min", min_total=5)
    top_gain = _rank_table(family_stats, "support_gain_per_min", min_total=5)

    recs: list[dict[str, str]] = []
    if top_conclusive:
        row = top_conclusive[0]
        recs.append(
            {
                "id": "stage1_fast_discriminator",
                "rule": f"Start each cycle with `{row['name']}` checks for fast signal collection.",
            }
        )
    if top_gain:
        row = top_gain[0]
        recs.append(
            {
                "id": "stage2_frontier_push",
                "rule": f"Prioritize `{row['name']}` when allocating heavy budget to frontier-promotion candidates.",
            }
        )

    expensive_inconclusive = [
        dict(name=k, **v)
        for k, v in family_stats.items()
        if float(v.get("mean_duration_s", 0.0)) >= 30.0 and float(v.get("inconclusive_rate", 0.0)) >= 0.2
    ]
    expensive_inconclusive.sort(key=lambda r: (float(r["inconclusive_rate"]), float(r["mean_duration_s"])), reverse=True)
    if expensive_inconclusive:
        row = expensive_inconclusive[0]
        recs.append(
            {
                "id": "quarantine_high_cost_inconclusive",
                "rule": f"Quarantine `{row['name']}` behind single-solver decomposition before dual/replay escalation.",
            }
        )

    recs.append(
        {
            "id": "paired_claim_counterclaim",
            "rule": "Keep paired gate/counterclaim hypotheses for each manual kernel to maximize falsify-first clarity.",
        }
    )
    recs.append(
        {
            "id": "three_stage_budget",
            "rule": "Budget sequence: fast gate/counterclaim -> replay/timeout only on ambiguous or frontier-critical items -> Lean replay on promoted kernels.",
        }
    )
    return recs


def main() -> int:
    ap = argparse.ArgumentParser(description="Learn ROI-weighted best practices from supervised cycle results.")
    ap.add_argument("--runs-root", type=Path, default=Path("runs/manual_morph_supervised"))
    ap.add_argument("--out-json", type=Path, default=Path("runs/manual_morph_supervised/roi_best_practices.json"))
    ap.add_argument("--out-md", type=Path, default=Path("runs/manual_morph_supervised/roi_best_practices.md"))
    ap.add_argument("--min-total", type=int, default=5)
    args = ap.parse_args()

    runs_root = (ROOT / args.runs_root).resolve() if not args.runs_root.is_absolute() else args.runs_root
    cycle_dirs = [p for p in sorted(runs_root.glob("h*_supervised_cycle*")) if p.is_dir()]

    obs: list[dict[str, Any]] = []
    for cycle_dir in cycle_dirs:
        hmap = _load_hypothesis_map(cycle_dir)
        rows = _load_rows_for_cycle(cycle_dir)
        for row in rows:
            hid = str(row.get("hypothesis_id", ""))
            hyp = hmap.get(hid, {})
            check = str(row.get("check") or hyp.get("support_recipe") or hyp.get("falsification_recipe") or "")
            status = _status_bucket(str(row.get("final_status", "")))
            try:
                duration_s = float(row.get("duration_s", 0.0))
            except Exception:
                duration_s = 0.0
            vec = hyp.get("expected_metric_delta")
            obs.append(
                {
                    "cycle": cycle_dir.name,
                    "hypothesis_id": hid,
                    "status": status,
                    "duration_s": max(0.0, duration_s),
                    "check": check,
                    "family": _family_for_check(check),
                    "kernel_yaml": _extract_kernel_path(check),
                    "transform": str(hyp.get("representation_shift_used", "unknown")),
                    "metric_delta_sum": _sum_vec(vec),
                }
            )

    family_agg: dict[str, dict[str, Any]] = {}
    transform_agg: dict[str, dict[str, Any]] = {}
    kernel_agg: dict[str, dict[str, Any]] = {}

    for row in obs:
        status = str(row["status"])
        duration = float(row["duration_s"])
        gain = float(row["metric_delta_sum"]) if status == "supported" else 0.0

        fam = family_agg.setdefault(str(row["family"]), _default_agg())
        fam["total"] += 1
        fam[status] += 1
        fam["duration_s_total"] += duration
        fam["support_gain_sum"] += max(0.0, gain)

        tr = transform_agg.setdefault(str(row["transform"]), _default_agg())
        tr["total"] += 1
        tr[status] += 1
        tr["duration_s_total"] += duration
        tr["support_gain_sum"] += max(0.0, gain)

        kernel = row.get("kernel_yaml")
        if kernel:
            ka = kernel_agg.setdefault(str(kernel), _default_agg())
            ka["total"] += 1
            ka[status] += 1
            ka["duration_s_total"] += duration
            ka["support_gain_sum"] += max(0.0, gain)

    family_stats = _finalize_agg(family_agg)
    transform_stats = _finalize_agg(transform_agg)
    kernel_stats = _finalize_agg(kernel_agg)

    top_conclusive = _rank_table(family_stats, "conclusive_per_min", min_total=max(1, int(args.min_total)))
    top_gain = _rank_table(family_stats, "support_gain_per_min", min_total=max(1, int(args.min_total)))
    top_kernel_falsifiers = _rank_table(kernel_stats, "falsify_rate", min_total=max(1, int(args.min_total)))
    recs = _policy_recommendations(family_stats)

    payload = {
        "schema": "zenodex/roi-best-practices/v1",
        "generated_at_unix": int(time.time()),
        "runs_root": str(runs_root),
        "cycles_count": len(cycle_dirs),
        "observations": len(obs),
        "family_stats": family_stats,
        "transform_stats": transform_stats,
        "kernel_stats": kernel_stats,
        "top_families_by_conclusive_per_min": top_conclusive[:12],
        "top_families_by_support_gain_per_min": top_gain[:12],
        "top_kernel_falsifiers": top_kernel_falsifiers[:20],
        "policy_recommendations": recs,
    }

    out_json = (ROOT / args.out_json).resolve() if not args.out_json.is_absolute() else args.out_json
    out_md = (ROOT / args.out_md).resolve() if not args.out_md.is_absolute() else args.out_md
    _write_json(out_json, payload)

    lines = [
        "# ROI Best Practices",
        "",
        f"- cycles analyzed: `{len(cycle_dirs)}`",
        f"- observations: `{len(obs)}`",
        "",
        "## Top Families (Conclusive / min)",
    ]
    for row in top_conclusive[:10]:
        lines.append(
            f"- `{row['name']}`: conclusive/min={row['conclusive_per_min']:.2f}, mean_s={row['mean_duration_s']:.2f}, total={row['total']}"
        )
    lines.append("")
    lines.append("## Top Families (Support Gain / min)")
    for row in top_gain[:10]:
        lines.append(
            f"- `{row['name']}`: gain/min={row['support_gain_per_min']:.2f}, support_rate={row['support_rate']:.2f}, total={row['total']}"
        )
    lines.append("")
    lines.append("## Policy Recommendations")
    for row in recs:
        lines.append(f"- `{row['id']}`: {row['rule']}")
    lines.append("")
    _write_md(out_md, "\n".join(lines) + "\n")

    print(
        json.dumps(
            {
                "ok": True,
                "out_json": str(out_json),
                "out_md": str(out_md),
                "cycles": len(cycle_dirs),
                "observations": len(obs),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
