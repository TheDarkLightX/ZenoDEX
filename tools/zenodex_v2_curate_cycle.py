#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def _read_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_rows_for_run(run_root: Path, run_name: str) -> list[dict[str, Any]]:
    rd = run_root / run_name
    rows: list[dict[str, Any]] = []

    # Combined summaries may provide either direct rows or part directories.
    for combined in sorted(rd.glob("summary_cycle*combined.json")):
        cobj = _read_json(combined, default={})
        crows = [dict(r) for r in cobj.get("rows", []) if isinstance(r, dict)]
        if crows:
            rows.extend(crows)
            return rows
        for part in cobj.get("parts", []):
            sp = run_root / str(part) / "summary.json"
            if not sp.exists():
                continue
            sobj = _read_json(sp, default={})
            rows.extend(dict(r) for r in sobj.get("rows", []) if isinstance(r, dict))
        if rows:
            return rows

    s = rd / "summary.json"
    if s.exists():
        sobj = _read_json(s, default={})
        rows.extend(dict(r) for r in sobj.get("rows", []) if isinstance(r, dict))
        if rows:
            return rows

    for sp in sorted(rd.glob("tranche_*/summary.json")):
        sobj = _read_json(sp, default={})
        rows.extend(dict(r) for r in sobj.get("rows", []) if isinstance(r, dict))
    return rows


def _load_status_history(run_root: Path, runs: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for run_name in runs:
        rows = _load_rows_for_run(run_root, run_name)
        latest_for_run: dict[str, str] = {}
        for r in rows:
            hid = str(r.get("hypothesis_id", ""))
            st = str(r.get("final_status", ""))
            if not hid or st not in {"supported", "falsified", "inconclusive"}:
                continue
            latest_for_run[hid] = st
        for hid, st in latest_for_run.items():
            out.setdefault(hid, []).append(st)
    return out


def _manual_v2_hypotheses() -> list[dict[str, Any]]:
    base = [
        (
            "H_cycle12_manual_esso_dual_verify_fee_calculator_ref_v1",
            "esso_verify_solver::cvc5,z3::src/kernels/dex/fee_calculator_ref.yaml",
            "restrict",
            [2, 0, 1, -1, 1],
            "Dual-solver fee_calculator_ref verification is not stable.",
        ),
        (
            "H_cycle12_manual_esso_dual_verify_fee_optimizer_v1",
            "esso_verify_solver::cvc5,z3::src/kernels/dex/fee_optimizer.yaml",
            "restrict",
            [2, 0, 1, -1, 1],
            "Dual-solver fee_optimizer verification is not stable.",
        ),
        (
            "H_cycle12_manual_esso_dual_verify_fee_optimizer_evolvable_v1",
            "esso_verify_solver::cvc5,z3::src/kernels/dex/fee_optimizer_evolvable_v1.yaml",
            "restrict",
            [2, 0, 1, -1, 1],
            "Dual-solver fee_optimizer_evolvable verification is not stable.",
        ),
        (
            "H_cycle12_manual_esso_dual_verify_fee_split_dust_carry_v1",
            "esso_verify_solver::cvc5,z3::src/kernels/dex/fee_split_dust_carry_evolvable_v1.yaml",
            "restrict",
            [2, 0, 1, -1, 1],
            "Dual-solver fee_split_dust_carry verification is not stable.",
        ),
        (
            "H_cycle12_manual_esso_dual_timeout1k_fee_optimizer_v1",
            "esso_verify_solver_timeout::cvc5,z3::1000::src/kernels/dex/fee_optimizer.yaml",
            "reduce",
            [1, 0, 1, -1, 2],
            "fee_optimizer does not remain VERIFIED under 1s dual-solver timeout.",
        ),
        (
            "H_cycle12_manual_esso_dual_timeout1k_fee_calculator_ref_v1",
            "esso_verify_solver_timeout::cvc5,z3::1000::src/kernels/dex/fee_calculator_ref.yaml",
            "reduce",
            [1, 0, 1, -1, 2],
            "fee_calculator_ref does not remain VERIFIED under 1s dual-solver timeout.",
        ),
        (
            "H_cycle12_manual_esso_dual_timeout1k_fee_split_dust_carry_v1",
            "esso_verify_solver_timeout::cvc5,z3::1000::src/kernels/dex/fee_split_dust_carry_evolvable_v1.yaml",
            "reduce",
            [1, 0, 1, -1, 2],
            "fee_split_dust_carry does not remain VERIFIED under 1s dual-solver timeout.",
        ),
        (
            "H_cycle12_manual_esso_dual_timeout1k_cpmm_swap_v8_v1",
            "esso_verify_solver_timeout::cvc5,z3::1000::src/kernels/dex/cpmm_swap_v8.yaml",
            "reduce",
            [1, 0, 1, -1, 2],
            "cpmm_swap_v8 does not remain VERIFIED under 1s dual-solver timeout.",
        ),
        (
            "H_cycle12_manual_esso_dual_repeat2_fee_optimizer_v1",
            "esso_repeat2_solver::cvc5,z3::src/kernels/dex/fee_optimizer.yaml",
            "reduce",
            [1, 0, 1, -1, 2],
            "fee_optimizer is unstable across 2x dual-solver replay.",
        ),
        (
            "H_cycle12_manual_esso_dual_repeat3_fee_calculator_ref_v1",
            "esso_repeat3_solver::cvc5,z3::src/kernels/dex/fee_calculator_ref.yaml",
            "reduce",
            [1, 0, 1, -1, 2],
            "fee_calculator_ref is unstable across 3x dual-solver replay.",
        ),
    ]

    out: list[dict[str, Any]] = []
    for hid, recipe, transform, vec, null_h in base:
        out.append(
            {
                "hypothesis_id": hid,
                "mechanism_change": "v2 solver-tier stress check for verified fee-family / cpmm kernels.",
                "representation_shift_used": transform,
                "expected_metric_delta": vec,
                "null_hypothesis": null_h,
                "falsification_recipe": recipe,
                "support_recipe": recipe,
                "formal_obligations": ["Deterministic verdict under specified solver posture"],
                "risk_modes": ["Solver posture drift", "Timeout posture fragility"],
                "status": "proposed",
                "timeout_s": 300,
            }
        )

    # Counterclaims that should falsify if dual-solver gates are genuinely stable.
    counters = [
        (
            "H_cycle12_manual_esso_dual_counterclaim_fee_optimizer_v1",
            "esso_fail_solver::cvc5,z3::src/kernels/dex/fee_optimizer.yaml",
        ),
        (
            "H_cycle12_manual_esso_dual_counterclaim_fee_calculator_ref_v1",
            "esso_fail_solver::cvc5,z3::src/kernels/dex/fee_calculator_ref.yaml",
        ),
        (
            "H_cycle12_manual_esso_dual_counterclaim_fee_split_dust_carry_v1",
            "esso_fail_solver::cvc5,z3::src/kernels/dex/fee_split_dust_carry_evolvable_v1.yaml",
        ),
        (
            "H_cycle12_manual_esso_dual_counterclaim_cpmm_swap_v8_v1",
            "esso_fail_solver::cvc5,z3::src/kernels/dex/cpmm_swap_v8.yaml",
        ),
        (
            "H_cycle12_manual_esso_dual_counterclaim_timeout1k_fee_optimizer_v1",
            "esso_fail_solver_timeout::cvc5,z3::1000::src/kernels/dex/fee_optimizer.yaml",
        ),
    ]
    for hid, recipe in counters:
        out.append(
            {
                "hypothesis_id": hid,
                "mechanism_change": "Counterclaim: dual-solver posture should fail under this recipe.",
                "representation_shift_used": "relax",
                "expected_metric_delta": [1, -1, -1, -1, -1],
                "null_hypothesis": "Deterministic dual-solver gate is stable under this recipe.",
                "falsification_recipe": recipe,
                "support_recipe": recipe,
                "formal_obligations": ["Deterministic failure witness exists"],
                "risk_modes": ["False negative from environment jitter"],
                "status": "proposed",
                "timeout_s": 300,
            }
        )
    return out


def _is_heavy(h: dict[str, Any]) -> bool:
    recipe = str(h.get("support_recipe", ""))
    timeout_s = int(h.get("timeout_s", 180))
    if timeout_s >= 330:
        return True
    if "repeat3" in recipe:
        return True
    if recipe.startswith("lean_repeat"):
        return True
    return False


def main() -> int:
    ap = argparse.ArgumentParser(description="Curate a v2 supervised 100-hypothesis cycle pack with retirement filtering.")
    ap.add_argument("--raw-pack", type=Path, required=True)
    ap.add_argument("--queue-json", type=Path, required=True)
    ap.add_argument("--combined-json", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument("--target", type=int, default=100)
    ap.add_argument("--heavy-target", type=int, default=20)
    args = ap.parse_args()

    out_dir = (ROOT / args.out_dir).resolve() if not args.out_dir.is_absolute() else args.out_dir
    raw_pack = (ROOT / args.raw_pack).resolve() if not args.raw_pack.is_absolute() else args.raw_pack
    queue_json = (ROOT / args.queue_json).resolve() if not args.queue_json.is_absolute() else args.queue_json
    combined_json = (ROOT / args.combined_json).resolve() if not args.combined_json.is_absolute() else args.combined_json

    raw_obj = _read_json(raw_pack, default={})
    raw_hyps = [h for h in raw_obj.get("hypotheses", []) if isinstance(h, dict) and h.get("hypothesis_id")]
    raw_by_id = {str(h["hypothesis_id"]): h for h in raw_hyps}

    queue_obj = _read_json(queue_json, default={})
    queue_ids = [str(r.get("hypothesis_id")) for r in queue_obj.get("queue", []) if isinstance(r, dict) and r.get("hypothesis_id")]

    combined = _read_json(combined_json, default={})
    runs = [str(x) for x in combined.get("runs", []) if isinstance(x, str)]
    status_history = _load_status_history(ROOT / "runs/manual_morph_supervised", runs)

    manual = _manual_v2_hypotheses()
    manual_ids = {str(h["hypothesis_id"]) for h in manual}
    priority_ids = set(queue_ids[:40]) | manual_ids

    retired: dict[str, dict[str, Any]] = {}
    for hid, hist in status_history.items():
        if len(hist) < 3:
            continue
        if not all(s == hist[0] for s in hist):
            continue
        if hid in priority_ids:
            continue
        # Keep active families in circulation.
        if "fee_" in hid or "solver_" in hid:
            continue
        retired[hid] = {"status_history": hist, "reason": "stable_status_3plus_no_priority"}

    selected: list[dict[str, Any]] = []
    seen: set[str] = set()

    def add_h(h: dict[str, Any]) -> None:
        hid = str(h.get("hypothesis_id", ""))
        if not hid or hid in seen:
            return
        seen.add(hid)
        selected.append(h)

    for h in manual:
        add_h(h)

    # Bring in top queue items that still exist in raw pack and are not retired.
    for hid in queue_ids:
        if hid in retired:
            continue
        h = raw_by_id.get(hid)
        if h is not None:
            add_h(h)
        if len(selected) >= int(args.target):
            break

    def score(h: dict[str, Any]) -> tuple[float, str]:
        hid = str(h.get("hypothesis_id", ""))
        tr = str(h.get("representation_shift_used", ""))
        recipe = str(h.get("support_recipe", ""))
        hist = status_history.get(hid, [])
        novelty = 1.0 if not hist else 0.0
        stable_penalty = 0.0
        if len(hist) >= 2 and all(s == hist[0] for s in hist):
            stable_penalty = 0.7
        tr_bonus = 0.0
        if tr in {"restrict", "reduce"}:
            tr_bonus = 0.25
        if tr == "relax":
            tr_bonus = -0.15
        recipe_bonus = 0.0
        if recipe.startswith("esso_verify_solver"):
            recipe_bonus = 0.3
        if "repeat3" in recipe:
            recipe_bonus = -0.1
        return (novelty + tr_bonus + recipe_bonus - stable_penalty, hid)

    for h in sorted(raw_hyps, key=score, reverse=True):
        if len(selected) >= int(args.target):
            break
        hid = str(h["hypothesis_id"])
        if hid in retired:
            continue
        add_h(h)

    # Fill any gap with non-retired raw hypotheses.
    for h in raw_hyps:
        if len(selected) >= int(args.target):
            break
        if str(h["hypothesis_id"]) in retired:
            continue
        add_h(h)

    selected = selected[: int(args.target)]

    heavy: list[dict[str, Any]] = []
    fast: list[dict[str, Any]] = []
    for h in selected:
        (heavy if _is_heavy(h) else fast).append(h)

    heavy_target = max(1, int(args.heavy_target))
    if len(heavy) > heavy_target:
        heavy_sorted = sorted(
            heavy,
            key=lambda x: (int(x.get("timeout_s", 0)), str(x.get("support_recipe", "")), str(x.get("hypothesis_id", ""))),
            reverse=True,
        )
        keep = heavy_sorted[:heavy_target]
        keep_ids = {str(h["hypothesis_id"]) for h in keep}
        moved = [h for h in heavy if str(h["hypothesis_id"]) not in keep_ids]
        heavy = keep
        fast.extend(moved)
    elif len(heavy) < heavy_target:
        promote_pool = sorted(
            [h for h in fast if "repeat2" in str(h.get("support_recipe", "")) or int(h.get("timeout_s", 0)) >= 240],
            key=lambda x: (int(x.get("timeout_s", 0)), str(x.get("hypothesis_id", ""))),
            reverse=True,
        )
        while len(heavy) < heavy_target and promote_pool:
            h = promote_pool.pop(0)
            fast.remove(h)
            heavy.append(h)

    heavy_ordered = sorted(
        heavy,
        key=lambda x: (int(x.get("timeout_s", 0)), str(x.get("support_recipe", "")), str(x.get("hypothesis_id", ""))),
        reverse=True,
    )

    _write_json(
        out_dir / "retirement_report_v2.json",
        {
            "schema": "zenodex/v2-retirement-report/v1",
            "created_at": int(time.time()),
            "runs_considered": runs,
            "retired_count": len(retired),
            "retired_hypotheses": retired,
        },
    )
    _write_json(out_dir / "hypothesis_pack_100.json", {"count": len(selected), "hypotheses": selected})
    _write_json(out_dir / "hypothesis_pack_fast.json", {"count": len(fast), "hypotheses": fast})
    _write_json(out_dir / "hypothesis_pack_heavy.json", {"count": len(heavy), "hypotheses": heavy})
    _write_json(out_dir / "hypothesis_pack_heavy_ordered.json", {"count": len(heavy_ordered), "hypotheses": heavy_ordered})
    _write_json(
        out_dir / "v2_curation_report.json",
        {
            "schema": "zenodex/v2-curation-report/v1",
            "created_at": int(time.time()),
            "target": int(args.target),
            "selected": len(selected),
            "fast": len(fast),
            "heavy": len(heavy),
            "manual_injected": len(manual),
            "queue_used": len(queue_ids),
            "retired_count": len(retired),
            "heavy_target": heavy_target,
        },
    )

    print(
        json.dumps(
            {
                "ok": True,
                "out_dir": str(out_dir),
                "selected": len(selected),
                "fast": len(fast),
                "heavy": len(heavy),
                "retired_count": len(retired),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
