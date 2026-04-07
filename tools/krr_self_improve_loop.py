#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import time
from collections import Counter
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def _read_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _run(cmd: list[str], *, timeout_s: int = 1800) -> tuple[int, str, str, float]:
    t0 = time.time()
    proc = subprocess.run(
        cmd,
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        timeout=max(60, int(timeout_s)),
        check=False,
    )
    return int(proc.returncode), str(proc.stdout or ""), str(proc.stderr or ""), float(time.time() - t0)


def _bridge_and_eval(
    *,
    run_dir: Path,
    cycle: int,
    manifest: Path,
    kb_path: Path,
    krr_backend: str,
    bridge_script: Path,
    bridge_manifest_flag: str,
    bridge_extra: list[str],
) -> dict[str, Any]:
    stem = manifest.parent.name
    pack_path = run_dir / f"pack_{stem}_{krr_backend}.json"
    eval_dir = run_dir / f"eval_{stem}_{krr_backend}"

    bridge_cmd = [
        "python3",
        str(bridge_script),
        "--cycle",
        str(int(cycle)),
        str(bridge_manifest_flag),
        str(manifest),
        "--out-json",
        str(pack_path),
        "--krr-backend",
        str(krr_backend),
        "--krr-kb",
        str(kb_path),
    ] + list(bridge_extra)

    rc, out, err, dt = _run(bridge_cmd, timeout_s=1800)
    if rc != 0:
        return {
            "ok": False,
            "phase": "bridge",
            "manifest": str(manifest),
            "returncode": rc,
            "stdout_tail": out[-2000:],
            "stderr_tail": err[-2000:],
            "duration_s": dt,
        }

    eval_cmd = [
        "python3",
        "tools/zenodex_manual_supervised_runner.py",
        "--hypotheses-json",
        str(pack_path),
        "--out-dir",
        str(eval_dir),
    ]
    rc2, out2, err2, dt2 = _run(eval_cmd, timeout_s=1800)
    if rc2 != 0:
        return {
            "ok": False,
            "phase": "eval",
            "manifest": str(manifest),
            "returncode": rc2,
            "stdout_tail": out2[-2000:],
            "stderr_tail": err2[-2000:],
            "duration_s": dt2,
        }

    pack = _read_json(pack_path, default={})
    summary = _read_json(eval_dir / "summary.json", default={})
    analysis = _read_json(eval_dir / "analysis.json", default={})
    rows = [r for r in (summary.get("rows") or []) if isinstance(r, dict)]
    counts = Counter(str(r.get("final_status", "")) for r in rows)
    n = len(rows)
    support_rate = (float(counts.get("supported", 0)) / float(n)) if n > 0 else 0.0
    avg_selection_score = statistics.mean(float(h.get("selection_score", 0.0)) for h in (pack.get("hypotheses") or [])) if (pack.get("hypotheses") or []) else 0.0

    return {
        "ok": True,
        "manifest": str(manifest),
        "manifest_name": stem,
        "hypothesis_count": int(n),
        "supported": int(counts.get("supported", 0)),
        "falsified": int(counts.get("falsified", 0)),
        "inconclusive": int(counts.get("inconclusive", 0)),
        "support_rate": float(support_rate),
        "frontier_size": int(len(analysis.get("pareto_frontier", []) if isinstance(analysis, dict) else [])),
        "avg_selection_score": float(avg_selection_score),
        "krr_backend_counts": (pack.get("selection_stats", {}) or {}).get("krr_backend_counts", {}),
        "krr_fallback_reasons": (pack.get("selection_stats", {}) or {}).get("krr_fallback_reasons", {}),
    }


def _aggregate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    valid = [r for r in rows if isinstance(r, dict) and bool(r.get("ok"))]
    if not valid:
        return {
            "runs": 0,
            "total_hypotheses": 0,
            "supported": 0,
            "falsified": 0,
            "inconclusive": 0,
            "support_rate": 0.0,
            "avg_selection_score_mean": 0.0,
            "frontier_size_mean": 0.0,
        }
    total_hyp = sum(int(r.get("hypothesis_count", 0)) for r in valid)
    supported = sum(int(r.get("supported", 0)) for r in valid)
    falsified = sum(int(r.get("falsified", 0)) for r in valid)
    inconclusive = sum(int(r.get("inconclusive", 0)) for r in valid)
    return {
        "runs": len(valid),
        "total_hypotheses": int(total_hyp),
        "supported": int(supported),
        "falsified": int(falsified),
        "inconclusive": int(inconclusive),
        "support_rate": float(supported) / float(total_hyp) if total_hyp > 0 else 0.0,
        "avg_selection_score_mean": float(statistics.mean(float(r.get("avg_selection_score", 0.0)) for r in valid)),
        "frontier_size_mean": float(statistics.mean(float(r.get("frontier_size", 0.0)) for r in valid)),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Iterative KRR self-improvement loop with auto-vs-off A/B gates.")
    ap.add_argument("--loop-root", type=Path, default=Path("runs/krr_self_improve_loop"))
    ap.add_argument("--bridge-script", type=Path, default=Path("tools/zenodex_candidate_bridge.py"), help="Path to the candidate bridge script.")
    ap.add_argument("--bridge-manifest-flag", type=str, default="--candidate-manifest", help="Manifest flag passed to the bridge script.")
    ap.add_argument("--iterations", type=int, default=3)
    ap.add_argument("--cycle-base", type=int, default=200)
    ap.add_argument("--manifest", action="append", default=[], help="Candidate manifest JSON path. Repeatable.")
    ap.add_argument("--kb-seed", type=Path, default=Path("tools/krr_knowledge_base.json"))
    ap.add_argument("--min-count", type=int, default=4)
    ap.add_argument("--max-auto-rules", type=int, default=24)
    ap.add_argument("--mode", type=str, default="stress", choices=["regular", "stress"])
    args = ap.parse_args()

    loop_root = (ROOT / args.loop_root).resolve() if not args.loop_root.is_absolute() else args.loop_root
    loop_root.mkdir(parents=True, exist_ok=True)

    manifests: list[Path] = []
    for raw in list(args.manifest or []):
        p = Path(raw)
        if not p.is_absolute():
            p = (ROOT / p).resolve()
        if p.exists():
            manifests.append(p)
    manifests = sorted(set(manifests))

    if not manifests:
        print("error: provide at least one --manifest path", flush=True)
        return 2

    bridge_script = (ROOT / args.bridge_script).resolve() if not args.bridge_script.is_absolute() else args.bridge_script
    if not bridge_script.exists():
        print(f"error: bridge script not found: {bridge_script}", flush=True)
        return 2

    kb_seed = (ROOT / args.kb_seed).resolve() if not args.kb_seed.is_absolute() else args.kb_seed
    current_kb = kb_seed

    bridge_extra = ["--max-per-operator", "4", "--max-signature-repeats", "10", "--min-speedup", "0.9", "--min-check-support-rate", "0.0", "--min-check-history-total", "99999"]
    if str(args.mode) == "regular":
        bridge_extra = ["--max-per-operator", "3", "--max-signature-repeats", "4"]

    history: list[dict[str, Any]] = []
    best_gain = -10**9
    best_iter = -1

    for i in range(1, max(1, int(args.iterations)) + 1):
        iter_dir = loop_root / f"iter_{i:03d}"
        iter_dir.mkdir(parents=True, exist_ok=True)

        refined_kb = iter_dir / "krr_refined.json"
        refine_cmd = [
            "python3",
            "tools/krr_refine_from_evidence.py",
            "--kb-in",
            str(current_kb),
            "--kb-out",
            str(refined_kb),
            "--min-count",
            str(max(1, int(args.min_count))),
            "--max-auto-rules",
            str(max(1, int(args.max_auto_rules))),
        ]
        rc, out, err, _dt = _run(refine_cmd, timeout_s=600)
        if rc != 0:
            record = {
                "iteration": i,
                "ok": False,
                "phase": "refine",
                "returncode": rc,
                "stdout_tail": out[-2000:],
                "stderr_tail": err[-2000:],
            }
            history.append(record)
            _write_json(loop_root / "loop_report.json", {"schema": "zenodex/krr-self-improve/v1", "history": history})
            print(json.dumps(record, sort_keys=True))
            continue

        cycle = int(args.cycle_base) + i
        auto_rows: list[dict[str, Any]] = []
        off_rows: list[dict[str, Any]] = []
        for m in manifests:
            auto_rows.append(
                _bridge_and_eval(
                    run_dir=iter_dir,
                    cycle=cycle,
                    manifest=m,
                    kb_path=refined_kb,
                    krr_backend="auto",
                    bridge_script=bridge_script,
                    bridge_manifest_flag=args.bridge_manifest_flag,
                    bridge_extra=bridge_extra,
                )
            )
            off_rows.append(
                _bridge_and_eval(
                    run_dir=iter_dir,
                    cycle=cycle,
                    manifest=m,
                    kb_path=refined_kb,
                    krr_backend="off",
                    bridge_script=bridge_script,
                    bridge_manifest_flag=args.bridge_manifest_flag,
                    bridge_extra=bridge_extra,
                )
            )

        agg_auto = _aggregate(auto_rows)
        agg_off = _aggregate(off_rows)
        support_gain = float(agg_auto.get("support_rate", 0.0)) - float(agg_off.get("support_rate", 0.0))
        score_gain = float(agg_auto.get("avg_selection_score_mean", 0.0)) - float(agg_off.get("avg_selection_score_mean", 0.0))
        frontier_gain = float(agg_auto.get("frontier_size_mean", 0.0)) - float(agg_off.get("frontier_size_mean", 0.0))
        gain = (20.0 * support_gain) + score_gain + (0.1 * frontier_gain)

        record = {
            "iteration": i,
            "ok": True,
            "cycle": cycle,
            "kb_in": str(current_kb),
            "kb_refined": str(refined_kb),
            "aggregate_auto": agg_auto,
            "aggregate_off": agg_off,
            "support_gain": support_gain,
            "score_gain": score_gain,
            "frontier_gain": frontier_gain,
            "objective_gain": gain,
            "auto_rows": auto_rows,
            "off_rows": off_rows,
        }
        history.append(record)

        if gain >= best_gain:
            best_gain = gain
            best_iter = i
            best_kb = iter_dir / "krr_best_candidate.json"
            best_kb.write_text(refined_kb.read_text(encoding="utf-8"), encoding="utf-8")
            current_kb = best_kb
        else:
            # Keep exploring from current best if this iteration regressed.
            pass

        _write_json(
            loop_root / "loop_report.json",
            {
                "schema": "zenodex/krr-self-improve/v1",
                "mode": str(args.mode),
                "iterations": int(args.iterations),
                "best_iteration": int(best_iter),
                "best_gain": float(best_gain),
                "history": history,
            },
        )

        print(
            json.dumps(
                {
                    "ok": True,
                    "iteration": i,
                    "best_iteration": best_iter,
                    "objective_gain": gain,
                    "best_gain": best_gain,
                    "support_gain": support_gain,
                    "score_gain": score_gain,
                },
                sort_keys=True,
            )
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
