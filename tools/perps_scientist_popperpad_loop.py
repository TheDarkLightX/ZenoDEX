#!/usr/bin/env python3
"""Run a PopperPad-first Morph scientist loop for perps domains.

Flow:
1) Create a falsifiable PopperPad hypothesis for a domain/profile.
2) Run search A/B (Morph `scientist ab-sweep`).
3) If search meets gate, run independent confirm A/B.
4) If confirm meets gate, run long `scientist improve`.
5) Record corroboration/falsification/knowledge in PopperPad.

This keeps the scientist workflow append-only and falsification-first.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Any

try:
    from popper_pad import PopperPad  # type: ignore
except Exception:  # pragma: no cover - fallback path for alternate invocation styles
    from tools.popper_pad import PopperPad  # type: ignore


def _stable_hash(obj: object) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _run_json(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout_seconds: int,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        text=True,
        capture_output=True,
        timeout=int(timeout_seconds) if int(timeout_seconds) > 0 else None,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "command failed\n"
            f"cmd: {' '.join(cmd)}\n"
            f"code: {proc.returncode}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"failed to parse JSON output for: {' '.join(cmd)}") from exc


def _ab_metrics(obj: dict[str, Any]) -> dict[str, float]:
    agg = dict(obj.get("aggregate") or {})
    lift = dict(agg.get("lift") or {})
    with_arm = dict(agg.get("with_portals") or {})
    without_arm = dict(agg.get("without_portals") or {})
    return {
        "has_lift_rate": float(lift.get("has_lift_rate", 0.0)),
        "solved_rate_delta": float(lift.get("solved_rate_delta", 0.0)),
        "avg_seconds_reduction": float(lift.get("avg_seconds_reduction", 0.0)),
        "with_avg_seconds": float(with_arm.get("avg_seconds", 0.0)),
        "without_avg_seconds": float(without_arm.get("avg_seconds", 0.0)),
    }


def _meets_gate(
    metrics: dict[str, float],
    *,
    min_lift_rate: float,
    min_solved_delta: float,
    min_avg_seconds_reduction: float,
) -> bool:
    return bool(
        float(metrics["has_lift_rate"]) >= float(min_lift_rate)
        and float(metrics["solved_rate_delta"]) >= float(min_solved_delta)
        and float(metrics["avg_seconds_reduction"]) >= float(min_avg_seconds_reduction)
    )


def _metrics_mean(rows: list[dict[str, float]]) -> dict[str, float]:
    if not rows:
        return {
            "has_lift_rate": 0.0,
            "solved_rate_delta": 0.0,
            "avg_seconds_reduction": 0.0,
            "with_avg_seconds": 0.0,
            "without_avg_seconds": 0.0,
        }
    keys = tuple(rows[0].keys())
    out: dict[str, float] = {}
    for k in keys:
        out[str(k)] = float(sum(float(r.get(str(k), 0.0)) for r in rows)) / float(len(rows))
    return out


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    out: list[dict[str, Any]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue
        out.append(json.loads(line))
    return out


def _improve_summary(improve_log_path: Path) -> dict[str, Any]:
    rows = _load_jsonl(improve_log_path)
    campaigns = len(rows)
    archived = [int(r.get("archived_count", 0)) for r in rows]
    promoted = [int(r.get("total_promoted", 0)) for r in rows]
    return {
        "campaigns_completed": campaigns,
        "total_archived_added": int(sum(archived)),
        "min_archived_per_campaign": int(min(archived) if archived else 0),
        "avg_archived_per_campaign": float(sum(archived)) / float(campaigns) if campaigns else 0.0,
        "total_promoted": int(sum(promoted)),
        "meets_long_gate": bool(campaigns >= 3 and (min(archived) if archived else 0) > 0),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="PopperPad-first Morph scientist loop for perps.")
    ap.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--domain", type=str, default="perp_settlement_bounty_farming")
    ap.add_argument("--seed", type=int, default=192000)
    ap.add_argument("--search-runs", type=int, default=1)
    ap.add_argument("--search-seeds", type=int, default=4)
    ap.add_argument("--search-seed-step", type=int, default=1000)
    ap.add_argument("--min-search-pass-rate", type=float, default=1.0)
    ap.add_argument("--confirm-seeds", type=int, default=4)
    ap.add_argument("--confirm-seed-offset", type=int, default=9000)
    ap.add_argument("--confirm-runs", type=int, default=1)
    ap.add_argument("--confirm-seed-step", type=int, default=2000)
    ap.add_argument("--min-confirm-pass-rate", type=float, default=1.0)
    ap.add_argument("--ab-train-instances", type=int, default=12)
    ap.add_argument("--ab-holdout-instances", type=int, default=24)
    ap.add_argument("--ab-max-rounds", type=int, default=2)
    ap.add_argument("--ab-patience-rounds", type=int, default=2)
    ap.add_argument("--ab-max-eval-instances", type=int, default=96)
    ap.add_argument("--ab-max-generated-per-round", type=int, default=48)
    ap.add_argument("--ab-fast-refuter-instances", type=int, default=2)
    ap.add_argument("--ab-max-depth", type=int, default=5)
    ap.add_argument("--ab-max-expanded", type=int, default=220)
    ap.add_argument("--ab-max-wall-seconds", type=int, default=8)
    ap.add_argument("--ab-timeout-seconds", type=int, default=220)
    ap.add_argument("--min-lift-rate", type=float, default=0.75)
    ap.add_argument("--min-solved-delta", type=float, default=0.0)
    ap.add_argument("--min-avg-seconds-reduction", type=float, default=0.0)
    ap.add_argument("--max-campaigns", type=int, default=6)
    ap.add_argument("--campaigns-per-level", type=int, default=2)
    ap.add_argument("--max-rounds-per-campaign", type=int, default=10)
    ap.add_argument("--max-generated-per-round", type=int, default=96)
    ap.add_argument("--max-eval-instances-per-campaign", type=int, default=224)
    ap.add_argument("--improve-timeout-seconds", type=int, default=0)
    ap.add_argument("--pad", type=Path, default=Path("knowledge/popper_pad.jsonl"))
    ap.add_argument("--pad-domain", type=str, default="perps-mech-sci")
    ap.add_argument("--agent", type=str, default="perps-mech-sci")
    ap.add_argument("--run-label", type=str, default="")
    ap.add_argument("--run-root", type=Path, default=Path("runs/mech_sci_iter/popperpad_loop"))
    ap.add_argument("--out", type=Path, default=Path("runs/mech_sci_iter/popperpad_loop/summary.json"))
    args = ap.parse_args()

    repo_root = args.repo_root.resolve()
    run_label = str(args.run_label).strip() or f"pp_{int(time.time())}"
    run_root = (repo_root / args.run_root / run_label).resolve()
    run_root.mkdir(parents=True, exist_ok=True)

    env = dict(os.environ)
    py_path = str((repo_root / "external" / "Morph").resolve())
    env["PYTHONPATH"] = f"{py_path}:{env.get('PYTHONPATH', '')}" if env.get("PYTHONPATH") else py_path

    pad = PopperPad((repo_root / args.pad).resolve())

    profile = {
        "domain": str(args.domain),
        "search_runs": int(args.search_runs),
        "search_seeds": int(args.search_seeds),
        "search_seed_step": int(args.search_seed_step),
        "min_search_pass_rate": float(args.min_search_pass_rate),
        "confirm_seeds": int(args.confirm_seeds),
        "confirm_runs": int(args.confirm_runs),
        "confirm_seed_step": int(args.confirm_seed_step),
        "min_confirm_pass_rate": float(args.min_confirm_pass_rate),
        "ab_train_instances": int(args.ab_train_instances),
        "ab_holdout_instances": int(args.ab_holdout_instances),
        "ab_max_rounds": int(args.ab_max_rounds),
        "ab_patience_rounds": int(args.ab_patience_rounds),
        "ab_max_eval_instances": int(args.ab_max_eval_instances),
        "ab_max_generated_per_round": int(args.ab_max_generated_per_round),
        "ab_fast_refuter_instances": int(args.ab_fast_refuter_instances),
        "ab_max_depth": int(args.ab_max_depth),
        "ab_max_expanded": int(args.ab_max_expanded),
        "ab_max_wall_seconds": int(args.ab_max_wall_seconds),
    }
    profile_hash = _stable_hash(profile)[:16]
    gate = {
        "has_lift_rate_min": float(args.min_lift_rate),
        "solved_rate_delta_min": float(args.min_solved_delta),
        "avg_seconds_reduction_min": float(args.min_avg_seconds_reduction),
    }

    claim = (
        f"Profile {profile_hash} on domain {args.domain} achieves reproducible lift "
        f"(search+confirm) under gate {gate} and survives long improve campaigns."
    )
    test = (
        f"Run ab-sweep search x{int(args.search_runs)} "
        f"(seed+k*{int(args.search_seed_step)}, seeds={int(args.search_seeds)}) and "
        f"confirm x{int(args.confirm_runs)} (seed+{int(args.confirm_seed_offset)}+k*{int(args.confirm_seed_step)}, "
        f"seeds={int(args.confirm_seeds)}), then "
        f"scientist improve(max_campaigns={int(args.max_campaigns)}). Falsify on any gate failure."
    )
    hyp_id = pad.add_hypothesis(
        claim=claim,
        test=test,
        domain=str(args.pad_domain),
        agent=str(args.agent),
        confidence=0.5,
        references=[str(run_root.relative_to(repo_root))],
    )

    def ab_cmd(seed: int, seeds: int, out_dir: Path) -> list[str]:
        return [
            "python3",
            "-m",
            "morph",
            "--json",
            "scientist",
            "ab-sweep",
            "--domain",
            str(args.domain),
            "--out",
            str(out_dir),
            "--seed",
            str(seed),
            "--seeds",
            str(seeds),
            "--train-instances",
            str(args.ab_train_instances),
            "--holdout-instances",
            str(args.ab_holdout_instances),
            "--max-rounds",
            str(args.ab_max_rounds),
            "--patience-rounds",
            str(args.ab_patience_rounds),
            "--max-eval-instances",
            str(args.ab_max_eval_instances),
            "--max-generated-per-round",
            str(args.ab_max_generated_per_round),
            "--fast-refuter-instances",
            str(args.ab_fast_refuter_instances),
            "--max-depth",
            str(args.ab_max_depth),
            "--max-expanded",
            str(args.ab_max_expanded),
            "--max-wall-seconds",
            str(args.ab_max_wall_seconds),
        ]

    summary: dict[str, Any] = {
        "schema": "zenodex/perps-popperpad-loop/v1",
        "run_label": run_label,
        "domain": str(args.domain),
        "profile_hash": profile_hash,
        "hypothesis_id": hyp_id,
        "gate": gate,
    }

    search_out = run_root / "search"
    search_out.mkdir(parents=True, exist_ok=True)
    search_runs_total = max(1, int(args.search_runs))
    search_rows: list[dict[str, Any]] = []
    search_metrics_rows: list[dict[str, float]] = []
    for idx in range(search_runs_total):
        search_seed = int(args.seed) + int(idx) * int(args.search_seed_step)
        run_out = search_out / f"run_{idx:02d}"
        run_out.mkdir(parents=True, exist_ok=True)
        t0 = time.time()
        search_obj = _run_json(
            ab_cmd(int(search_seed), int(args.search_seeds), run_out),
            cwd=repo_root,
            env=env,
            timeout_seconds=int(args.ab_timeout_seconds),
        )
        search_elapsed = time.time() - t0
        (run_out / "ab_sweep.json").write_text(
            json.dumps(search_obj, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        search_metrics = _ab_metrics(search_obj)
        this_pass = _meets_gate(
            search_metrics,
            min_lift_rate=float(args.min_lift_rate),
            min_solved_delta=float(args.min_solved_delta),
            min_avg_seconds_reduction=float(args.min_avg_seconds_reduction),
        )
        search_metrics_rows.append(search_metrics)
        search_rows.append(
            {
                "run_index": int(idx),
                "seed": int(search_seed),
                "seeds": int(args.search_seeds),
                "elapsed_s": float(search_elapsed),
                "metrics": search_metrics,
                "pass": bool(this_pass),
                "artifact": str((run_out / "ab_sweep.json").relative_to(repo_root)),
            }
        )

    search_pass_count = sum(1 for row in search_rows if bool(row.get("pass", False)))
    search_pass_rate = float(search_pass_count) / float(search_runs_total) if search_runs_total else 0.0
    search_metrics_mean = _metrics_mean(search_metrics_rows)
    search_pass = bool(search_pass_rate >= float(args.min_search_pass_rate))
    summary["search"] = {
        "runs": search_rows,
        "runs_total": int(search_runs_total),
        "pass_count": int(search_pass_count),
        "pass_rate": float(search_pass_rate),
        "min_pass_rate": float(args.min_search_pass_rate),
        "metrics_mean": search_metrics_mean,
        "pass": bool(search_pass),
        "artifact_dir": str(search_out.relative_to(repo_root)),
    }

    if not search_pass:
        failed_metrics = [row.get("metrics", {}) for row in search_rows if not bool(row.get("pass", False))]
        pad.falsify(
            hypothesis_id=hyp_id,
            counterexample=(
                f"search_gate_failed pass_rate={search_pass_rate} "
                f"min_pass_rate={float(args.min_search_pass_rate)} "
                f"metrics_mean={search_metrics_mean} failed_metrics={failed_metrics}"
            ),
            agent=str(args.agent),
            evidence_path=str(search_out.relative_to(repo_root)),
        )
        summary["status"] = "falsified_on_search"
        out_path = (repo_root / args.out).resolve()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0

    pad.corroborate(
        hypothesis_id=hyp_id,
        test_description=(
            f"search A/B passed gate with pass_rate={search_pass_rate} "
            f"metrics_mean={search_metrics_mean}"
        ),
        severity="high",
        agent=str(args.agent),
        evidence_path=str(search_out.relative_to(repo_root)),
    )

    confirm_out = run_root / "confirm"
    confirm_out.mkdir(parents=True, exist_ok=True)
    confirm_runs_total = max(1, int(args.confirm_runs))
    confirm_rows: list[dict[str, Any]] = []
    confirm_metrics_rows: list[dict[str, float]] = []
    for idx in range(confirm_runs_total):
        confirm_seed = int(args.seed) + int(args.confirm_seed_offset) + int(idx) * int(args.confirm_seed_step)
        run_out = confirm_out / f"run_{idx:02d}"
        run_out.mkdir(parents=True, exist_ok=True)
        t1 = time.time()
        confirm_obj = _run_json(
            ab_cmd(confirm_seed, int(args.confirm_seeds), run_out),
            cwd=repo_root,
            env=env,
            timeout_seconds=int(args.ab_timeout_seconds),
        )
        confirm_elapsed = time.time() - t1
        (run_out / "ab_sweep.json").write_text(json.dumps(confirm_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        confirm_metrics = _ab_metrics(confirm_obj)
        this_pass = _meets_gate(
            confirm_metrics,
            min_lift_rate=float(args.min_lift_rate),
            min_solved_delta=float(args.min_solved_delta),
            min_avg_seconds_reduction=float(args.min_avg_seconds_reduction),
        )
        confirm_metrics_rows.append(confirm_metrics)
        confirm_rows.append(
            {
                "run_index": int(idx),
                "seed": int(confirm_seed),
                "seeds": int(args.confirm_seeds),
                "elapsed_s": float(confirm_elapsed),
                "metrics": confirm_metrics,
                "pass": bool(this_pass),
                "artifact": str((run_out / "ab_sweep.json").relative_to(repo_root)),
            }
        )

    confirm_pass_count = sum(1 for row in confirm_rows if bool(row.get("pass", False)))
    confirm_pass_rate = float(confirm_pass_count) / float(confirm_runs_total) if confirm_runs_total else 0.0
    confirm_metrics_mean = _metrics_mean(confirm_metrics_rows)
    confirm_pass = bool(confirm_pass_rate >= float(args.min_confirm_pass_rate))
    summary["confirm"] = {
        "runs": confirm_rows,
        "runs_total": int(confirm_runs_total),
        "pass_count": int(confirm_pass_count),
        "pass_rate": float(confirm_pass_rate),
        "min_pass_rate": float(args.min_confirm_pass_rate),
        "metrics_mean": confirm_metrics_mean,
        "pass": bool(confirm_pass),
        "artifact_dir": str(confirm_out.relative_to(repo_root)),
    }

    if not confirm_pass:
        failed_metrics = [row.get("metrics", {}) for row in confirm_rows if not bool(row.get("pass", False))]
        pad.falsify(
            hypothesis_id=hyp_id,
            counterexample=(
                f"confirm_gate_failed pass_rate={confirm_pass_rate} "
                f"min_pass_rate={float(args.min_confirm_pass_rate)} "
                f"metrics_mean={confirm_metrics_mean} failed_metrics={failed_metrics}"
            ),
            agent=str(args.agent),
            evidence_path=str(confirm_out.relative_to(repo_root)),
        )
        summary["status"] = "falsified_on_confirm"
        out_path = (repo_root / args.out).resolve()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0

    pad.corroborate(
        hypothesis_id=hyp_id,
        test_description=(
            f"confirm A/B passed gate with pass_rate={confirm_pass_rate} "
            f"metrics_mean={confirm_metrics_mean}"
        ),
        severity="high",
        agent=str(args.agent),
        evidence_path=str(confirm_out.relative_to(repo_root)),
    )

    improve_out = run_root / "improve"
    archive_out = run_root / "archive"
    improve_out.mkdir(parents=True, exist_ok=True)
    archive_out.mkdir(parents=True, exist_ok=True)
    improve_cmd = [
        "python3",
        "-m",
        "morph",
        "scientist",
        "improve",
        "--domains",
        str(args.domain),
        "--archive-dir",
        str(archive_out),
        "--out",
        str(improve_out),
        "--seed",
        str(args.seed),
        "--max-campaigns",
        str(args.max_campaigns),
        "--campaigns-per-level",
        str(args.campaigns_per_level),
        "--max-rounds-per-campaign",
        str(args.max_rounds_per_campaign),
        "--max-generated-per-round",
        str(args.max_generated_per_round),
        "--max-eval-instances-per-campaign",
        str(args.max_eval_instances_per_campaign),
    ]
    t2 = time.time()
    proc = subprocess.run(
        improve_cmd,
        cwd=str(repo_root),
        env=env,
        text=True,
        capture_output=True,
        timeout=int(args.improve_timeout_seconds) if int(args.improve_timeout_seconds) > 0 else None,
    )
    improve_elapsed = time.time() - t2
    if proc.returncode != 0:
        raise RuntimeError(
            "improve command failed\n"
            f"cmd: {' '.join(improve_cmd)}\n"
            f"code: {proc.returncode}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )

    improve_log = improve_out / "improvement_log.jsonl"
    improve_summary = _improve_summary(improve_log)
    summary["improve"] = {
        "elapsed_s": float(improve_elapsed),
        "summary": improve_summary,
        "artifact": str(improve_log.relative_to(repo_root)),
    }

    if bool(improve_summary.get("meets_long_gate", False)):
        pad.corroborate(
            hypothesis_id=hyp_id,
            test_description=f"long improve passed durability gate summary={improve_summary}",
            severity="extreme",
            agent=str(args.agent),
            evidence_path=str(improve_log.relative_to(repo_root)),
        )
        pad.knowledge(
            fact=(
                f"Domain {args.domain} profile {profile_hash} is promotion-grade under gate {gate} "
                f"with long-campaign durability {improve_summary}"
            ),
            evidence=str(improve_log.relative_to(repo_root)),
            domain=str(args.pad_domain),
            agent=str(args.agent),
            confidence=0.9,
            references=[
                str(search_out.relative_to(repo_root)),
                str(confirm_out.relative_to(repo_root)),
                str(improve_log.relative_to(repo_root)),
            ],
        )
        summary["status"] = "promotion_grade"
    else:
        pad.falsify(
            hypothesis_id=hyp_id,
            counterexample=f"long_gate_failed summary={improve_summary}",
            agent=str(args.agent),
            evidence_path=str(improve_log.relative_to(repo_root)),
        )
        summary["status"] = "falsified_on_long_gate"

    out_path = (repo_root / args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
