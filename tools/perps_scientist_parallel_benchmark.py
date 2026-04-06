#!/usr/bin/env python3
"""Benchmark parallel Morph scientist A/B sweeps across perps domains.

This launcher runs identical domain workloads under different parallel-worker
counts and reports wall-clock speedup plus per-domain lift metrics.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Any


def _default_domains() -> tuple[str, ...]:
    return (
        "perp_oracle_manipulation_reward_subsidy",
        "perp_settlement_bounty_farming",
        "perp_funding_rate_gaming",
        "perp_oracle_manipulation",
    )


def _run(cmd: list[str], *, cwd: Path, env: dict[str, str], timeout_seconds: int | None = None) -> str:
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            env=env,
            text=True,
            capture_output=True,
            timeout=timeout_seconds if timeout_seconds and timeout_seconds > 0 else None,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = None
        if exc.timeout is not None:
            elapsed = f"{float(exc.timeout):.1f}s"
        raise TimeoutError(
            "command timed out\n"
            f"cmd: {' '.join(cmd)}\n"
            f"timeout: {elapsed or 'unknown'}\n"
            f"stdout:\n{exc.stdout or ''}\n"
            f"stderr:\n{exc.stderr or ''}"
        ) from exc
    if proc.returncode != 0:
        raise RuntimeError(
            "command failed\n"
            f"cmd: {' '.join(cmd)}\n"
            f"code: {proc.returncode}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )
    return proc.stdout


def _parse_workers_list(raw: str) -> list[int]:
    out: list[int] = []
    for tok in raw.split(","):
        t = tok.strip()
        if not t:
            continue
        n = int(t)
        if n <= 0:
            raise ValueError("worker counts must be positive")
        out.append(n)
    if not out:
        raise ValueError("workers list is empty")
    return out


def _rel(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def _run_domain_ab_sweep(
    *,
    repo_root: Path,
    env: dict[str, str],
    domain: str,
    seed_start: int,
    seeds: int,
    out_dir: Path,
    ab_args: dict[str, int],
) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.perf_counter()
    cmd = [
        "python3",
        "-m",
        "morph",
        "--json",
        "scientist",
        "ab-sweep",
        "--domain",
        str(domain),
        "--out",
        str(out_dir),
        "--seed",
        str(seed_start),
        "--seeds",
        str(seeds),
        "--train-instances",
        str(ab_args["train_instances"]),
        "--holdout-instances",
        str(ab_args["holdout_instances"]),
        "--max-rounds",
        str(ab_args["max_rounds"]),
        "--patience-rounds",
        str(ab_args["patience_rounds"]),
        "--max-eval-instances",
        str(ab_args["max_eval_instances"]),
        "--max-generated-per-round",
        str(ab_args["max_generated_per_round"]),
        "--fast-refuter-instances",
        str(ab_args["fast_refuter_instances"]),
        "--max-depth",
        str(ab_args["max_depth"]),
        "--max-expanded",
        str(ab_args["max_expanded"]),
        "--n-vars",
        str(ab_args["n_vars"]),
        "--n-clauses",
        str(ab_args["n_clauses"]),
        "--k",
        str(ab_args["k"]),
        "--tautology-per-var",
        str(ab_args["tautology_per_var"]),
        "--duplicate-factor",
        str(ab_args["duplicate_factor"]),
    ]

    try:
        stdout = _run(
            cmd,
            cwd=repo_root,
            env=env,
            timeout_seconds=int(ab_args.get("run_timeout_seconds", 0) or 0),
        )
    except Exception as exc:
        elapsed_s = time.perf_counter() - t0
        status = "timeout" if isinstance(exc, TimeoutError) else "error"
        return {
            "domain": str(domain),
            "seed_start": int(seed_start),
            "seeds": int(seeds),
            "status": status,
            "elapsed_s": float(elapsed_s),
            "error": str(exc),
        }

    elapsed_s = time.perf_counter() - t0
    try:
        obj = json.loads(stdout)
    except Exception as exc:
        return {
            "domain": str(domain),
            "seed_start": int(seed_start),
            "seeds": int(seeds),
            "status": "error",
            "elapsed_s": float(elapsed_s),
            "error": f"invalid JSON output: {exc}",
        }
    ab_sweep_path = out_dir / "ab_sweep.json"
    ab_sweep_path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    agg = dict(obj.get("aggregate") or {})
    lift = dict(agg.get("lift") or {})
    with_arm = dict(agg.get("with_portals") or {})
    without_arm = dict(agg.get("without_portals") or {})

    return {
        "domain": str(domain),
        "seed_start": int(seed_start),
        "seeds": int(seeds),
        "status": "ok",
        "elapsed_s": float(elapsed_s),
        "ab_sweep_path": _rel(ab_sweep_path, repo_root),
        "lift": {
            "has_lift_rate": float(lift.get("has_lift_rate", 0.0)),
            "avg_seconds_reduction": float(lift.get("avg_seconds_reduction", 0.0)),
            "solved_rate_delta": float(lift.get("solved_rate_delta", 0.0)),
            "with_avg_seconds": float(with_arm.get("avg_seconds", 0.0)),
            "without_avg_seconds": float(without_arm.get("avg_seconds", 0.0)),
        },
    }


def _run_worker_benchmark(
    *,
    repo_root: Path,
    env: dict[str, str],
    workers: int,
    domains: tuple[str, ...],
    seed: int,
    seeds: int,
    run_dir: Path,
    ab_args: dict[str, int],
) -> dict[str, Any]:
    run_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.perf_counter()

    results: list[dict[str, Any]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=int(workers)) as pool:
        future_to_domain: dict[concurrent.futures.Future[dict[str, Any]], str] = {}
        for idx, domain in enumerate(domains):
            seed_start = int(seed) + int(idx * 100)
            out_dir = run_dir / domain
            fut = pool.submit(
                _run_domain_ab_sweep,
                repo_root=repo_root,
                env=env,
                domain=domain,
                seed_start=seed_start,
                seeds=seeds,
                out_dir=out_dir,
                ab_args=ab_args,
            )
            future_to_domain[fut] = domain

        for fut in concurrent.futures.as_completed(future_to_domain):
            results.append(fut.result())

    wall_s = time.perf_counter() - t0
    results_sorted = sorted(results, key=lambda r: str(r["domain"]))
    ok_count = sum(1 for r in results_sorted if str(r.get("status", "ok")) == "ok")
    timeout_count = sum(1 for r in results_sorted if str(r.get("status", "")) == "timeout")
    error_count = sum(1 for r in results_sorted if str(r.get("status", "")) == "error")
    return {
        "workers": int(workers),
        "domains": results_sorted,
        "wall_seconds": float(wall_s),
        "ok_count": int(ok_count),
        "timeout_count": int(timeout_count),
        "error_count": int(error_count),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Benchmark parallel Morph scientist A/B sweeps for perps domains.")
    ap.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--domains", type=str, default=",".join(_default_domains()))
    ap.add_argument("--seed", type=int, default=20_000)
    ap.add_argument("--seeds", type=int, default=2)
    ap.add_argument("--workers-list", type=str, default="1,2,4")
    ap.add_argument("--run-label", type=str, default="")
    ap.add_argument("--runs-root", type=Path, default=Path("runs/mech_sci_iter/parallel_bench"))
    ap.add_argument("--out", type=Path, default=Path("runs/mech_sci_iter/parallel_bench/benchmark_summary.json"))

    # A/B budget controls.
    ap.add_argument("--train-instances", type=int, default=12)
    ap.add_argument("--holdout-instances", type=int, default=24)
    ap.add_argument("--max-rounds", type=int, default=2)
    ap.add_argument("--patience-rounds", type=int, default=2)
    ap.add_argument("--max-eval-instances", type=int, default=128)
    ap.add_argument("--max-generated-per-round", type=int, default=48)
    ap.add_argument("--fast-refuter-instances", type=int, default=2)
    ap.add_argument("--max-depth", type=int, default=5)
    ap.add_argument("--max-expanded", type=int, default=260)
    ap.add_argument("--n-vars", type=int, default=40)
    ap.add_argument("--n-clauses", type=int, default=120)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--tautology-per-var", type=int, default=2)
    ap.add_argument("--duplicate-factor", type=int, default=2)
    ap.add_argument(
        "--run-timeout-seconds",
        type=int,
        default=0,
        help="Hard timeout per domain ab-sweep (0 disables timeout).",
    )
    args = ap.parse_args()

    repo_root = args.repo_root.resolve()
    domains = tuple(d.strip() for d in str(args.domains).split(",") if d.strip())
    if not domains:
        raise SystemExit("no domains provided")
    workers_list = _parse_workers_list(str(args.workers_list))

    env = dict(os.environ)
    py_path = str((repo_root / "external" / "Morph").resolve())
    env["PYTHONPATH"] = f"{py_path}:{env.get('PYTHONPATH', '')}" if env.get("PYTHONPATH") else py_path

    run_label = str(args.run_label).strip() or str(int(time.time()))
    bench_root = (repo_root / args.runs_root / run_label).resolve()
    bench_root.mkdir(parents=True, exist_ok=True)

    ab_args = {
        "train_instances": int(args.train_instances),
        "holdout_instances": int(args.holdout_instances),
        "max_rounds": int(args.max_rounds),
        "patience_rounds": int(args.patience_rounds),
        "max_eval_instances": int(args.max_eval_instances),
        "max_generated_per_round": int(args.max_generated_per_round),
        "fast_refuter_instances": int(args.fast_refuter_instances),
        "max_depth": int(args.max_depth),
        "max_expanded": int(args.max_expanded),
        "n_vars": int(args.n_vars),
        "n_clauses": int(args.n_clauses),
        "k": int(args.k),
        "tautology_per_var": int(args.tautology_per_var),
        "duplicate_factor": int(args.duplicate_factor),
        "run_timeout_seconds": int(args.run_timeout_seconds),
    }

    runs: list[dict[str, Any]] = []
    for workers in workers_list:
        run_dir = bench_root / f"workers_{workers}"
        runs.append(
            _run_worker_benchmark(
                repo_root=repo_root,
                env=env,
                workers=workers,
                domains=domains,
                seed=int(args.seed),
                seeds=int(args.seeds),
                run_dir=run_dir,
                ab_args=ab_args,
            )
        )

    base_workers = int(workers_list[0])
    base = next(r for r in runs if int(r["workers"]) == base_workers)
    base_wall_s = float(base["wall_seconds"])
    for run in runs:
        wall_s = float(run["wall_seconds"])
        run["speedup_vs_base"] = (base_wall_s / wall_s) if wall_s > 0 else 0.0

    summary = {
        "schema": "morph/perps-parallel-benchmark/v1",
        "run_label": run_label,
        "bench_root": _rel(bench_root, repo_root),
        "seed": int(args.seed),
        "seeds": int(args.seeds),
        "domains": list(domains),
        "workers_list": list(workers_list),
        "ab_args": ab_args,
        "base_workers": base_workers,
        "runs": runs,
    }

    out_path = (repo_root / args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
