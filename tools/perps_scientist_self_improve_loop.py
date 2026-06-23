#!/usr/bin/env python3
"""Run a repeatable Morph perps self-improvement loop.

Workflow:
1) Run matched A/B sweeps per domain.
2) Gate domains on sustained lift criteria.
3) Run longer `scientist improve` campaigns on gated domains.
4) Emit one summary JSON artifact.
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


def _run(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout_seconds: int | None = None,
) -> str:
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            env=env,
            text=True,
            capture_output=True,
            timeout=(int(timeout_seconds) if timeout_seconds and int(timeout_seconds) > 0 else None),
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            "command timed out\n"
            f"cmd: {' '.join(cmd)}\n"
            f"timeout_seconds: {int(timeout_seconds) if timeout_seconds else 0}\n"
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


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue
        rows.append(json.loads(line))
    return rows


def _append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(row, sort_keys=True) + "\n")


def _stable_hash(obj: object) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _ab_gate(
    ab: dict[str, Any],
    *,
    min_lift_rate: float,
    min_solved_delta: float,
    min_avg_seconds_reduction: float,
) -> dict[str, Any]:
    agg = dict((ab.get("aggregate") or {}))
    lift = dict((agg.get("lift") or {}))
    has_lift_rate = float(lift.get("has_lift_rate", 0.0))
    solved_delta = float(lift.get("solved_rate_delta", 0.0))
    avg_seconds_reduction = float(lift.get("avg_seconds_reduction", 0.0))
    return {
        "has_lift_rate": has_lift_rate,
        "solved_rate_delta": solved_delta,
        "avg_seconds_reduction": avg_seconds_reduction,
        "meets_gate": bool(
            has_lift_rate >= min_lift_rate
            and solved_delta >= min_solved_delta
            and avg_seconds_reduction >= min_avg_seconds_reduction
        ),
    }


def _improve_summary(improve_log_path: Path) -> dict[str, Any]:
    rows = _load_jsonl(improve_log_path)
    campaigns = len(rows)
    archived = [int(r.get("archived_count", 0)) for r in rows]
    promoted = [int(r.get("total_promoted", 0)) for r in rows]
    return {
        "campaigns_completed": campaigns,
        "total_archived_added": int(sum(archived)),
        "min_archived_per_campaign": int(min(archived) if archived else 0),
        "avg_archived_per_campaign": (float(sum(archived)) / float(campaigns)) if campaigns else 0.0,
        "total_promoted": int(sum(promoted)),
        "meets_long_gate": bool(campaigns >= 3 and (min(archived) if archived else 0) > 0),
    }


def _default_domains() -> tuple[str, ...]:
    return (
        "perp_oracle_manipulation_reward_subsidy",
        "perp_settlement_bounty_farming",
        "perp_funding_rate_gaming",
        "perp_oracle_manipulation",
        "perp_oracle_manipulation_lp",
        "perp_collateral_depeg",
    )


def _domain_code_update_template(domain: str) -> dict[str, Any]:
    if str(domain) == "perp_oracle_manipulation_reward_subsidy":
        return {
            "domain": str(domain),
            "target_files": [
                "src/core/perp_v2/engine.py",
                "src/core/perp_v2/guards.py",
                "src/core/perp_v2/math.py",
                "src/integration/perp_engine.py",
                "tests/core/test_perp_v2/test_engine.py",
                "tests/integration/test_perp_engine.py",
            ],
            "intent": "harden reward-subsidy anti-manipulation paths with validated scientist discoveries",
            "required_invariants": [
                "integer-only deterministic transitions",
                "solved-quality non-regression",
                "fail-closed guards for malformed or stale oracle/funding states",
            ],
        }
    if str(domain) == "perp_settlement_bounty_farming":
        return {
            "domain": str(domain),
            "target_files": [
                "src/core/perp_v2/engine.py",
                "src/core/perp_v2/guards.py",
                "src/integration/perp_engine.py",
                "tests/core/test_perp_v2/test_engine.py",
                "tests/integration/test_perp_engine.py",
            ],
            "intent": "reduce keeper bounty farming surface while preserving deterministic liquidation semantics",
            "required_invariants": [
                "liquidation correctness under bounded oracle move",
                "no tactic/checker mismatch on mutable bounty fields",
                "no solvability regressions in valid liquidation scenarios",
            ],
        }
    if str(domain) == "perp_funding_rate_gaming":
        return {
            "domain": str(domain),
            "target_files": [
                "src/core/perp_v2/math.py",
                "src/core/perp_v2/updates.py",
                "src/integration/perp_engine.py",
                "tests/core/test_perp_v2/test_math.py",
                "tests/integration/test_perp_engine.py",
            ],
            "intent": "tighten funding arithmetic/budget-balance behavior against rounding extraction vectors",
            "required_invariants": [
                "funding budget-balance or explicit fail-closed rejection",
                "deterministic sign and rounding behavior across long/short legs",
                "collateral non-negativity and no hidden overflow path",
            ],
        }
    if str(domain) == "perp_oracle_manipulation_lp":
        return {
            "domain": str(domain),
            "target_files": [
                "src/core/perp_v2/engine.py",
                "src/core/perp_v2/guards.py",
                "src/integration/perp_engine.py",
                "tests/core/test_perp_v2/test_engine.py",
                "tests/integration/test_perp_engine.py",
            ],
            "intent": "harden attacker-as-LP oracle-manipulation assumptions in production guardrails",
            "required_invariants": [
                "risk checks must account for LP-fee recapture by attackers",
                "deterministic integer-only non-recapturable cost floor",
                "no solved-quality regression on prior oracle-manipulation reward/subsidy suites",
            ],
        }
    return {
        "domain": str(domain),
        "target_files": [],
        "intent": "translate validated scientist lift into production code hardening",
        "required_invariants": [
            "deterministic integer semantics",
            "non-regression on solved quality",
        ],
    }


def _ab_profile(
    *,
    domain: str,
    seed_start: int,
    seeds: int,
    args: argparse.Namespace,
) -> dict[str, Any]:
    return {
        "domain": str(domain),
        "seed_start": int(seed_start),
        "seeds": int(seeds),
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
        "ab_run_timeout_seconds": int(args.ab_run_timeout_seconds),
        "ab_n_vars": int(args.ab_n_vars),
        "ab_n_clauses": int(args.ab_n_clauses),
        "ab_k": int(args.ab_k),
        "ab_tautology_per_var": int(args.ab_tautology_per_var),
        "ab_duplicate_factor": int(args.ab_duplicate_factor),
    }


def _count_prior_no_lift(
    *,
    ledger_rows: list[dict[str, Any]],
    domain: str,
    profile_hash: str,
    no_lift_threshold: float,
    min_solved_delta: float,
    min_avg_seconds_reduction: float,
) -> int:
    cnt = 0
    for row in ledger_rows:
        if str(row.get("event")) != "ab_result":
            continue
        if str(row.get("domain")) != str(domain):
            continue
        if str(row.get("profile_hash")) != str(profile_hash):
            continue
        has_lift_rate = float(row.get("has_lift_rate", 0.0))
        solved_delta = float(row.get("solved_rate_delta", 0.0))
        avg_seconds_reduction = float(row.get("avg_seconds_reduction", 0.0))
        if (
            (has_lift_rate <= float(no_lift_threshold) or avg_seconds_reduction < float(min_avg_seconds_reduction))
            and solved_delta >= float(min_solved_delta)
        ):
            cnt += 1
    return cnt


def main() -> int:
    ap = argparse.ArgumentParser(description="Run Morph perps self-improvement loop.")
    ap.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--domains", type=str, default=",".join(_default_domains()))
    ap.add_argument("--seed", type=int, default=10_000)
    ap.add_argument("--seeds", type=int, default=10)
    ap.add_argument("--ab-base-dir", type=Path, default=Path("runs/mech_sci_iter/loop_ab"))
    ap.add_argument("--improve-base-dir", type=Path, default=Path("runs/mech_sci_iter/loop_improve"))
    ap.add_argument("--archive-base-dir", type=Path, default=Path("runs/mech_sci_iter/loop_archive"))
    ap.add_argument("--min-lift-rate", type=float, default=0.8)
    ap.add_argument("--min-solved-delta", type=float, default=0.0)
    ap.add_argument("--min-avg-seconds-reduction", type=float, default=0.0)
    ap.add_argument("--max-campaigns", type=int, default=6)
    ap.add_argument("--campaigns-per-level", type=int, default=2)
    ap.add_argument("--max-rounds-per-campaign", type=int, default=8)
    ap.add_argument("--max-generated-per-round", type=int, default=96)
    ap.add_argument("--max-eval-instances-per-campaign", type=int, default=192)
    ap.add_argument("--ab-train-instances", type=int, default=12)
    ap.add_argument("--ab-holdout-instances", type=int, default=24)
    ap.add_argument("--ab-max-rounds", type=int, default=2)
    ap.add_argument("--ab-patience-rounds", type=int, default=2)
    ap.add_argument("--ab-max-eval-instances", type=int, default=128)
    ap.add_argument("--ab-max-generated-per-round", type=int, default=48)
    ap.add_argument("--ab-fast-refuter-instances", type=int, default=2)
    ap.add_argument("--ab-max-depth", type=int, default=5)
    ap.add_argument("--ab-max-expanded", type=int, default=260)
    ap.add_argument("--ab-max-wall-seconds", type=int, default=0)
    ap.add_argument("--ab-run-timeout-seconds", type=int, default=0)
    ap.add_argument("--ab-n-vars", type=int, default=40)
    ap.add_argument("--ab-n-clauses", type=int, default=120)
    ap.add_argument("--ab-k", type=int, default=3)
    ap.add_argument("--ab-tautology-per-var", type=int, default=2)
    ap.add_argument("--ab-duplicate-factor", type=int, default=2)
    ap.add_argument("--evidence-ledger", type=Path, default=Path("runs/mech_sci_iter/evidence/perps_scientist_ledger.jsonl"))
    ap.add_argument("--run-label", type=str, default="")
    ap.add_argument("--no-lift-threshold", type=float, default=0.2)
    ap.add_argument("--repeat-block-after", type=int, default=1)
    ap.add_argument("--allow-repeat-no-lift-profiles", action="store_true", default=False)
    ap.add_argument("--out", type=Path, default=Path("runs/mech_sci_iter/loop_summary.json"))
    args = ap.parse_args()

    repo_root = args.repo_root.resolve()
    domains = tuple(d.strip() for d in str(args.domains).split(",") if d.strip())
    if not domains:
        raise SystemExit("no domains provided")

    env = dict(os.environ)
    py_path = str((repo_root / "external" / "Morph").resolve())
    env["PYTHONPATH"] = f"{py_path}:{env.get('PYTHONPATH', '')}" if env.get("PYTHONPATH") else py_path

    ab_base = (repo_root / args.ab_base_dir).resolve()
    improve_base = (repo_root / args.improve_base_dir).resolve()
    archive_base = (repo_root / args.archive_base_dir).resolve()
    ab_base.mkdir(parents=True, exist_ok=True)
    improve_base.mkdir(parents=True, exist_ok=True)
    archive_base.mkdir(parents=True, exist_ok=True)
    evidence_path = (repo_root / args.evidence_ledger).resolve()
    ledger_rows = _load_jsonl(evidence_path)
    run_id = _stable_hash(
        {
            "seed": int(args.seed),
            "seeds": int(args.seeds),
            "domains": domains,
            "run_label": str(args.run_label),
            "time_s": int(time.time()),
        }
    )[:16]

    summary: dict[str, Any] = {
        "schema": "morph/perps-self-improve-loop/v1",
        "run_id": run_id,
        "run_label": str(args.run_label),
        "domains": {},
        "selected_for_improve": [],
        "code_update_candidates": [],
    }
    _append_jsonl(
        evidence_path,
        {
            "event": "run_start",
            "run_id": run_id,
            "run_label": str(args.run_label),
            "ts_s": time.time(),
            "domains": list(domains),
            "seed": int(args.seed),
            "seeds": int(args.seeds),
        },
    )

    for idx, domain in enumerate(domains):
        seed_start = int(args.seed) + idx * 100
        ab_out = ab_base / domain
        ab_out.mkdir(parents=True, exist_ok=True)
        profile = _ab_profile(domain=domain, seed_start=seed_start, seeds=int(args.seeds), args=args)
        profile_hash = _stable_hash(profile)
        prior_no_lift = _count_prior_no_lift(
            ledger_rows=ledger_rows,
            domain=domain,
            profile_hash=profile_hash,
            no_lift_threshold=float(args.no_lift_threshold),
            min_solved_delta=float(args.min_solved_delta),
            min_avg_seconds_reduction=float(args.min_avg_seconds_reduction),
        )
        if (not bool(args.allow_repeat_no_lift_profiles)) and prior_no_lift >= int(args.repeat_block_after):
            skip_msg = (
                f"skipped repeated no-lift profile (domain={domain}, "
                f"profile_hash={profile_hash}, prior_no_lift={prior_no_lift})"
            )
            gate = {
                "has_lift_rate": 0.0,
                "solved_rate_delta": 0.0,
                "avg_seconds_reduction": 0.0,
                "meets_gate": False,
            }
            summary["domains"][domain] = {
                "ab_sweep_path": None,
                "ab_gate": gate,
                "ab_profile_hash": profile_hash,
                "skipped_reason": skip_msg,
            }
            _append_jsonl(
                evidence_path,
                {
                    "event": "ab_skip_repeat_no_lift",
                    "run_id": run_id,
                    "domain": domain,
                    "profile_hash": profile_hash,
                    "prior_no_lift": int(prior_no_lift),
                    "no_lift_threshold": float(args.no_lift_threshold),
                    "min_avg_seconds_reduction": float(args.min_avg_seconds_reduction),
                    "ts_s": time.time(),
                },
            )
            continue

        ab_stdout = _run(
            [
                "python3",
                "-m",
                "morph",
                "--json",
                "scientist",
                "ab-sweep",
                "--domain",
                domain,
                "--out",
                str(ab_out),
                "--seed",
                str(seed_start),
                "--seeds",
                str(args.seeds),
                "--train-instances",
                str(args.ab_train_instances),
                "--holdout-instances",
                str(args.ab_holdout_instances),
                "--n-vars",
                str(args.ab_n_vars),
                "--n-clauses",
                str(args.ab_n_clauses),
                "--k",
                str(args.ab_k),
                "--tautology-per-var",
                str(args.ab_tautology_per_var),
                "--duplicate-factor",
                str(args.ab_duplicate_factor),
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
            ]
            + (
                ["--max-wall-seconds", str(args.ab_max_wall_seconds)]
                if int(args.ab_max_wall_seconds) > 0
                else []
            ),
            cwd=repo_root,
            env=env,
            timeout_seconds=(int(args.ab_run_timeout_seconds) if int(args.ab_run_timeout_seconds) > 0 else None),
        )

        try:
            ab_obj = json.loads(ab_stdout)
        except json.JSONDecodeError as exc:
            raise RuntimeError(f"failed to parse ab-sweep JSON output for domain={domain}: {exc}") from exc

        ab_path = ab_out / "ab_sweep.json"
        ab_path.write_text(json.dumps(ab_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        gate = _ab_gate(
            ab_obj,
            min_lift_rate=float(args.min_lift_rate),
            min_solved_delta=float(args.min_solved_delta),
            min_avg_seconds_reduction=float(args.min_avg_seconds_reduction),
        )

        summary["domains"][domain] = {
            "ab_sweep_path": str(ab_path.relative_to(repo_root)),
            "ab_gate": gate,
            "ab_profile_hash": profile_hash,
            "prior_no_lift": int(prior_no_lift),
        }
        _append_jsonl(
            evidence_path,
            {
                "event": "ab_result",
                "run_id": run_id,
                "domain": domain,
                "profile_hash": profile_hash,
                "has_lift_rate": float(gate["has_lift_rate"]),
                "solved_rate_delta": float(gate["solved_rate_delta"]),
                "avg_seconds_reduction": float(gate["avg_seconds_reduction"]),
                "meets_gate": bool(gate["meets_gate"]),
                "ab_sweep_path": str(ab_path.relative_to(repo_root)),
                "ts_s": time.time(),
            },
        )

        if gate["meets_gate"]:
            summary["selected_for_improve"].append(domain)

    for domain in summary["selected_for_improve"]:
        improve_out = improve_base / domain
        archive_dir = archive_base / domain
        improve_out.mkdir(parents=True, exist_ok=True)
        archive_dir.mkdir(parents=True, exist_ok=True)

        _run(
            [
                "python3",
                "-m",
                "morph",
                "scientist",
                "improve",
                "--domains",
                domain,
                "--archive-dir",
                str(archive_dir),
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
            ],
            cwd=repo_root,
            env=env,
        )

        improve_log = improve_out / "improvement_log.jsonl"
        improve_summary = _improve_summary(improve_log)
        summary["domains"][domain]["improve"] = {
            "improve_log_path": str(improve_log.relative_to(repo_root)),
            "summary": improve_summary,
        }
        if bool(improve_summary.get("meets_long_gate", False)):
            cand = dict(_domain_code_update_template(str(domain)))
            cand.update(
                {
                    "status": "ready_for_implementation",
                    "evidence": {
                        "ab_sweep_path": summary["domains"][domain].get("ab_sweep_path"),
                        "improve_log_path": str(improve_log.relative_to(repo_root)),
                    },
                }
            )
            summary["code_update_candidates"].append(cand)
            _append_jsonl(
                evidence_path,
                {
                    "event": "code_update_candidate",
                    "run_id": run_id,
                    "domain": domain,
                    "status": "ready_for_implementation",
                    "ab_sweep_path": summary["domains"][domain].get("ab_sweep_path"),
                    "improve_log_path": str(improve_log.relative_to(repo_root)),
                    "target_files": cand.get("target_files", []),
                    "ts_s": time.time(),
                },
            )
        else:
            cand = dict(_domain_code_update_template(str(domain)))
            cand.update(
                {
                    "status": "needs_long_campaign_validation",
                    "evidence": {
                        "ab_sweep_path": summary["domains"][domain].get("ab_sweep_path"),
                        "improve_log_path": str(improve_log.relative_to(repo_root)),
                    },
                }
            )
            summary["code_update_candidates"].append(cand)
        _append_jsonl(
            evidence_path,
            {
                "event": "improve_result",
                "run_id": run_id,
                "domain": domain,
                "improve_log_path": str(improve_log.relative_to(repo_root)),
                "campaigns_completed": int(improve_summary.get("campaigns_completed", 0)),
                "total_archived_added": int(improve_summary.get("total_archived_added", 0)),
                "min_archived_per_campaign": int(improve_summary.get("min_archived_per_campaign", 0)),
                "meets_long_gate": bool(improve_summary.get("meets_long_gate", False)),
                "ts_s": time.time(),
            },
        )

    out_path = (repo_root / args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _append_jsonl(
        evidence_path,
        {
            "event": "run_summary",
            "run_id": run_id,
            "run_label": str(args.run_label),
            "selected_for_improve": list(summary.get("selected_for_improve", [])),
            "out_path": str(out_path.relative_to(repo_root)),
            "ts_s": time.time(),
        },
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
