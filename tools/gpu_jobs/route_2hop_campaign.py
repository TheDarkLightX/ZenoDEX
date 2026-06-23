#!/usr/bin/env python3
"""
Route improvement v1 campaign runner (internal).

Runs many independent jobs through:
1) GPU-assisted search (untrusted ranking hint)
2) Deterministic witness verification (fail-closed replay)

This tool is designed to:
- generate regression corpora of verified "improvement witnesses",
- benchmark CPU vs GPU ranking backends,
- prototype "useful work" markets (miners propose; chain verifies).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

# Allow `python3 tools/gpu_jobs/...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402
from tools.gpu_jobs.route_2hop_search_cpmm import compute_route_improvement_witness_v1  # noqa: E402
from tools.proof_verifiers.route_improvement_v1 import verify_route_improvement_witness  # noqa: E402


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_list(value: Any, *, name: str) -> List[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return list(value)


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _dump_json_line(obj: Mapping[str, Any]) -> str:
    # Keep JSONL deterministic and compact.
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"


def _job_digest(job: Mapping[str, Any], pools: Sequence[Mapping[str, Any]]) -> str:
    pools_norm = [dict(p) for p in pools]
    pools_norm.sort(key=lambda d: str(d.get("pool_id", "")))
    data = {"job": dict(job), "pools": pools_norm}
    return sha256_hex(domain_sep_bytes("improvement_bounty_job", version=1) + canonical_json_bytes(data))


def _safe_name(s: str) -> str:
    # For filenames only; do not use for hashes.
    out = []
    for ch in str(s):
        if ch.isalnum() or ch in ("-", "_", "."):
            out.append(ch)
        else:
            out.append("_")
    return "".join(out)[:180] or "job"


@dataclass(frozen=True)
class RunResult:
    status: str  # ok|skipped|compute_error|verify_error
    ok: bool
    error: str
    job_id: str
    improves: bool
    baseline_out: int
    proposal_out: int
    improvement: int
    approx_backend: str
    evaluated: Optional[int]


def _iter_jobs_jsonl(path: Path) -> Iterable[Tuple[int, Mapping[str, Any]]]:
    text = path.read_text(encoding="utf-8")
    for i, raw in enumerate(text.splitlines()):
        raw = raw.strip()
        if not raw:
            continue
        obj = json.loads(raw)
        yield i, _require_mapping(obj, name=f"jobs[{i}]")


def _resolve_pools(job: Mapping[str, Any], pools_default: Optional[Sequence[Mapping[str, Any]]]) -> List[Mapping[str, Any]]:
    pools = job.get("pools")
    if pools is None:
        if pools_default is None:
            raise TypeError("job missing pools and no --pools provided")
        return [dict(p) for p in pools_default]
    pools_list = _require_list(pools, name="job.pools")
    return [_require_mapping(p, name="pool") for p in pools_list]


def _run_one(
    *,
    job: Mapping[str, Any],
    pools_default: Optional[Sequence[Mapping[str, Any]]],
    prefer_gpu: bool,
    topk: int,
    adaptive_prune: bool,
    topk_max: int,
    allow_no_improvement: bool,
) -> Tuple[RunResult, Optional[Mapping[str, Any]]]:
    # Validate minimal job fields; keep any extra keys (job_id, tags) ignored.
    asset_in = _require_str(job.get("asset_in"), name="job.asset_in")
    asset_out = _require_str(job.get("asset_out"), name="job.asset_out")
    amount_in = _require_int(job.get("amount_in"), name="job.amount_in")
    if amount_in <= 0:
        raise ValueError("job.amount_in must be positive")
    if asset_in == asset_out:
        raise ValueError("job.asset_in must differ from job.asset_out")

    pools = _resolve_pools(job, pools_default=pools_default)
    job_core = {"asset_in": asset_in, "asset_out": asset_out, "amount_in": int(amount_in), "max_hops": 2}
    job_id = str(job.get("job_id") or _job_digest(job_core, pools))

    # The witness compute function expects pools embedded.
    witness_job = dict(job_core)
    witness_job["pools"] = [dict(p) for p in pools]

    try:
        witness = compute_route_improvement_witness_v1(
            witness_job,
            prefer_gpu=bool(prefer_gpu),
            topk=int(topk),
            adaptive_prune=bool(adaptive_prune),
            topk_max=int(topk_max),
            allow_no_improvement=bool(allow_no_improvement),
        )
    except Exception as exc:
        msg = f"{type(exc).__name__}: {exc}"
        # Treat invalid/no-solution jobs as "skipped" rather than hard failure.
        # This is important when doing BVA sweeps that intentionally include rejects.
        skipped = False
        if isinstance(exc, (TypeError, ValueError)):
            needles = (
                "amount_in must be positive",
                "asset_in must differ",
                "job missing pools",
                "pools must be a list",
                "no valid direct CPMM pool found",
            )
            if any(n in str(exc) for n in needles):
                skipped = True
        rr = RunResult(
            status="skipped" if skipped else "compute_error",
            ok=False,
            error=("skipped: " if skipped else "compute_error: ") + msg,
            job_id=job_id,
            improves=False,
            baseline_out=0,
            proposal_out=0,
            improvement=0,
            approx_backend="",
            evaluated=None,
        )
        return rr, None

    ok, err = verify_route_improvement_witness(_require_mapping(witness, name="witness"))
    if not ok:
        rr = RunResult(
            status="verify_error",
            ok=False,
            error=f"verify_error: {err or 'unknown'}",
            job_id=job_id,
            improves=bool(witness.get("improves", False)),
            baseline_out=int(_require_mapping(witness.get("baseline"), name="baseline").get("amount_out", 0)),
            proposal_out=int(_require_mapping(witness.get("proposal"), name="proposal").get("amount_out", 0)),
            improvement=0,
            approx_backend=str(_require_mapping(witness.get("meta", {}), name="meta").get("approx_backend", "")),
            evaluated=None,
        )
        return rr, witness

    base = _require_mapping(witness.get("baseline"), name="baseline")
    prop = _require_mapping(witness.get("proposal"), name="proposal")
    base_out = _require_int(base.get("amount_out"), name="baseline.amount_out")
    prop_out = _require_int(prop.get("amount_out"), name="proposal.amount_out")
    improves = bool(witness.get("improves", False))
    improvement = int(prop_out) - int(base_out) if improves else 0

    meta = _require_mapping(witness.get("meta", {}), name="meta")
    approx_backend = str(meta.get("approx_backend", ""))
    evaluated = meta.get("evaluated")
    evaluated_i: Optional[int] = None
    if evaluated is not None:
        try:
            evaluated_i = _require_int(evaluated, name="meta.evaluated")
        except Exception:
            evaluated_i = None

    rr = RunResult(
        status="ok",
        ok=True,
        error="",
        job_id=job_id,
        improves=bool(improves),
        baseline_out=int(base_out),
        proposal_out=int(prop_out),
        improvement=int(improvement),
        approx_backend=str(approx_backend),
        evaluated=evaluated_i,
    )
    return rr, witness


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs-jsonl", required=True, help="JSONL of jobs: {asset_in,asset_out,amount_in[,job_id][,pools]}")
    ap.add_argument("--pools", default="", help="Optional pools JSON: a list of pools used for all jobs (unless job overrides).")
    ap.add_argument("--out-dir", required=True, help="Directory to write outputs (results.jsonl, summary.json, witnesses/...).")
    ap.add_argument("--prefer-gpu", action="store_true", help="Prefer GPU backend when available (Torch/CuPy).")
    ap.add_argument("--topk", type=int, default=256, help="Exact-evaluate only the top-K approximate 2-hop candidates.")
    ap.add_argument("--adaptive-prune", action="store_true", help="Use UB-pruning path (see route_2hop_search_cpmm.py).")
    ap.add_argument("--topk-max", type=int, default=0, help="Max candidates to consider under --adaptive-prune (0 => use --topk).")
    ap.add_argument("--allow-no-improvement", action="store_true", help="Keep jobs even if they have no improvement (proposal==baseline).")
    ap.add_argument(
        "--store-witnesses",
        choices=["improvements_only", "all", "none"],
        default="improvements_only",
        help="Which witnesses to store on disk (to manage space).",
    )
    ap.add_argument("--max-jobs", type=int, default=0, help="Process at most N jobs (0 => all).")
    ap.add_argument("--fail-fast", action="store_true", help="Stop on first compute/verify failure.")
    ap.add_argument(
        "--strict",
        action="store_true",
        help="Exit non-zero if any compute/verify errors occur (skips are tolerated).",
    )
    args = ap.parse_args()

    jobs_path = Path(args.jobs_jsonl)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    witness_dir = out_dir / "witnesses"
    witness_dir.mkdir(parents=True, exist_ok=True)

    pools_default: Optional[List[Mapping[str, Any]]] = None
    if str(args.pools).strip():
        pools_obj = _load_json(Path(args.pools))
        pools_list = _require_list(pools_obj, name="pools")
        pools_default = [_require_mapping(p, name="pool") for p in pools_list]

    results_path = out_dir / "results.jsonl"
    summary_path = out_dir / "summary.json"

    n_total = 0
    n_ok = 0
    n_skipped = 0
    n_verify_fail = 0
    n_compute_fail = 0
    n_improves = 0
    improvement_sum = 0
    best: Optional[RunResult] = None
    backend_counts: Dict[str, int] = {}

    with results_path.open("w", encoding="utf-8") as f:
        for i, job in _iter_jobs_jsonl(jobs_path):
            if int(args.max_jobs) > 0 and n_total >= int(args.max_jobs):
                break
            n_total += 1

            try:
                rr, witness = _run_one(
                    job=job,
                    pools_default=pools_default,
                    prefer_gpu=bool(args.prefer_gpu),
                    topk=int(args.topk),
                    adaptive_prune=bool(args.adaptive_prune),
                    topk_max=int(args.topk_max),
                    allow_no_improvement=bool(args.allow_no_improvement),
                )
            except Exception as exc:
                rr = RunResult(
                    status="compute_error",
                    ok=False,
                    error=f"runner_error: {type(exc).__name__}: {exc}",
                    job_id=str(job.get("job_id") or f"line_{i}"),
                    improves=False,
                    baseline_out=0,
                    proposal_out=0,
                    improvement=0,
                    approx_backend="",
                    evaluated=None,
                )
                witness = None

            if rr.ok:
                n_ok += 1
                backend_counts[rr.approx_backend] = int(backend_counts.get(rr.approx_backend, 0)) + 1
                if rr.improves:
                    n_improves += 1
                    improvement_sum += int(rr.improvement)
                    if best is None or rr.improvement > best.improvement:
                        best = rr
            else:
                if rr.status == "skipped":
                    n_skipped += 1
                elif rr.status == "verify_error":
                    n_verify_fail += 1
                else:
                    n_compute_fail += 1
                if bool(args.fail_fast):
                    f.write(_dump_json_line({"job_id": rr.job_id, "ok": False, "error": rr.error}))
                    break

            rec: Dict[str, Any] = {
                "job_id": rr.job_id,
                "status": rr.status,
                "ok": bool(rr.ok),
                "error": rr.error,
                "improves": bool(rr.improves),
                "baseline_out": int(rr.baseline_out),
                "proposal_out": int(rr.proposal_out),
                "improvement": int(rr.improvement),
                "approx_backend": rr.approx_backend,
                "evaluated": rr.evaluated,
            }
            f.write(_dump_json_line(rec))

            store_mode = str(args.store_witnesses)
            if witness is not None and store_mode != "none":
                if store_mode == "all" or (store_mode == "improvements_only" and rr.ok and rr.improves):
                    # Stable filename: job_id + digest to avoid collisions.
                    digest = ""
                    try:
                        digest = str(_job_digest(_require_mapping(witness.get("job"), name="witness.job"), _require_list(witness.get("pools"), name="witness.pools")))
                    except Exception:
                        digest = ""
                    fn = _safe_name(rr.job_id) + (("_" + digest[2:18]) if digest.startswith("0x") else "") + ".json"
                    (witness_dir / fn).write_text(json.dumps(witness, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    summary: Dict[str, Any] = {
        "jobs_total": int(n_total),
        "jobs_ok": int(n_ok),
        "jobs_skipped": int(n_skipped),
        "jobs_compute_fail": int(n_compute_fail),
        "jobs_verify_fail": int(n_verify_fail),
        "jobs_improve": int(n_improves),
        "improvement_sum": int(improvement_sum),
        "improvement_avg": (float(improvement_sum) / float(n_improves)) if n_improves > 0 else 0.0,
        "approx_backend_counts": dict(sorted(backend_counts.items(), key=lambda kv: kv[0])),
        "best_job_id": best.job_id if best is not None else None,
        "best_improvement": best.improvement if best is not None else None,
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    sys.stdout.write(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    if bool(args.strict):
        return 0 if (n_compute_fail == 0 and n_verify_fail == 0) else 2
    return 0 if (n_verify_fail == 0) else 2


if __name__ == "__main__":
    raise SystemExit(main())
