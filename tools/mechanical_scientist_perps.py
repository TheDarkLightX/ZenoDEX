#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import copy
import hashlib
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import yaml


_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
if sys.version_info < (3, 10):
    raise SystemExit("tools/mechanical_scientist_perps.py requires Python 3.10+")


@dataclass(frozen=True)
class Hypothesis:
    hypothesis_id: str
    source: str
    strategy_source: str
    tactic_names: tuple[str, ...]
    max_depth: int
    max_expanded: int
    mdl_portal: bool


@dataclass(frozen=True)
class EvalRecord:
    hypothesis_id: str
    split: str
    seed: int
    bundle_dir: str
    run_returncode: int
    doctor_returncode: int
    strict_ok: bool
    outcome: str
    expanded: int | None
    visited: int | None
    frontier_remaining: int | None
    duration_seconds: float


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _default_config_path() -> Path:
    return _repo_root() / "docs" / "derivatives" / "mechanical_scientist_perps_config.yaml"


def _utc_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")


def _json_dumps(obj: object) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def _append_jsonl(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(_json_dumps(obj) + "\n")


def _load_yaml(path: Path) -> dict[str, Any]:
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"config must be a mapping: {path}")
    return obj


def _read_json(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"expected JSON object: {path}")
    return obj


def _read_int_list(cfg: dict[str, Any], key: str) -> list[int]:
    raw = cfg.get(key)
    if not isinstance(raw, list) or not raw:
        raise ValueError(f"{key} must be a non-empty list")
    out: list[int] = []
    for i, v in enumerate(raw):
        if not isinstance(v, int) or v <= 0:
            raise ValueError(f"{key}[{i}] must be a positive integer")
        out.append(int(v))
    return out


def _read_bool_list(cfg: dict[str, Any], key: str) -> list[bool]:
    raw = cfg.get(key)
    if not isinstance(raw, list) or not raw:
        raise ValueError(f"{key} must be a non-empty list")
    out: list[bool] = []
    for i, v in enumerate(raw):
        if not isinstance(v, bool):
            raise ValueError(f"{key}[{i}] must be a bool")
        out.append(bool(v))
    return out


def _read_tactic_packs(search: dict[str, Any]) -> dict[str, list[str]]:
    raw = search.get("tactic_packs")
    if not isinstance(raw, dict) or not raw:
        raise ValueError("search.tactic_packs must be a non-empty mapping")
    out: dict[str, list[str]] = {}
    for pack_name, pack_vals in raw.items():
        if not isinstance(pack_name, str) or not pack_name:
            raise ValueError("search.tactic_packs keys must be non-empty strings")
        if not isinstance(pack_vals, list) or not pack_vals:
            raise ValueError(f"search.tactic_packs.{pack_name} must be a non-empty list")
        steps: list[str] = []
        for i, step in enumerate(pack_vals):
            if not isinstance(step, str) or not step.strip():
                raise ValueError(f"search.tactic_packs.{pack_name}[{i}] must be a non-empty string")
            steps.append(step.strip())
        out[pack_name] = steps
    return out


def _read_strategy_templates(search: dict[str, Any]) -> list[tuple[str, str]]:
    raw = search.get("strategy_templates")
    if not isinstance(raw, list) or not raw:
        raise ValueError("search.strategy_templates must be a non-empty list")
    out: list[tuple[str, str]] = []
    for i, item in enumerate(raw):
        if not isinstance(item, dict):
            raise ValueError(f"search.strategy_templates[{i}] must be an object")
        name = item.get("name")
        src = item.get("source")
        if not isinstance(name, str) or not name.strip():
            raise ValueError(f"search.strategy_templates[{i}].name must be a non-empty string")
        if not isinstance(src, str) or not src.strip():
            raise ValueError(f"search.strategy_templates[{i}].source must be a non-empty string")
        if "{TACTICS}" not in src:
            raise ValueError(f"search.strategy_templates[{i}].source must include {{TACTICS}}")
        out.append((name.strip(), src.strip()))
    return out


def _initial_sigma0() -> dict[str, object]:
    from dataclasses import asdict

    from generated.perp_python import perp_epoch_isolated_v2_ref as ref
    from src.core.perp_epoch import perp_epoch_isolated_v2_native_initial_state

    return {
        "goal": "Find a witness where perp_v2 native diverges from generated ref (and validate vs YAML interpreter).",
        "representation": _json_dumps(
            {
                "steps": [],
                "native_state": dict(perp_epoch_isolated_v2_native_initial_state()),
                "ref_state": dict(asdict(ref.init_state())),
                "diverged": False,
                "divergence": None,
            }
        ),
        "givens": [],
        "constraints": [],
        "examples": [],
        "obligations": [],
    }


def _build_tactics_json(step_tactics: tuple[str, ...]) -> list[dict[str, object]]:
    tactics: list[dict[str, object]] = [
        {"name": "TrySolve", "source": "TrySolve", "tag": "≅", "cert_type": "primitive"}
    ]
    for name in step_tactics:
        tactics.append({"name": name, "source": name, "tag": "↦", "cert_type": "primitive"})
    return tactics


def _hypothesis_id(
    *,
    strategy_source: str,
    tactic_names: tuple[str, ...],
    max_depth: int,
    max_expanded: int,
    mdl_portal: bool,
) -> str:
    payload = {
        "strategy_source": strategy_source,
        "tactic_names": list(tactic_names),
        "max_depth": int(max_depth),
        "max_expanded": int(max_expanded),
        "mdl_portal": bool(mdl_portal),
    }
    h = hashlib.sha256(_json_dumps(payload).encode("utf-8")).hexdigest()
    return f"hyp:{h[:16]}"


def _candidate_priority(h: Hypothesis) -> tuple[int, int, int, str]:
    archive_bonus = 1 if h.source.startswith("archive:") else 0
    # Lower depth/expanded is preferred for early rounds to improve throughput.
    return (archive_bonus, -int(h.max_expanded), -int(h.max_depth), h.hypothesis_id)


def _load_archive(path: Path) -> list[Hypothesis]:
    if not path.exists():
        return []
    out: list[Hypothesis] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        obj = json.loads(line)
        if not isinstance(obj, dict):
            continue
        try:
            hid = str(obj["hypothesis_id"])
            strategy_source = str(obj["strategy_source"])
            tactic_names_raw = obj["tactic_names"]
            if not isinstance(tactic_names_raw, list) or not tactic_names_raw:
                continue
            tactic_names = tuple(str(x) for x in tactic_names_raw)
            max_depth = int(obj["max_depth"])
            max_expanded = int(obj["max_expanded"])
            mdl_portal = bool(obj["mdl_portal"])
        except (KeyError, TypeError, ValueError):
            continue
        out.append(
            Hypothesis(
                hypothesis_id=hid,
                source="archive:promoted",
                strategy_source=strategy_source,
                tactic_names=tactic_names,
                max_depth=max_depth,
                max_expanded=max_expanded,
                mdl_portal=mdl_portal,
            )
        )
    return out


def _generate_hypotheses(config: dict[str, Any], archived: list[Hypothesis]) -> list[Hypothesis]:
    search = config["search"]
    depth_grid = _read_int_list(search, "max_depth_grid")
    expanded_grid = _read_int_list(search, "max_expanded_grid")
    mdl_opts = _read_bool_list(search, "mdl_portal_options")
    templates = _read_strategy_templates(search)
    tactic_packs = _read_tactic_packs(search)

    out: list[Hypothesis] = []
    by_id: dict[str, Hypothesis] = {}
    for h in archived:
        if h.hypothesis_id not in by_id:
            by_id[h.hypothesis_id] = h

    for pack_name, pack in tactic_packs.items():
        tactic_expr = " + ".join(pack)
        step_tactics = tuple(pack)
        for template_name, template_src in templates:
            strategy_source = template_src.replace("{TACTICS}", tactic_expr).replace("{TRY}", "TrySolve")
            for max_depth in depth_grid:
                for max_expanded in expanded_grid:
                    for mdl_portal in mdl_opts:
                        hid = _hypothesis_id(
                            strategy_source=strategy_source,
                            tactic_names=step_tactics,
                            max_depth=max_depth,
                            max_expanded=max_expanded,
                            mdl_portal=mdl_portal,
                        )
                        if hid in by_id:
                            continue
                        by_id[hid] = Hypothesis(
                            hypothesis_id=hid,
                            source=f"grid:{template_name}:{pack_name}",
                            strategy_source=strategy_source,
                            tactic_names=step_tactics,
                            max_depth=max_depth,
                            max_expanded=max_expanded,
                            mdl_portal=mdl_portal,
                        )
    out = list(by_id.values())
    out.sort(key=_candidate_priority, reverse=True)
    return out


def _campaign_paths(root: Path, out_dir: Path | None, cfg: dict[str, Any]) -> tuple[Path, Path]:
    runtime_cfg = cfg["runtime"]
    output_root = root / str(runtime_cfg["output_root"])
    campaign_dir = out_dir if out_dir is not None else output_root / _utc_stamp()
    archive_cfg = cfg["archive"]
    archive_path = root / str(archive_cfg["global_promoted_jsonl"])
    return campaign_dir, archive_path


def _prepare_env(root: Path) -> dict[str, str]:
    env = dict(os.environ)
    env["PYTHONPATH"] = str(root / "external" / "Morph") + os.pathsep + str(root) + os.pathsep + env.get("PYTHONPATH", "")
    env.setdefault("PYTHONPYCACHEPREFIX", str(Path("/tmp") / "pycache"))
    return env


def _run_bundle(
    *,
    root: Path,
    python: str,
    env: dict[str, str],
    domain_import: str,
    runtime_import: str,
    sigma0: dict[str, object],
    hypothesis: Hypothesis,
    bundle_dir: Path,
    seed: int,
    run_timeout_seconds: float | None,
    hard_timeout_seconds: float | None,
) -> EvalRecord:
    bundle_dir.mkdir(parents=True, exist_ok=True)
    sigma0_path = bundle_dir / "sigma0.json"
    tactics_path = bundle_dir / "tactics.json"
    telemetry_path = bundle_dir / "telemetry.json"
    run_stdout_path = bundle_dir / "run.stdout.log"
    run_stderr_path = bundle_dir / "run.stderr.log"
    doc_stdout_path = bundle_dir / "doctor.stdout.log"
    doc_stderr_path = bundle_dir / "doctor.stderr.log"

    _write_json(sigma0_path, sigma0)
    _write_json(tactics_path, _build_tactics_json(hypothesis.tactic_names))

    cmd = [
        python,
        "-m",
        "morph",
        "run",
        "kernel",
        "--out",
        str(bundle_dir),
        "--sigma0-json",
        str(sigma0_path),
        "--domain-import",
        str(domain_import),
        "--runtime-import",
        str(runtime_import),
        "--tactics-json",
        str(tactics_path),
        "--strategy",
        str(hypothesis.strategy_source),
        "--seed",
        str(int(seed)),
        "--max-depth",
        str(int(hypothesis.max_depth)),
        "--max-expanded",
        str(int(hypothesis.max_expanded)),
        "--strict",
        "--telemetry-json",
        str(telemetry_path),
    ]
    if hypothesis.mdl_portal:
        cmd.append("--mdl-portal")
    if run_timeout_seconds is not None:
        cmd.extend(["--timeout", str(float(run_timeout_seconds))])

    run_returncode: int
    timed_out = False
    start_ts = time.monotonic()
    with run_stdout_path.open("w", encoding="utf-8") as out_fh, run_stderr_path.open("w", encoding="utf-8") as err_fh:
        try:
            run_proc = subprocess.run(
                cmd,
                cwd=str(root),
                env=env,
                stdout=out_fh,
                stderr=err_fh,
                timeout=(float(hard_timeout_seconds) if hard_timeout_seconds is not None else None),
            )
            run_returncode = int(run_proc.returncode)
        except subprocess.TimeoutExpired:
            timed_out = True
            run_returncode = 124
            err_fh.write("mechanical_scientist_perps: hard timeout expired; terminated morph run\n")
            err_fh.flush()
    elapsed = float(max(0.0, time.monotonic() - start_ts))

    doctor_returncode: int
    if run_returncode == 0:
        doc_cmd = [python, "-m", "morph", "doctor", "--strict", str(bundle_dir)]
        with doc_stdout_path.open("w", encoding="utf-8") as out_fh, doc_stderr_path.open("w", encoding="utf-8") as err_fh:
            doc_proc = subprocess.run(doc_cmd, cwd=str(root), env=env, stdout=out_fh, stderr=err_fh)
        doctor_returncode = int(doc_proc.returncode)
    else:
        doc_stdout_path.write_text("doctor skipped: morph run did not exit cleanly\n", encoding="utf-8")
        doc_stderr_path.write_text("", encoding="utf-8")
        doctor_returncode = 125

    outcome = "TIMEOUT" if timed_out else "ERROR"
    packet_path = bundle_dir / "packet.json"
    if packet_path.exists():
        try:
            packet_obj = _read_json(packet_path)
            raw_outcome = packet_obj.get("outcome")
            if isinstance(raw_outcome, str) and raw_outcome:
                outcome = raw_outcome
        except (OSError, ValueError, json.JSONDecodeError):
            outcome = "TIMEOUT" if timed_out else "ERROR"

    expanded: int | None = None
    visited: int | None = None
    frontier_remaining: int | None = None
    if telemetry_path.exists():
        try:
            telemetry_obj = _read_json(telemetry_path)
            stats = telemetry_obj.get("stats")
            if isinstance(stats, dict):
                if isinstance(stats.get("expanded"), int):
                    expanded = int(stats["expanded"])
                if isinstance(stats.get("visited"), int):
                    visited = int(stats["visited"])
                if isinstance(stats.get("frontier_remaining"), int):
                    frontier_remaining = int(stats["frontier_remaining"])
        except (OSError, ValueError, json.JSONDecodeError):
            pass

    strict_ok = run_returncode == 0 and doctor_returncode == 0
    return EvalRecord(
        hypothesis_id=hypothesis.hypothesis_id,
        split="",
        seed=int(seed),
        bundle_dir=str(bundle_dir),
        run_returncode=run_returncode,
        doctor_returncode=doctor_returncode,
        strict_ok=bool(strict_ok),
        outcome=str(outcome),
        expanded=expanded,
        visited=visited,
        frontier_remaining=frontier_remaining,
        duration_seconds=elapsed,
    )


def _aggregate_records(
    *,
    hypothesis: Hypothesis,
    records: list[EvalRecord],
    success_outcomes: set[str],
) -> dict[str, Any]:
    train = [r for r in records if r.split == "train"]
    holdout = [r for r in records if r.split == "holdout"]
    train_successes = sum(1 for r in train if r.outcome in success_outcomes)
    holdout_successes = sum(1 for r in holdout if r.outcome in success_outcomes)
    strict_count = sum(1 for r in records if r.strict_ok)
    strict_rate = float(strict_count) / float(max(1, len(records)))
    expanded_vals = [int(r.expanded) for r in records if r.expanded is not None]
    avg_expanded = (sum(expanded_vals) / float(len(expanded_vals))) if expanded_vals else None
    visited_vals = [int(r.visited) for r in records if r.visited is not None]
    avg_visited = (sum(visited_vals) / float(len(visited_vals))) if visited_vals else None
    frontier_vals = [int(r.frontier_remaining) for r in records if r.frontier_remaining is not None]
    avg_frontier_remaining = (sum(frontier_vals) / float(len(frontier_vals))) if frontier_vals else None
    frontier_exhaustion_rate = (
        float(sum(1 for v in frontier_vals if int(v) == 0)) / float(len(frontier_vals)) if frontier_vals else None
    )

    return {
        "hypothesis_id": hypothesis.hypothesis_id,
        "source": hypothesis.source,
        "strategy_source": hypothesis.strategy_source,
        "tactic_names": list(hypothesis.tactic_names),
        "max_depth": int(hypothesis.max_depth),
        "max_expanded": int(hypothesis.max_expanded),
        "mdl_portal": bool(hypothesis.mdl_portal),
        "train_total": len(train),
        "holdout_total": len(holdout),
        "train_successes": int(train_successes),
        "holdout_successes": int(holdout_successes),
        "strict_count": int(strict_count),
        "strict_rate": float(strict_rate),
        "avg_expanded": avg_expanded,
        "avg_visited": avg_visited,
        "avg_frontier_remaining": avg_frontier_remaining,
        "frontier_exhaustion_rate": frontier_exhaustion_rate,
    }


def _select_promotions(
    *,
    aggregates: list[dict[str, Any]],
    promotion_cfg: dict[str, Any],
) -> list[dict[str, Any]]:
    success_outcomes_raw = promotion_cfg.get("success_outcomes")
    if not isinstance(success_outcomes_raw, list) or not success_outcomes_raw:
        raise ValueError("promotion.success_outcomes must be a non-empty list")
    success_outcomes = {str(x) for x in success_outcomes_raw}

    require_all_strict = bool(promotion_cfg.get("require_all_strict", True))
    min_train_successes = int(promotion_cfg.get("min_train_successes", 1))
    min_holdout_successes = int(promotion_cfg.get("min_holdout_successes", 1))
    max_promoted = int(promotion_cfg.get("max_promoted_per_round", 1))
    allow_frontier = bool(promotion_cfg.get("allow_frontier_promotion_without_success", False))
    allow_coverage = bool(promotion_cfg.get("allow_coverage_frontier_promotion", False))
    require_holdout_for_coverage = bool(promotion_cfg.get("require_holdout_for_coverage", True))
    prefer_non_archive = bool(promotion_cfg.get("coverage_prefer_non_archive", True))
    coverage_min_avg_visited = int(promotion_cfg.get("coverage_min_avg_visited", 0))
    coverage_min_avg_expanded = int(promotion_cfg.get("coverage_min_avg_expanded", 0))
    if max_promoted < 1:
        raise ValueError("promotion.max_promoted_per_round must be >= 1")
    if coverage_min_avg_visited < 0:
        raise ValueError("promotion.coverage_min_avg_visited must be >= 0")
    if coverage_min_avg_expanded < 0:
        raise ValueError("promotion.coverage_min_avg_expanded must be >= 0")

    promoted: list[dict[str, Any]] = []
    qualifying: list[dict[str, Any]] = []
    for row in aggregates:
        if require_all_strict and float(row["strict_rate"]) < 1.0:
            continue
        if int(row["train_successes"]) < min_train_successes:
            continue
        if int(row["holdout_successes"]) < min_holdout_successes:
            continue
        qualifying.append(row)

    qualifying.sort(
        key=lambda r: (
            int(r["holdout_successes"]),
            int(r["train_successes"]),
            -(float(r["avg_expanded"]) if r["avg_expanded"] is not None else 1e18),
        ),
        reverse=True,
    )
    for row in qualifying[:max_promoted]:
        row2 = dict(row)
        row2["promotion_reason"] = "meets_success_threshold"
        promoted.append(row2)

    if promoted:
        return promoted

    if allow_coverage:
        coverage_rows = [r for r in aggregates if float(r["strict_rate"]) >= 1.0]
        coverage_rows = [
            r
            for r in coverage_rows
            if (not require_holdout_for_coverage or int(r.get("holdout_total", 0)) >= 1)
            if float(r["avg_visited"] if r["avg_visited"] is not None else 0.0) >= float(coverage_min_avg_visited)
            and float(r["avg_expanded"] if r["avg_expanded"] is not None else 0.0) >= float(coverage_min_avg_expanded)
        ]
        coverage_rows.sort(
            key=lambda r: (
                1 if (prefer_non_archive and not str(r["source"]).startswith("archive:")) else 0,
                float(r["avg_visited"] if r["avg_visited"] is not None else -1.0),
                float(r["avg_expanded"] if r["avg_expanded"] is not None else -1.0),
                -float(r["avg_frontier_remaining"] if r["avg_frontier_remaining"] is not None else 1e18),
            ),
            reverse=True,
        )
        for row in coverage_rows[:max_promoted]:
            row2 = dict(row)
            row2["promotion_reason"] = "coverage_frontier"
            promoted.append(row2)
        if promoted:
            return promoted

    if allow_frontier:
        strict_rows = [r for r in aggregates if float(r["strict_rate"]) >= 1.0]
        strict_rows.sort(
            key=lambda r: (
                -float(r["strict_rate"]),
                -(float(r["holdout_successes"]) + float(r["train_successes"])),
                float(r["avg_expanded"]) if r["avg_expanded"] is not None else 1e18,
            )
        )
        for row in strict_rows[:max_promoted]:
            row2 = dict(row)
            row2["promotion_reason"] = "strict_frontier_fallback"
            promoted.append(row2)
    return promoted


def _quick_overrides(cfg: dict[str, Any]) -> dict[str, Any]:
    out = copy.deepcopy(cfg)
    out["campaign"]["rounds"] = 1
    out["campaign"]["candidates_per_round"] = 2
    out["campaign"]["train_seeds_per_hypothesis"] = 1
    out["campaign"]["holdout_seeds_per_hypothesis"] = 1
    out["campaign"]["stop_after_rounds_without_promotion"] = 1
    out["campaign"]["min_new_candidates_per_round"] = 1
    out["campaign"]["run_timeout_seconds"] = 45
    out["campaign"]["hard_timeout_seconds"] = 60
    out["campaign"]["max_parallel_bundles"] = max(4, int(out["campaign"].get("max_parallel_bundles", 2)))
    out["campaign"]["holdout_top_k"] = int(out["campaign"]["candidates_per_round"])
    out["promotion"]["allow_coverage_frontier_promotion"] = True
    out["promotion"]["coverage_min_avg_visited"] = 10
    out["promotion"]["coverage_prefer_non_archive"] = True
    out["search"]["max_depth_grid"] = [min(_read_int_list(out["search"], "max_depth_grid"))]
    out["search"]["max_expanded_grid"] = [min(_read_int_list(out["search"], "max_expanded_grid"))]
    templates = _read_strategy_templates(out["search"])
    out["search"]["strategy_templates"] = [{"name": templates[0][0], "source": templates[0][1]}]
    return out


def _select_round_candidates(
    *,
    hypotheses: list[Hypothesis],
    candidates_per_round: int,
    min_new_candidates_per_round: int,
    excluded_ids: set[str] | None = None,
) -> list[Hypothesis]:
    if candidates_per_round <= 0:
        return []
    want_new = max(0, min(min_new_candidates_per_round, candidates_per_round))
    excluded = excluded_ids or set()
    selected: list[Hypothesis] = []
    selected_ids: set[str] = set()

    unseen = [h for h in hypotheses if h.hypothesis_id not in excluded]
    primary = unseen if unseen else hypotheses

    # First: reserve slots for exploration (non-archived), preferring unseen candidates.
    for h in primary:
        if len(selected) >= want_new:
            break
        if h.source.startswith("archive:"):
            continue
        if h.hypothesis_id in selected_ids:
            continue
        selected.append(h)
        selected_ids.add(h.hypothesis_id)

    # Then: fill remainder from unseen pool.
    for h in primary:
        if len(selected) >= candidates_per_round:
            break
        if h.hypothesis_id in selected_ids:
            continue
        selected.append(h)
        selected_ids.add(h.hypothesis_id)

    # Finally: if unseen is exhausted, allow replay from already-seen hypotheses.
    if len(selected) < candidates_per_round and unseen:
        for h in hypotheses:
            if len(selected) >= candidates_per_round:
                break
            if h.hypothesis_id in selected_ids:
                continue
            selected.append(h)
            selected_ids.add(h.hypothesis_id)

    return selected


def run_campaign(*, config_path: Path, out_dir: Path | None, quick: bool) -> int:
    root = _repo_root()
    cfg = _load_yaml(config_path)
    if cfg.get("schema") != "zenodex/mechanical-scientist-perps/v1":
        raise ValueError("unsupported config schema")
    if quick:
        cfg = _quick_overrides(cfg)

    runtime_cfg = cfg.get("runtime")
    campaign_cfg = cfg.get("campaign")
    promotion_cfg = cfg.get("promotion")
    if not isinstance(runtime_cfg, dict) or not isinstance(campaign_cfg, dict) or not isinstance(promotion_cfg, dict):
        raise ValueError("config must include runtime/campaign/promotion mappings")

    python = str(runtime_cfg.get("python", "python3.11"))
    domain_import = str(runtime_cfg["domain_import"])
    runtime_import = str(runtime_cfg["runtime_import"])

    campaign_dir, archive_path = _campaign_paths(root, out_dir, cfg)
    campaign_dir.mkdir(parents=True, exist_ok=True)
    env = _prepare_env(root)
    sigma0 = _initial_sigma0()

    archived = _load_archive(archive_path)
    all_hypotheses = _generate_hypotheses(cfg, archived=archived)
    candidates_per_round = int(campaign_cfg.get("candidates_per_round", 6))
    if candidates_per_round < 1:
        raise ValueError("campaign.candidates_per_round must be >= 1")
    min_new_candidates_per_round = int(campaign_cfg.get("min_new_candidates_per_round", 1))
    if min_new_candidates_per_round < 0:
        raise ValueError("campaign.min_new_candidates_per_round must be >= 0")
    rounds = int(campaign_cfg.get("rounds", 1))
    if rounds < 1:
        raise ValueError("campaign.rounds must be >= 1")

    seed_start = int(campaign_cfg.get("seed_start", 0))
    seed_step = int(campaign_cfg.get("seed_step", 1))
    holdout_seed_offset = int(campaign_cfg.get("holdout_seed_offset", 1_000_000))
    round_seed_stride = int(campaign_cfg.get("round_seed_stride", 100))
    train_count = int(campaign_cfg.get("train_seeds_per_hypothesis", 1))
    holdout_count = int(campaign_cfg.get("holdout_seeds_per_hypothesis", 1))
    if train_count < 1 or holdout_count < 1:
        raise ValueError("campaign train/holdout seed counts must be >= 1")
    holdout_top_k_raw = campaign_cfg.get("holdout_top_k")
    holdout_top_k: int | None
    if holdout_top_k_raw is None:
        holdout_top_k = None
    else:
        holdout_top_k = int(holdout_top_k_raw)
        if holdout_top_k < 1:
            raise ValueError("campaign.holdout_top_k must be >= 1 when provided")
    run_timeout_seconds_raw = campaign_cfg.get("run_timeout_seconds")
    run_timeout_seconds: float | None
    if run_timeout_seconds_raw is None:
        run_timeout_seconds = None
    else:
        run_timeout_seconds = float(run_timeout_seconds_raw)
        if run_timeout_seconds <= 0.0:
            raise ValueError("campaign.run_timeout_seconds must be > 0 when provided")
    hard_timeout_seconds_raw = campaign_cfg.get("hard_timeout_seconds")
    hard_timeout_seconds: float | None
    if hard_timeout_seconds_raw is None:
        hard_timeout_seconds = (float(run_timeout_seconds) + 15.0) if run_timeout_seconds is not None else None
    else:
        hard_timeout_seconds = float(hard_timeout_seconds_raw)
        if hard_timeout_seconds <= 0.0:
            raise ValueError("campaign.hard_timeout_seconds must be > 0 when provided")
    max_parallel_bundles = int(campaign_cfg.get("max_parallel_bundles", 1))
    if max_parallel_bundles < 1:
        raise ValueError("campaign.max_parallel_bundles must be >= 1")

    stop_after_no_promo = int(campaign_cfg.get("stop_after_rounds_without_promotion", 2))
    if stop_after_no_promo < 1:
        raise ValueError("campaign.stop_after_rounds_without_promotion must be >= 1")

    success_outcomes_raw = promotion_cfg.get("success_outcomes", ["SOLVED"])
    if not isinstance(success_outcomes_raw, list) or not success_outcomes_raw:
        raise ValueError("promotion.success_outcomes must be non-empty")
    success_outcomes = {str(x) for x in success_outcomes_raw}

    _write_json(campaign_dir / "config.resolved.json", cfg)
    summary_rows: list[dict[str, Any]] = []
    all_evals: list[EvalRecord] = []
    evaluated_hypothesis_ids: set[str] = set()
    rounds_without_promotion = 0
    promotions_total = 0
    campaign_start_ts = time.monotonic()

    for round_index in range(rounds):
        evaluated_before_round = set(evaluated_hypothesis_ids)
        selected = _select_round_candidates(
            hypotheses=all_hypotheses,
            candidates_per_round=candidates_per_round,
            min_new_candidates_per_round=min_new_candidates_per_round,
            excluded_ids=evaluated_hypothesis_ids,
        )
        if not selected:
            break

        for hypothesis in selected:
            _append_jsonl(
                campaign_dir / "hypotheses.jsonl",
                {
                    "round_index": int(round_index),
                    "hypothesis_id": hypothesis.hypothesis_id,
                    "source": hypothesis.source,
                    "strategy_source": hypothesis.strategy_source,
                    "tactic_names": list(hypothesis.tactic_names),
                    "max_depth": int(hypothesis.max_depth),
                    "max_expanded": int(hypothesis.max_expanded),
                    "mdl_portal": bool(hypothesis.mdl_portal),
                },
            )

        round_seed_base = seed_start + round_index * round_seed_stride
        train_seeds = [round_seed_base + i * seed_step for i in range(train_count)]
        holdout_seeds = [round_seed_base + holdout_seed_offset + i * seed_step for i in range(holdout_count)]

        round_start_ts = time.monotonic()
        evals_for_round: list[EvalRecord] = []
        train_jobs: list[tuple[Hypothesis, str, int, Path]] = []
        for hypothesis in selected:
            for seed in train_seeds:
                bundle_dir = (
                    campaign_dir
                    / "bundles"
                    / f"round_{round_index:02d}"
                    / hypothesis.hypothesis_id.replace(":", "_")
                    / f"train_seed_{seed}"
                )
                train_jobs.append((hypothesis, "train", int(seed), bundle_dir))
        holdout_jobs: list[tuple[Hypothesis, str, int, Path]] = []

        def _record_eval(rec: EvalRecord) -> None:
            evals_for_round.append(rec)
            all_evals.append(rec)
            evaluated_hypothesis_ids.add(rec.hypothesis_id)
            _append_jsonl(
                campaign_dir / "evaluations.jsonl",
                {
                    "round_index": int(round_index),
                    "hypothesis_id": rec.hypothesis_id,
                    "split": rec.split,
                    "seed": int(rec.seed),
                    "bundle_dir": rec.bundle_dir,
                    "run_returncode": int(rec.run_returncode),
                    "doctor_returncode": int(rec.doctor_returncode),
                    "strict_ok": bool(rec.strict_ok),
                    "outcome": rec.outcome,
                    "expanded": rec.expanded,
                    "visited": rec.visited,
                    "frontier_remaining": rec.frontier_remaining,
                    "duration_seconds": float(rec.duration_seconds),
                },
            )

        def _run_jobs(bundle_jobs: list[tuple[Hypothesis, str, int, Path]]) -> None:
            if not bundle_jobs:
                return
            if max_parallel_bundles == 1:
                for hypothesis, split, seed, bundle_dir in bundle_jobs:
                    rec0 = _run_bundle(
                        root=root,
                        python=python,
                        env=env,
                        domain_import=domain_import,
                        runtime_import=runtime_import,
                        sigma0=sigma0,
                        hypothesis=hypothesis,
                        bundle_dir=bundle_dir,
                        seed=seed,
                        run_timeout_seconds=run_timeout_seconds,
                        hard_timeout_seconds=hard_timeout_seconds,
                    )
                    rec = EvalRecord(
                        hypothesis_id=rec0.hypothesis_id,
                        split=split,
                        seed=rec0.seed,
                        bundle_dir=rec0.bundle_dir,
                        run_returncode=rec0.run_returncode,
                        doctor_returncode=rec0.doctor_returncode,
                        strict_ok=rec0.strict_ok,
                        outcome=rec0.outcome,
                        expanded=rec0.expanded,
                        visited=rec0.visited,
                        frontier_remaining=rec0.frontier_remaining,
                        duration_seconds=rec0.duration_seconds,
                    )
                    _record_eval(rec)
                return

            with concurrent.futures.ThreadPoolExecutor(max_workers=max_parallel_bundles) as pool:
                fut_map: dict[concurrent.futures.Future[EvalRecord], tuple[Hypothesis, str, int, Path]] = {}
                for hypothesis, split, seed, bundle_dir in bundle_jobs:
                    fut = pool.submit(
                        _run_bundle,
                        root=root,
                        python=python,
                        env=env,
                        domain_import=domain_import,
                        runtime_import=runtime_import,
                        sigma0=sigma0,
                        hypothesis=hypothesis,
                        bundle_dir=bundle_dir,
                        seed=seed,
                        run_timeout_seconds=run_timeout_seconds,
                        hard_timeout_seconds=hard_timeout_seconds,
                    )
                    fut_map[fut] = (hypothesis, split, int(seed), bundle_dir)
                for fut in concurrent.futures.as_completed(fut_map):
                    hypothesis, split, seed, bundle_dir = fut_map[fut]
                    try:
                        rec0 = fut.result()
                    except Exception:
                        rec0 = EvalRecord(
                            hypothesis_id=hypothesis.hypothesis_id,
                            split="",
                            seed=int(seed),
                            bundle_dir=str(bundle_dir),
                            run_returncode=1,
                            doctor_returncode=125,
                            strict_ok=False,
                            outcome="ERROR",
                            expanded=None,
                            visited=None,
                            frontier_remaining=None,
                            duration_seconds=0.0,
                        )
                    rec = EvalRecord(
                        hypothesis_id=rec0.hypothesis_id,
                        split=split,
                        seed=rec0.seed,
                        bundle_dir=rec0.bundle_dir,
                        run_returncode=rec0.run_returncode,
                        doctor_returncode=rec0.doctor_returncode,
                        strict_ok=rec0.strict_ok,
                        outcome=rec0.outcome,
                        expanded=rec0.expanded,
                        visited=rec0.visited,
                        frontier_remaining=rec0.frontier_remaining,
                        duration_seconds=rec0.duration_seconds,
                    )
                    _record_eval(rec)

        _run_jobs(train_jobs)

        def _train_rank_key(h: Hypothesis) -> tuple[float, float, float, str]:
            train_records = [r for r in evals_for_round if r.hypothesis_id == h.hypothesis_id and r.split == "train"]
            if not train_records:
                return (0.0, -1.0, -1.0, h.hypothesis_id)
            strict_rate = float(sum(1 for r in train_records if r.strict_ok)) / float(len(train_records))
            avg_visited = (
                float(sum(int(r.visited) for r in train_records if r.visited is not None)) / float(len(train_records))
                if train_records
                else -1.0
            )
            avg_expanded = (
                float(sum(int(r.expanded) for r in train_records if r.expanded is not None)) / float(len(train_records))
                if train_records
                else -1.0
            )
            return (strict_rate, avg_visited, avg_expanded, h.hypothesis_id)

        if holdout_top_k is None or holdout_top_k >= len(selected):
            holdout_selected = list(selected)
        else:
            holdout_selected = sorted(selected, key=_train_rank_key, reverse=True)[:holdout_top_k]
        holdout_selected_ids = {h.hypothesis_id for h in holdout_selected}

        for hypothesis in selected:
            if hypothesis.hypothesis_id not in holdout_selected_ids:
                continue
            for seed in holdout_seeds:
                bundle_dir = (
                    campaign_dir
                    / "bundles"
                    / f"round_{round_index:02d}"
                    / hypothesis.hypothesis_id.replace(":", "_")
                    / f"holdout_seed_{seed}"
                )
                holdout_jobs.append((hypothesis, "holdout", int(seed), bundle_dir))
        _run_jobs(holdout_jobs)

        aggregates: list[dict[str, Any]] = []
        by_hid: dict[str, list[EvalRecord]] = {}
        for rec in evals_for_round:
            by_hid.setdefault(rec.hypothesis_id, []).append(rec)
        for hypothesis in selected:
            records = by_hid.get(hypothesis.hypothesis_id, [])
            row = _aggregate_records(hypothesis=hypothesis, records=records, success_outcomes=success_outcomes)
            row["round_index"] = int(round_index)
            aggregates.append(row)
            _append_jsonl(campaign_dir / "round_aggregates.jsonl", row)

        promoted = _select_promotions(aggregates=aggregates, promotion_cfg=promotion_cfg)
        for p in promoted:
            promotions_total += 1
            p2 = dict(p)
            p2["round_index"] = int(round_index)
            _append_jsonl(campaign_dir / "promotions.jsonl", p2)
            _append_jsonl(
                archive_path,
                {
                    "hypothesis_id": p["hypothesis_id"],
                    "strategy_source": p["strategy_source"],
                    "tactic_names": p["tactic_names"],
                    "max_depth": p["max_depth"],
                    "max_expanded": p["max_expanded"],
                    "mdl_portal": p["mdl_portal"],
                    "promotion_reason": p["promotion_reason"],
                    "promoted_at_utc": _utc_stamp(),
                    "campaign_dir": str(campaign_dir),
                    "round_index": int(round_index),
                },
            )

        round_elapsed_seconds = float(max(0.0, time.monotonic() - round_start_ts))
        round_visited_total = int(sum(int(r.visited) for r in evals_for_round if r.visited is not None))
        round_expanded_total = int(sum(int(r.expanded) for r in evals_for_round if r.expanded is not None))
        round_strict_ok = int(sum(1 for r in evals_for_round if r.strict_ok))
        round_avg_eval_duration = (
            float(sum(float(r.duration_seconds) for r in evals_for_round) / float(len(evals_for_round)))
            if evals_for_round
            else 0.0
        )
        round_summary = {
            "round_index": int(round_index),
            "candidate_count": len(selected),
            "evaluation_count": len(evals_for_round),
            "train_evaluation_count": len(train_jobs),
            "holdout_evaluation_count": len(holdout_jobs),
            "holdout_hypothesis_count": int(len(holdout_selected_ids)),
            "promotion_count": len(promoted),
            "new_hypotheses_in_round": int(sum(1 for h in selected if h.hypothesis_id not in evaluated_before_round)),
            "total_unique_hypotheses_evaluated": int(len(evaluated_hypothesis_ids)),
            "round_elapsed_seconds": round_elapsed_seconds,
            "round_evaluations_per_minute": (
                float(len(evals_for_round)) * 60.0 / round_elapsed_seconds if round_elapsed_seconds > 0 else 0.0
            ),
            "round_unique_hypotheses_per_minute": (
                float(sum(1 for h in selected if h.hypothesis_id not in evaluated_before_round)) * 60.0 / round_elapsed_seconds
                if round_elapsed_seconds > 0
                else 0.0
            ),
            "round_visited_total": round_visited_total,
            "round_expanded_total": round_expanded_total,
            "round_strict_ok_count": round_strict_ok,
            "round_strict_ok_rate": (
                float(round_strict_ok) / float(len(evals_for_round)) if evals_for_round else 0.0
            ),
            "round_avg_eval_duration_seconds": round_avg_eval_duration,
        }
        summary_rows.append(round_summary)
        _append_jsonl(campaign_dir / "round_summaries.jsonl", round_summary)

        if promoted:
            rounds_without_promotion = 0
            archived = _load_archive(archive_path)
            all_hypotheses = _generate_hypotheses(cfg, archived=archived)
        else:
            rounds_without_promotion += 1
            # Rotate window through remaining hypotheses when no promotion lands.
            all_hypotheses = all_hypotheses[candidates_per_round:] + all_hypotheses[:candidates_per_round]

        if rounds_without_promotion >= stop_after_no_promo:
            break

    campaign_elapsed_seconds = float(max(0.0, time.monotonic() - campaign_start_ts))
    total_visited = int(sum(int(r.visited) for r in all_evals if r.visited is not None))
    total_expanded = int(sum(int(r.expanded) for r in all_evals if r.expanded is not None))
    total_strict_ok = int(sum(1 for r in all_evals if r.strict_ok))
    campaign_summary = {
        "schema": "zenodex/mechanical-scientist-perps-campaign/v1",
        "campaign_dir": str(campaign_dir),
        "config_path": str(config_path),
        "quick": bool(quick),
        "total_rounds_executed": len(summary_rows),
        "total_evaluations": len(all_evals),
        "total_unique_hypotheses_evaluated": int(len(evaluated_hypothesis_ids)),
        "total_promotions": int(promotions_total),
        "elapsed_seconds": campaign_elapsed_seconds,
        "evaluations_per_minute": (float(len(all_evals)) * 60.0 / campaign_elapsed_seconds if campaign_elapsed_seconds > 0 else 0.0),
        "unique_hypotheses_per_minute": (
            float(len(evaluated_hypothesis_ids)) * 60.0 / campaign_elapsed_seconds if campaign_elapsed_seconds > 0 else 0.0
        ),
        "visited_per_second": (float(total_visited) / campaign_elapsed_seconds if campaign_elapsed_seconds > 0 else 0.0),
        "total_visited": total_visited,
        "total_expanded": total_expanded,
        "strict_ok_count": total_strict_ok,
        "strict_ok_rate": (float(total_strict_ok) / float(len(all_evals)) if all_evals else 0.0),
    }
    _write_json(campaign_dir / "campaign_summary.json", campaign_summary)
    print(json.dumps(campaign_summary, sort_keys=True, indent=2))
    return 0


def replay_campaign(*, campaign_dir: Path, python: str) -> int:
    root = _repo_root()
    env = _prepare_env(root)
    manifests = sorted(campaign_dir.rglob("manifest.json"))
    if not manifests:
        print(f"no bundle manifests found under {campaign_dir}", file=sys.stderr)
        return 2

    ok = 0
    failed = 0
    for manifest in manifests:
        bundle_dir = manifest.parent
        cmd = [python, "-m", "morph", "doctor", "--strict", str(bundle_dir)]
        proc = subprocess.run(cmd, cwd=str(root), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if proc.returncode == 0:
            ok += 1
        else:
            failed += 1
            sys.stderr.write(f"[replay-fail] {bundle_dir}\n")
            sys.stderr.write(proc.stdout)
            if not proc.stdout.endswith("\n"):
                sys.stderr.write("\n")

    summary = {"bundles_checked": len(manifests), "ok": ok, "failed": failed}
    print(json.dumps(summary, sort_keys=True, indent=2))
    return 0 if failed == 0 else 1


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Mechanical scientist campaign for ZenoDEX perps parity.")
    sub = ap.add_subparsers(dest="cmd", required=True)

    campaign = sub.add_parser("campaign", help="Run a perps scientist campaign with strict evidence gating.")
    campaign.add_argument("--config", type=Path, default=_default_config_path())
    campaign.add_argument("--out", type=Path, default=None, help="Campaign output directory (defaults under runs/morph).")
    campaign.add_argument("--quick", action="store_true", help="Use a tiny smoke configuration override.")

    replay = sub.add_parser("replay", help="Replay strict doctor across all bundles in a campaign directory.")
    replay.add_argument("--campaign-dir", type=Path, required=True)
    replay.add_argument("--python", type=str, default="python3.11")

    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    if args.cmd == "campaign":
        return run_campaign(config_path=args.config.resolve(), out_dir=(args.out.resolve() if args.out else None), quick=bool(args.quick))
    if args.cmd == "replay":
        return replay_campaign(campaign_dir=args.campaign_dir.resolve(), python=str(args.python))
    raise SystemExit("unknown command")


if __name__ == "__main__":
    raise SystemExit(main())
