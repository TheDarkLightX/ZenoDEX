#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _read_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _append_jsonl(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(row, sort_keys=True) + "\n")


def _run_cmd(cmd: list[str], timeout_s: int = 7200) -> tuple[int | None, str, str, float, bool]:
    t0 = time.time()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(ROOT),
            text=True,
            capture_output=True,
            timeout=max(1, int(timeout_s)),
        )
    except subprocess.TimeoutExpired as exc:
        return None, str(exc.stdout or ""), str(exc.stderr or ""), float(time.time() - t0), True
    return int(proc.returncode), proc.stdout, proc.stderr, float(time.time() - t0), False


def _discover_pytest_files() -> list[str]:
    files: list[str] = []
    for sub in ("tests/core", "tests/state", "tests/formal"):
        root = ROOT / sub
        if not root.exists():
            continue
        for p in sorted(root.rglob("test_*.py")):
            if p.is_file():
                files.append(str(p.relative_to(ROOT)))
    return sorted(set(files))


def _base_hypothesis_count() -> int:
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from tools.zenodex_autonomous_scientist import _candidate_specs  # pylint: disable=import-outside-toplevel

    return len(_candidate_specs())


def _slice_window(items: list[str], start: int, count: int) -> list[str]:
    if not items or count <= 0:
        return []
    n = len(items)
    out: list[str] = []
    for i in range(count):
        out.append(items[(start + i) % n])
    return out


def _summarize_cycle(cycle_dir: Path) -> dict[str, Any]:
    state = _read_json(cycle_dir / "state.json", default={})
    rows = []
    p = cycle_dir / "epoch_summaries.jsonl"
    if p.exists():
        rows = [json.loads(x) for x in p.read_text(encoding="utf-8").splitlines() if x.strip()]

    status_counts: dict[str, int] = {}
    for h in (state.get("hypotheses") or {}).values():
        st = str(h.get("status", "unknown"))
        status_counts[st] = int(status_counts.get(st, 0)) + 1

    transform_scores: dict[str, Any] = {}
    check_coverage = None
    repeat_share = None
    frontier_tail = []
    frontier_tail_avg = None
    frontier_contrib: dict[str, float] = {}
    if rows:
        last = rows[-1]
        for deep in (last.get("outputs") or {}).get("deep_insights", []):
            det = deep.get("details") or {}
            if "transform_scores" in det:
                transform_scores = det["transform_scores"]
            if "check_coverage_ratio" in det:
                check_coverage = float(det["check_coverage_ratio"])
            if "repeat_share_of_events" in det:
                repeat_share = float(det["repeat_share_of_events"])
            if "frontier_gain_tail" in det:
                frontier_tail = [int(x) for x in det.get("frontier_gain_tail", [])]
                frontier_tail_avg = float(det.get("frontier_gain_tail_avg", 0.0))
            if "frontier_positive_contribution_by_transform" in det:
                frontier_contrib = {
                    str(k): float(v) for k, v in (det.get("frontier_positive_contribution_by_transform") or {}).items()
                }

    falsified_ids: list[str] = []
    supported_ids: list[str] = []
    for row in rows:
        out = row.get("outputs") or {}
        falsified_ids.extend(str(x.get("hypothesis_id")) for x in out.get("newly_falsified", []))
        supported_ids.extend(str(x.get("hypothesis_id")) for x in out.get("newly_supported", []))

    final_roadmap = _read_json(cycle_dir / "final_roadmap.json", default={})
    decisions = {"promote": 0, "drop": 0, "iterate": 0}
    for row in (final_roadmap.get("rows") or []):
        d = str(row.get("decision", "iterate"))
        decisions[d] = int(decisions.get(d, 0)) + 1

    return {
        "epochs_completed": int(state.get("last_epoch", 0)),
        "status_counts": status_counts,
        "decisions": decisions,
        "supported_ids": sorted(set(supported_ids)),
        "falsified_ids": sorted(set(falsified_ids)),
        "transform_scores": transform_scores,
        "check_coverage_ratio": check_coverage,
        "repeat_share_of_events": repeat_share,
        "frontier_gain_tail": frontier_tail,
        "frontier_gain_tail_avg": frontier_tail_avg,
        "frontier_positive_contribution_by_transform": frontier_contrib,
    }


def _next_cycle_params(
    *,
    exploration_ratio: float,
    replay_repeats: int,
    max_width: int,
    summary: dict[str, Any],
) -> tuple[float, int, int, list[str]]:
    notes: list[str] = []
    exp = float(exploration_ratio)
    rep = int(replay_repeats)
    width = int(max_width)

    repeat_share = summary.get("repeat_share_of_events")
    if isinstance(repeat_share, float) and repeat_share >= 0.2:
        rep = min(9, rep + 1)
        exp = min(0.85, exp + 0.03)
        notes.append("repeat_share_high: increased replay repeats and exploration")

    tail_avg = summary.get("frontier_gain_tail_avg")
    if isinstance(tail_avg, float):
        if tail_avg <= 1.0:
            exp = min(0.9, exp + 0.05)
            width = min(16, width + 1)
            notes.append("frontier_gain_low: widened search and exploration")
        elif tail_avg >= 4.0:
            exp = max(0.55, exp - 0.02)
            notes.append("frontier_gain_high: slightly shifted toward exploitation")

    tf = summary.get("transform_scores") or {}
    relax = tf.get("relax") if isinstance(tf, dict) else None
    if isinstance(relax, dict):
        if float(relax.get("falsify_rate", 0.0)) >= 0.9 and int(relax.get("total", 0)) >= 6:
            notes.append("relax_falsify_near_1: prioritize restrict/reduce/equiv variants next")

    return exp, rep, width, notes


def main() -> int:
    ap = argparse.ArgumentParser(description="Supervised multi-cycle ZenoDEX research loop (100+ hypotheses/cycle).")
    ap.add_argument("--loop-root", type=Path, default=Path("runs/supervised_research_loop"))
    ap.add_argument("--pad", type=Path, default=Path("internal/popperpad/zenodex"))
    ap.add_argument("--cycles", type=int, default=3)
    ap.add_argument("--hypotheses-per-cycle", type=int, default=100)
    ap.add_argument("--max-epochs", type=int, default=8)
    ap.add_argument("--min-epochs", type=int, default=4)
    ap.add_argument("--max-width", type=int, default=10)
    ap.add_argument("--exploration-ratio", type=float, default=0.68)
    ap.add_argument("--max-supported-repeats", type=int, default=2)
    ap.add_argument("--max-falsified-repeats", type=int, default=1)
    ap.add_argument("--stagnation-epochs", type=int, default=6)
    ap.add_argument("--marginal-frontier-threshold", type=int, default=0)
    ap.add_argument("--auto-pytest-replay-repeats", type=int, default=3)
    ap.add_argument("--scientist-timeout-s", type=int, default=7200)
    args = ap.parse_args()

    loop_root = (ROOT / args.loop_root).resolve()
    loop_root.mkdir(parents=True, exist_ok=True)

    all_pytests = _discover_pytest_files()
    base_count = _base_hypothesis_count()
    target = max(1, int(args.hypotheses_per_cycle))
    extra_needed = max(0, target - base_count)
    files_per_cycle = max(0, math.ceil(extra_needed / 3.0))

    history_path = loop_root / "cycle_history.jsonl"
    _write_json(
        loop_root / "loop_config.json",
        {
            "schema": "zenodex/supervised-loop-config/v1",
            "created_at": _now_iso(),
            "base_hypothesis_count": base_count,
            "pytest_file_count": len(all_pytests),
            "target_hypotheses_per_cycle": target,
            "files_per_cycle": files_per_cycle,
            "cycles": int(args.cycles),
        },
    )

    exploration = float(args.exploration_ratio)
    replay_repeats = max(2, int(args.auto_pytest_replay_repeats))
    width = max(1, int(args.max_width))
    cycle_reports: list[dict[str, Any]] = []

    for cycle in range(1, max(1, int(args.cycles)) + 1):
        cycle_name = f"cycle_{cycle:03d}"
        cycle_root = loop_root / cycle_name
        offset = 0
        if all_pytests:
            offset = ((cycle - 1) * max(1, files_per_cycle)) % len(all_pytests)
        pytest_window = _slice_window(all_pytests, offset, files_per_cycle)

        scientist_cmd = [
            "python3",
            "tools/zenodex_autonomous_scientist.py",
            "--run-root",
            str(cycle_root.relative_to(ROOT)),
            "--pad",
            str(args.pad),
            "--max-epochs",
            str(max(1, int(args.max_epochs))),
            "--min-epochs",
            str(max(1, int(args.min_epochs))),
            "--max-width",
            str(max(1, int(width))),
            "--exploration-ratio",
            str(exploration),
            "--max-supported-repeats",
            str(max(1, int(args.max_supported_repeats))),
            "--max-falsified-repeats",
            str(max(0, int(args.max_falsified_repeats))),
            "--stagnation-epochs",
            str(max(1, int(args.stagnation_epochs))),
            "--marginal-frontier-threshold",
            str(int(args.marginal_frontier_threshold)),
            "--target-hypotheses",
            str(target),
            "--auto-pytest-hypotheses",
            "--max-auto-pytest-files",
            str(max(0, files_per_cycle)),
            "--auto-pytest-offset-files",
            str(offset),
            "--auto-pytest-replay-repeats",
            str(replay_repeats),
        ]
        rc, out, err, dt, timed_out = _run_cmd(scientist_cmd, timeout_s=max(60, int(args.scientist_timeout_s)))

        summary = _summarize_cycle(cycle_root)
        cycle_report = {
            "schema": "zenodex/supervised-cycle-report/v1",
            "cycle": cycle,
            "at": _now_iso(),
            "cycle_root": str(cycle_root),
            "scientist": {
                "command": scientist_cmd,
                "returncode": rc,
                "timeout": timed_out,
                "duration_s": dt,
                "stdout_tail": out[-2000:],
                "stderr_tail": err[-2000:],
            },
            "hypothesis_target": target,
            "pytest_offset": offset,
            "pytest_window": pytest_window,
            "summary": summary,
        }
        _write_json(cycle_root / "cycle_review.json", cycle_report)
        _append_jsonl(history_path, cycle_report)
        cycle_reports.append(cycle_report)

        exploration, replay_repeats, width, notes = _next_cycle_params(
            exploration_ratio=exploration,
            replay_repeats=replay_repeats,
            max_width=width,
            summary=summary,
        )
        _write_json(
            cycle_root / "next_cycle_plan.json",
            {
                "schema": "zenodex/supervised-next-cycle-plan/v1",
                "generated_at": _now_iso(),
                "next_exploration_ratio": exploration,
                "next_auto_pytest_replay_repeats": replay_repeats,
                "next_max_width": width,
                "notes": notes,
            },
        )
        if timed_out:
            break

    aggregate = {
        "schema": "zenodex/supervised-loop-summary/v1",
        "generated_at": _now_iso(),
        "loop_root": str(loop_root),
        "cycles_requested": int(args.cycles),
        "cycles_completed": len(cycle_reports),
        "cycle_dirs": [r["cycle_root"] for r in cycle_reports],
    }
    _write_json(loop_root / "loop_summary.json", aggregate)
    print(json.dumps({"ok": True, **aggregate}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
