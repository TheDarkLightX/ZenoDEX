#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

from metamuse_split_routing_lane import lane_packet


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _arg_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _run_cmd(cmd: list[str], *, cwd: Path) -> dict[str, Any]:
    t0 = time.time()
    proc = subprocess.run(cmd, cwd=str(cwd), text=True, capture_output=True)
    return {
        "command": cmd,
        "rc": int(proc.returncode),
        "duration_s": float(time.time() - t0),
        "stdout_tail": str(proc.stdout or "")[-4000:],
        "stderr_tail": str(proc.stderr or "")[-4000:],
    }


def build_epoch_packet() -> dict[str, Any]:
    lane = lane_packet()
    return {
        "schema": "zenodex/metamuse-epoch/v1",
        "generated_at_unix": int(time.time()),
        "lane": {
            "lane_id": lane["lane_id"],
            "title": lane["title"],
            "representation": lane["representation"],
            "abstraction_level": lane["abstraction_level"],
            "goal": lane["goal"],
            "obligations": lane["obligations"],
        },
        "waypoints": {
            "problem_invariants": lane["invariants"],
            "baseline_families": lane["baseline_families"],
            "reformulation_axes": lane["reformulation_axes"],
            "candidate_principles": [h["mechanism_change"] for h in lane["hypotheses"]],
            "performance_descriptors": lane["performance_descriptors"],
            "curated_corpus_size": len(lane["curated_corpus"]),
        },
        "stimuli": lane["stimuli"],
        "hypotheses": lane["hypotheses"],
        "curated_corpus": lane["curated_corpus"],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Emit and optionally run a MetaMuse-style ZenoDEX algorithm epoch.")
    ap.add_argument("--lane", default="split_routing_exact_in_dgstr")
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument("--run-checks", action="store_true")
    args = ap.parse_args()

    if str(args.lane).strip() != "split_routing_exact_in_dgstr":
        raise SystemExit(f"unsupported lane: {args.lane}")

    out_dir = (ROOT / args.out_dir).resolve() if not args.out_dir.is_absolute() else args.out_dir
    packet = build_epoch_packet()
    _write_json(out_dir / "epoch_packet.json", packet)
    _write_json(out_dir / "waypoints.json", packet["waypoints"])
    _write_json(out_dir / "stimuli.json", packet["stimuli"])
    _write_json(out_dir / "hypotheses.json", {"hypotheses": packet["hypotheses"]})
    _write_json(out_dir / "curated_corpus.json", packet["curated_corpus"])

    result: dict[str, Any] = {
        "schema": "zenodex/metamuse-epoch-result/v1",
        "lane": str(args.lane),
        "out_dir": str(out_dir),
        "run_checks": bool(args.run_checks),
    }
    if args.run_checks:
        run_dir = out_dir / "supervised_run"
        cmd = [
            "python3",
            "tools/zenodex_manual_supervised_runner.py",
            "--hypotheses-json",
            _arg_path(out_dir / "hypotheses.json"),
            "--out-dir",
            _arg_path(run_dir),
        ]
        run_info = _run_cmd(cmd, cwd=ROOT)
        result["runner"] = run_info
        if run_info["rc"] == 0:
            summary_path = run_dir / "summary.json"
            analysis_path = run_dir / "analysis.json"
            if summary_path.exists():
                result["summary"] = json.loads(summary_path.read_text(encoding="utf-8"))
            if analysis_path.exists():
                result["analysis"] = json.loads(analysis_path.read_text(encoding="utf-8"))

    _write_json(out_dir / "result.json", result)
    print(json.dumps({"ok": True, "out_dir": str(out_dir), "run_checks": bool(args.run_checks)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
