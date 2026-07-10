#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_token(text: str, *, max_len: int = 120) -> str:
    chars = []
    for ch in str(text):
        if ch.isalnum() or ch in "_.-":
            chars.append(ch)
        else:
            chars.append("_")
    token = "".join(chars).strip("._")
    if not token:
        token = "x"
    return token[:max_len]


def _load_hypotheses(path: Path) -> list[dict[str, Any]]:
    raw = _read_json(path)
    if isinstance(raw, list):
        rows = raw
    elif isinstance(raw, dict):
        rows = raw.get("hypotheses", [])
    else:
        rows = []
    return [x for x in rows if isinstance(x, dict)]


def _run_check(*, check_id: str, mode: str, timeout_s: int, json_out: Path) -> dict[str, Any]:
    cmd = [
        "python3",
        "tools/zenodex_autonomous_checks.py",
        "--check",
        check_id,
        "--mode",
        mode,
        "--timeout-s",
        str(int(timeout_s)),
        "--json-out",
        str(json_out),
    ]
    t0 = time.time()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(ROOT),
            text=True,
            capture_output=True,
            timeout=max(1, int(timeout_s) + 90),
        )
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        return {
            "rc": None,
            "timed_out": True,
            "duration_s": float(time.time() - t0),
            "stdout_tail": str(exc.stdout or "")[-2000:],
            "stderr_tail": str(exc.stderr or "")[-2000:],
            "payload": {"status": "fail", "reason": "timeout"},
        }

    payload: dict[str, Any] = {}
    if json_out.exists():
        try:
            payload = _read_json(json_out)
        except Exception:
            payload = {}

    return {
        "rc": int(proc.returncode),
        "timed_out": timed_out,
        "duration_s": float(time.time() - t0),
        "stdout_tail": str(proc.stdout or "")[-2000:],
        "stderr_tail": str(proc.stderr or "")[-2000:],
        "payload": payload,
    }


def _dominates(a: list[float], b: list[float]) -> bool:
    return all(x >= y for x, y in zip(a, b)) and any(x > y for x, y in zip(a, b))


def main() -> int:
    ap = argparse.ArgumentParser(description="Manual/supervised deterministic hypothesis runner.")
    ap.add_argument("--hypotheses-json", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, required=True)
    args = ap.parse_args()

    hyp_path = (ROOT / args.hypotheses_json).resolve() if not args.hypotheses_json.is_absolute() else args.hypotheses_json
    out_dir = (ROOT / args.out_dir).resolve() if not args.out_dir.is_absolute() else args.out_dir
    results_dir = out_dir / "results"
    results_dir.mkdir(parents=True, exist_ok=True)

    hypotheses = _load_hypotheses(hyp_path)
    print(f"Loaded {len(hypotheses)} hypotheses from {hyp_path}")

    summary_rows: list[dict[str, Any]] = []
    by_id: dict[str, dict[str, Any]] = {}

    for i, h in enumerate(hypotheses, 1):
        hid = str(h.get("hypothesis_id", ""))
        if not hid:
            continue
        by_id[hid] = h
        refute_check_id = str(h.get("falsification_recipe", h.get("support_recipe", "")))
        support_check_id = str(h.get("support_recipe", h.get("falsification_recipe", "")))
        timeout_s = int(h.get("timeout_s", 180))

        hdir = results_dir / _safe_token(hid, max_len=180)
        hdir.mkdir(parents=True, exist_ok=True)

        started = int(time.time())
        ref_json = hdir / f"{_safe_token(hid)}_refute_{_safe_token(refute_check_id)}.json"
        refute = _run_check(check_id=refute_check_id, mode="refute", timeout_s=timeout_s, json_out=ref_json)

        support: dict[str, Any] | None = None
        final_status = "inconclusive"
        if (refute.get("payload") or {}).get("status") == "pass":
            final_status = "falsified"
        else:
            sup_json = hdir / f"{_safe_token(hid)}_support_{_safe_token(support_check_id)}.json"
            support = _run_check(check_id=support_check_id, mode="support", timeout_s=timeout_s, json_out=sup_json)
            if (support.get("payload") or {}).get("status") == "pass":
                final_status = "supported"

        finished = int(time.time())
        rec = {
            "hypothesis_id": hid,
            "refute_check": refute_check_id,
            "support_check": support_check_id,
            "started_at": started,
            "finished_at": finished,
            "duration_s": max(0, finished - started),
            "timeout_s": timeout_s,
            "final_status": final_status,
            "refute": refute,
        }
        if support is not None:
            rec["support"] = support
        _write_json(hdir / "result.json", rec)

        summary_rows.append(
            {
                "hypothesis_id": hid,
                "refute_check": refute_check_id,
                "support_check": support_check_id,
                "final_status": final_status,
                "duration_s": rec["duration_s"],
            }
        )
        print(f"[{i}/{len(hypotheses)}] {hid} -> {final_status}")

    summary = {
        "count": len(summary_rows),
        "created_at": int(time.time()),
        "rows": sorted(summary_rows, key=lambda r: r["hypothesis_id"]),
    }
    _write_json(out_dir / "summary.json", summary)

    status_counts: dict[str, int] = {"supported": 0, "falsified": 0, "inconclusive": 0}
    transform_breakdown: dict[str, dict[str, int]] = {}
    supported_rows: list[dict[str, Any]] = []
    for row in summary_rows:
        st = str(row["final_status"])
        status_counts[st] = int(status_counts.get(st, 0)) + 1
        hyp = by_id.get(str(row["hypothesis_id"]), {})
        tr = str(hyp.get("representation_shift_used", "unknown"))
        tb = transform_breakdown.setdefault(tr, {"total": 0, "supported": 0, "falsified": 0, "inconclusive": 0})
        tb["total"] += 1
        tb[st] = int(tb.get(st, 0)) + 1
        if st == "supported":
            vec = [float(x) for x in hyp.get("expected_metric_delta", [0, 0, 0, 0, 0])]
            supported_rows.append({"hypothesis_id": row["hypothesis_id"], "vector": vec, "transform": tr})

    frontier: list[dict[str, Any]] = []
    for a in supported_rows:
        if any(_dominates(b["vector"], a["vector"]) for b in supported_rows if b["hypothesis_id"] != a["hypothesis_id"]):
            continue
        frontier.append(a)
    frontier.sort(key=lambda r: (sum(r["vector"]), r["hypothesis_id"]), reverse=True)

    analysis = {
        "schema": "zenodex/manual-supervised-analysis/v1",
        "created_at": int(time.time()),
        "source_hypotheses": str(hyp_path),
        "run_dir": str(out_dir),
        "totals": status_counts,
        "transform_breakdown": transform_breakdown,
        "pareto_frontier": frontier,
    }
    _write_json(out_dir / "analysis.json", analysis)

    print(
        json.dumps(
            {
                "ok": True,
                "out": str(out_dir),
                "totals": status_counts,
                "frontier_size": len(frontier),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
