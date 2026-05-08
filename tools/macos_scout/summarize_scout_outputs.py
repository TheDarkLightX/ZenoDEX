#!/usr/bin/env python3
"""Summarize MacOS scout outputs into a compact review note."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


def _read_jsonl(path: Path, limit: int) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    out: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if len(out) >= limit:
                break
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out


def _read_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    text = path.read_text(encoding="utf-8").strip()
    return json.loads(text) if text else {}


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: summarize_scout_outputs.py <outdir>", file=sys.stderr)
        return 2
    outdir = Path(argv[1])
    summary = _read_summary(outdir / "summary.json")
    top = _read_jsonl(outdir / "top_candidates.jsonl", 5)
    counterexamples = _read_jsonl(outdir / "counterexamples.jsonl", 10)

    lines = [
        "# MacOS Scout Review",
        "",
        f"- Output: `{outdir}`",
        f"- Candidates: {summary.get('candidates', 'unknown')}",
        f"- Paths: {summary.get('paths', 'unknown')}",
        f"- Steps: {summary.get('steps', 'unknown')}",
        f"- Counterexamples: {summary.get('counterexample_count', 'unknown')}",
        f"- Zero-disaster legal-shape candidates: {summary.get('zero_disaster_legal_shape_count', 'unknown')}",
        "",
        "## Top Candidates",
        "",
    ]
    for item in top:
        lines.append(
            "- id={id} score={score:.4f} disaster_rate={disaster_rate:.8f} "
            "deflation_bps={deflation_bps:.4f} p99_drawdown_bps={p99_drawdown_bps:.4f}".format(
                id=item["id"],
                score=float(item["score"]),
                disaster_rate=float(item["disaster_rate"]),
                deflation_bps=float(item["deflation_bps"]),
                p99_drawdown_bps=float(item["p99_drawdown_bps"]),
            )
        )

    lines.extend(["", "## First Counterexamples", ""])
    if not counterexamples:
        lines.append("- none recorded in the bounded run")
    for item in counterexamples:
        lines.append(
            "- id={id} path={path} step={step} reason={reason} "
            "insurance={insurance:.4f} liquidity={liquidity:.6f}".format(
                id=item["id"],
                path=item["path"],
                step=item["step"],
                reason=item["reason"],
                insurance=float(item["insurance"]),
                liquidity=float(item["liquidity"]),
            )
        )

    lines.extend(
        [
            "",
            "## Required Follow-up",
            "",
            "1. Re-run the best candidates with a different seed.",
            "2. Convert repeated counterexample reasons into regression tests.",
            "3. Draft a Lean/SMT proof target for any formula worth promoting.",
        ]
    )

    review_path = outdir / "review.md"
    review_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(review_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
