#!/usr/bin/env python3
"""Summarize MacOS scout outputs into a compact review note."""

from __future__ import annotations

import json
import sys
from collections import Counter
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


def _count_reasons(path: Path) -> dict[str, int]:
    counts: Counter[str] = Counter()
    if not path.exists():
        return {}
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                counts[json.loads(line)["reason"]] += 1
    return dict(sorted(counts.items()))


def _strict_candidate_ok(item: dict[str, Any]) -> bool:
    candidate = item.get("candidate", {})
    if not isinstance(candidate, dict):
        return False
    if float(item.get("disaster_rate", 1.0)) != 0.0:
        return False
    if item.get("legal_shape_ok") is not True:
        return False
    if float(item.get("min_insurance_ratio", 0.0)) < 1.0:
        return False
    if float(item.get("guard_block_rate", 1.0)) > 0.05:
        return False
    if float(item.get("payout_budget_clamp_rate", 1.0)) > 0.50:
        return False
    if float(item.get("funding_clamp_rate", 1.0)) > 0.50:
        return False
    fee_burn_share = float(candidate.get("fee_burn_share", 1.0))
    insurance_share = float(candidate.get("insurance_share", 1.0))
    payout_cap_share = float(candidate.get("payout_cap_share", 1.0))
    return fee_burn_share + insurance_share <= 0.95 and payout_cap_share <= 0.50


def _write_jsonl(path: Path, items: list[dict[str, Any]]) -> None:
    path.write_text(
        "".join(json.dumps(item, sort_keys=True, separators=(",", ":")) + "\n" for item in items),
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: summarize_scout_outputs.py <outdir>", file=sys.stderr)
        return 2
    outdir = Path(argv[1])
    summary = _read_summary(outdir / "summary.json")
    top = _read_jsonl(outdir / "top_candidates.jsonl", 5)
    reranked = _read_jsonl(outdir / "reranked_top_candidates.jsonl", 5)
    counterexamples = _read_jsonl(outdir / "counterexamples.jsonl", 10)
    reason_counts = _count_reasons(outdir / "counterexamples.jsonl")
    strict_promotions = [item for item in _read_jsonl(outdir / "reranked_top_candidates.jsonl", 10**12) if _strict_candidate_ok(item)]
    _write_jsonl(outdir / "promotion_candidates.jsonl", strict_promotions)
    (outdir / "reason_counts.json").write_text(json.dumps(reason_counts, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines = [
        "# MacOS Scout Review",
        "",
        f"- Output: `{outdir}`",
        f"- Candidates: {summary.get('candidates', 'unknown')}",
        f"- Paths: {summary.get('paths', 'unknown')}",
        f"- Steps: {summary.get('steps', 'unknown')}",
        f"- Counterexamples: {summary.get('counterexample_count', 'unknown')}",
        f"- Zero-disaster legal-shape candidates: {summary.get('zero_disaster_legal_shape_count', 'unknown')}",
        f"- Screen seconds: {summary.get('screen_seconds', 'unknown')}",
        f"- Rerank seconds: {summary.get('rerank_seconds', 'unknown')}",
        f"- Retained bytes estimate: {summary.get('retained_bytes_estimate', 'unknown')}",
        f"- Strict promotion candidates: {len(strict_promotions)}",
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

    lines.extend(["", "## Reranked Top Candidates", ""])
    if not reranked:
        lines.append("- reranking was disabled or produced no candidates")
    for item in reranked:
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

    lines.extend(["", "## Counterexample Reason Counts", ""])
    if not reason_counts:
        lines.append("- none recorded in the bounded run")
    for reason, count in sorted(reason_counts.items(), key=lambda item: (-item[1], item[0])):
        lines.append(f"- {reason}: {count}")

    lines.extend(["", "## Strict Promotion Candidates", ""])
    if not strict_promotions:
        lines.append("- none passed the strict no-disaster/legal-shape/guard-use gate")
    for item in strict_promotions[:5]:
        lines.append(
            "- id={id} score={score:.4f} guard_block_rate={guard_block_rate:.8f} "
            "payout_budget_clamp_rate={payout_budget_clamp_rate:.8f} funding_clamp_rate={funding_clamp_rate:.8f}".format(
                id=item["id"],
                score=float(item["score"]),
                guard_block_rate=float(item.get("guard_block_rate", 0.0)),
                payout_budget_clamp_rate=float(item.get("payout_budget_clamp_rate", 0.0)),
                funding_clamp_rate=float(item.get("funding_clamp_rate", 0.0)),
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
