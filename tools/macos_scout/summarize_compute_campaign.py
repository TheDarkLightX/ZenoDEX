#!/usr/bin/env python3
"""Summarize a multi-run MacOS scout compute campaign."""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    text = path.read_text(encoding="utf-8").strip()
    return json.loads(text) if text else {}


def _read_first_jsonl(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                return json.loads(line)
    return None


def _read_reason_counts(path: Path) -> dict[str, int]:
    if not path.exists():
        return {}
    counts: Counter[str] = Counter()
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            item = json.loads(line)
            reason = item.get("reason")
            if reason is not None:
                counts[str(reason)] += 1
    return dict(sorted(counts.items()))


def _receipt_status(receipt: dict[str, Any]) -> str | None:
    status = receipt.get("status")
    if isinstance(status, str) and status.strip():
        return status.strip()
    ok = receipt.get("ok")
    if ok is True:
        return "accepted"
    if ok is False:
        return "rejected"
    return None


def _receipt_hash(receipt: dict[str, Any]) -> str | None:
    for key in ("receipt_hash", "stable_receipt_hash"):
        value = receipt.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return None


def _campaign_runs(campaign_root: Path) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []
    for path in sorted(campaign_root.iterdir()):
        if not path.is_dir():
            continue
        summary_path = path / "summary.json"
        if not summary_path.exists():
            continue
        summary = _read_json(summary_path)
        gate = _read_json(path / "regression_gate.json")
        witness = _read_json(path / "witness_space_receipt.json")
        first_promotion = _read_first_jsonl(path / "promotion_candidates.jsonl")
        reason_counts = _read_json(path / "reason_counts.json") or _read_reason_counts(path / "counterexamples.jsonl")
        runs.append(
            {
                "path": str(path),
                "seed": summary.get("seed"),
                "candidates": summary.get("candidates"),
                "paths": summary.get("paths"),
                "steps": summary.get("steps"),
                "counterexample_count": summary.get("counterexample_count"),
                "zero_disaster_legal_shape_count": summary.get("zero_disaster_legal_shape_count"),
                "screen_seconds": summary.get("screen_seconds"),
                "rerank_seconds": summary.get("rerank_seconds"),
                "retained_bytes_estimate": summary.get("retained_bytes_estimate"),
                "gate_status": _receipt_status(gate),
                "gate_receipt_hash": _receipt_hash(gate),
                "witness_status": _receipt_status(witness),
                "witness_receipt_hash": _receipt_hash(witness),
                "first_promotion_id": None if first_promotion is None else first_promotion.get("id"),
                "first_promotion_score": None if first_promotion is None else first_promotion.get("score"),
                "reason_counts": reason_counts,
            }
        )
    return runs


def _write_campaign_summary(campaign_root: Path, runs: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate_reasons: Counter[str] = Counter()
    for run in runs:
        for reason, count in dict(run.get("reason_counts") or {}).items():
            aggregate_reasons[str(reason)] += int(count)
    campaign_witness = _read_json(campaign_root / "witness_space_receipt.json")

    payload = {
        "schema": "zenodex/macos-scout-compute-campaign/v1",
        "campaign_root": str(campaign_root),
        "run_count": len(runs),
        "accepted_gate_count": sum(1 for run in runs if run.get("gate_status") == "accepted"),
        "accepted_witness_count": sum(1 for run in runs if run.get("witness_status") == "accepted"),
        "campaign_witness_status": _receipt_status(campaign_witness),
        "campaign_witness_receipt_hash": _receipt_hash(campaign_witness),
        "campaign_reachable_witness_count": campaign_witness.get("reachable_witness_count"),
        "total_candidates": sum(int(run.get("candidates") or 0) for run in runs),
        "total_counterexamples": sum(int(run.get("counterexample_count") or 0) for run in runs),
        "total_zero_disaster_legal_shape": sum(int(run.get("zero_disaster_legal_shape_count") or 0) for run in runs),
        "aggregate_reason_counts": dict(sorted(aggregate_reasons.items())),
        "runs": runs,
    }
    (campaign_root / "campaign_summary.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _write_review(campaign_root: Path, payload: dict[str, Any]) -> Path:
    lines = [
        "# MacOS Compute Campaign Review",
        "",
        f"- Campaign root: `{payload['campaign_root']}`",
        f"- Runs: {payload['run_count']}",
        f"- Accepted regression gates: {payload['accepted_gate_count']}",
        f"- Accepted witness receipts: {payload['accepted_witness_count']}",
        f"- Campaign witness receipt: {payload.get('campaign_witness_status') or 'missing'}",
        f"- Campaign witness receipt hash: {payload.get('campaign_witness_receipt_hash') or 'missing'}",
        f"- Campaign reachable witnesses: {payload.get('campaign_reachable_witness_count') if payload.get('campaign_reachable_witness_count') is not None else 'unknown'}",
        f"- Total candidates screened: {payload['total_candidates']}",
        f"- Total counterexamples: {payload['total_counterexamples']}",
        f"- Total zero-disaster legal-shape candidates: {payload['total_zero_disaster_legal_shape']}",
        "",
        "## Runs",
        "",
        "| run | seed | candidates | paths | steps | counterexamples | gate | witness | first promotion |",
        "| --- | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |",
    ]
    for run in payload["runs"]:
        first_promotion = run.get("first_promotion_id") or ""
        lines.append(
            "| `{path}` | {seed} | {candidates} | {paths} | {steps} | {counterexamples} | {gate} | {witness} | {promotion} |".format(
                path=run["path"],
                seed=run.get("seed", ""),
                candidates=run.get("candidates", ""),
                paths=run.get("paths", ""),
                steps=run.get("steps", ""),
                counterexamples=run.get("counterexample_count", ""),
                gate=run.get("gate_status", ""),
                witness=run.get("witness_status", ""),
                promotion=first_promotion,
            )
        )

    lines.extend(["", "## Aggregate Counterexample Reasons", ""])
    aggregate = payload.get("aggregate_reason_counts") or {}
    if not aggregate:
        lines.append("- none recorded")
    for reason, count in sorted(aggregate.items(), key=lambda item: (-item[1], item[0])):
        lines.append(f"- {reason}: {count}")

    lines.extend(
        [
            "",
            "## Promotion Rules",
            "",
            "1. Promote no candidate unless it survives at least two seeds.",
            "2. Turn repeated counterexample classes into public regression tests before mechanism notes.",
            "3. Pair every proposed formula with a Lean, SMT, or bounded replay proof target.",
            "4. Treat this campaign as bounded evidence. It does not establish live production safety.",
        ]
    )

    review_path = campaign_root / "campaign_review.md"
    review_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return review_path


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: summarize_compute_campaign.py <campaign_root>", file=sys.stderr)
        return 2
    campaign_root = Path(argv[1])
    if not campaign_root.is_dir():
        print(f"campaign root does not exist: {campaign_root}", file=sys.stderr)
        return 2
    runs = _campaign_runs(campaign_root)
    payload = _write_campaign_summary(campaign_root, runs)
    review_path = _write_review(campaign_root, payload)
    print(review_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
