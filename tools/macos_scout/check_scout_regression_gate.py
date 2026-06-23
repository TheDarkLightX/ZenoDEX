#!/usr/bin/env python3
"""Fail-closed regression gate for MacOS scout disaster outputs."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = ROOT / "tools" / "macos_scout" / "scout_regression_manifest.json"
MANIFEST_SCHEMA = "zenodex/macos-scout-regression-manifest/v1"
CHECK_SCHEMA = "zenodex/macos-scout-regression-gate/v1"
ALLOWED_STATUSES = {
    "repeat_regression_target",
    "declared_simulator_sentinel",
    "declared_process_sentinel",
}


@dataclass(frozen=True)
class CheckError(Exception):
    message: str

    def __str__(self) -> str:  # pragma: no cover
        return self.message


def _require_mapping(obj: Any, *, name: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise CheckError(f"{name} must be an object")
    return obj


def _require_list(obj: Any, *, name: str) -> list[Any]:
    if not isinstance(obj, list):
        raise CheckError(f"{name} must be a list")
    return obj


def _require_str(obj: Any, *, name: str) -> str:
    if not isinstance(obj, str) or not obj.strip():
        raise CheckError(f"{name} must be a non-empty string")
    return obj.strip()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise CheckError(f"missing JSON file: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise CheckError(f"invalid JSON in {path}: {exc}") from exc
    return _require_mapping(payload, name=str(path))


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    out: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            try:
                item = json.loads(text)
            except json.JSONDecodeError as exc:
                raise CheckError(f"invalid JSONL in {path}:{line_no}: {exc}") from exc
            out.append(_require_mapping(item, name=f"{path}:{line_no}"))
    return out


def _load_manifest(path: Path) -> dict[str, dict[str, Any]]:
    root = _load_json(path)
    if root.get("schema") != MANIFEST_SCHEMA:
        raise CheckError(f"manifest schema mismatch: {root.get('schema')!r}")
    entries = _require_list(root.get("reason_classes"), name="reason_classes")
    reasons: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(entries):
        entry = _require_mapping(raw, name=f"reason_classes[{index}]")
        reason = _require_str(entry.get("reason"), name=f"reason_classes[{index}].reason")
        if reason in reasons:
            raise CheckError(f"duplicate reason class: {reason}")
        status = _require_str(entry.get("status"), name=f"{reason}.status")
        if status not in ALLOWED_STATUSES:
            raise CheckError(f"{reason}: unsupported status {status!r}")
        _require_str(entry.get("hazard"), name=f"{reason}.hazard")
        _require_str(entry.get("hardening"), name=f"{reason}.hardening")
        _require_str(entry.get("proof_target"), name=f"{reason}.proof_target")
        reasons[reason] = entry
    return reasons


def _strict_candidate_errors(item: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    candidate = item.get("candidate")
    if not isinstance(candidate, dict):
        return ["missing candidate object"]
    if float(item.get("disaster_rate", 1.0)) != 0.0:
        errors.append("disaster_rate must be zero")
    if item.get("legal_shape_ok") is not True:
        errors.append("legal_shape_ok must be true")
    if float(item.get("min_insurance_ratio", 0.0)) < 1.0:
        errors.append("min_insurance_ratio must be >= 1.0")
    if float(item.get("guard_block_rate", 1.0)) > 0.05:
        errors.append("guard_block_rate must be <= 0.05")
    if float(item.get("payout_budget_clamp_rate", 1.0)) > 0.50:
        errors.append("payout_budget_clamp_rate must be <= 0.50")
    if float(item.get("funding_clamp_rate", 1.0)) > 0.50:
        errors.append("funding_clamp_rate must be <= 0.50")
    fee_burn_share = float(candidate.get("fee_burn_share", 1.0))
    insurance_share = float(candidate.get("insurance_share", 1.0))
    if fee_burn_share + insurance_share > 0.95:
        errors.append("fee_burn_share + insurance_share must be <= 0.95")
    if float(candidate.get("payout_cap_share", 1.0)) > 0.50:
        errors.append("payout_cap_share must be <= 0.50")
    return errors


def _run_receipt(run_dir: Path, known_reasons: dict[str, dict[str, Any]]) -> dict[str, Any]:
    if not run_dir.exists() or not run_dir.is_dir():
        raise CheckError(f"run_dir missing or not a directory: {run_dir}")
    counterexamples = _read_jsonl(run_dir / "counterexamples.jsonl")
    reason_counts = Counter(_require_str(item.get("reason"), name=f"{run_dir}.counterexamples.reason") for item in counterexamples)
    unknown_reasons = sorted(reason for reason in reason_counts if reason not in known_reasons)

    promotions = _read_jsonl(run_dir / "promotion_candidates.jsonl")
    promotion_errors: list[str] = []
    for index, item in enumerate(promotions):
        item_errors = _strict_candidate_errors(item)
        if item_errors:
            candidate_id = item.get("id", f"index:{index}")
            promotion_errors.append(f"{run_dir}:promotion_candidates[{candidate_id}]: " + "; ".join(item_errors))

    reranked = _read_jsonl(run_dir / "reranked_top_candidates.jsonl")
    strict_reranked_count = sum(1 for item in reranked if not _strict_candidate_errors(item))
    summary = _load_json(run_dir / "summary.json") if (run_dir / "summary.json").exists() else {}

    return {
        "run_dir": str(run_dir),
        "summary_schema": summary.get("schema"),
        "candidate_count": summary.get("candidates"),
        "counterexample_count": len(counterexamples),
        "reason_counts": dict(sorted(reason_counts.items())),
        "unknown_reasons": unknown_reasons,
        "promotion_candidate_count": len(promotions),
        "strict_reranked_candidate_count": strict_reranked_count,
        "promotion_errors": promotion_errors,
        "ok": not unknown_reasons and not promotion_errors,
    }


def build_receipt(
    run_dirs: Sequence[str | Path],
    *,
    manifest_path: str | Path = DEFAULT_MANIFEST,
) -> dict[str, Any]:
    if not run_dirs:
        raise CheckError("at least one --run-dir is required")
    known_reasons = _load_manifest(Path(manifest_path))
    runs = [_run_receipt(Path(run_dir), known_reasons) for run_dir in run_dirs]
    unknown_reasons = sorted({reason for run in runs for reason in run["unknown_reasons"]})
    promotion_errors = [error for run in runs for error in run["promotion_errors"]]
    aggregate_counts: Counter[str] = Counter()
    for run in runs:
        aggregate_counts.update(run["reason_counts"])
    ok = not unknown_reasons and not promotion_errors
    return {
        "schema": CHECK_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "manifest_path": str(manifest_path),
        "known_reason_count": len(known_reasons),
        "run_count": len(runs),
        "counterexample_count": sum(int(run["counterexample_count"]) for run in runs),
        "aggregate_reason_counts": dict(sorted(aggregate_counts.items())),
        "unknown_reasons": unknown_reasons,
        "promotion_errors": promotion_errors,
        "runs": runs,
    }


def _print_text(receipt: dict[str, Any]) -> None:
    print("MacOS Scout Regression Gate")
    print(f"status = {receipt['status']}")
    print(f"run_count = {receipt['run_count']}")
    print(f"known_reason_count = {receipt['known_reason_count']}")
    print(f"counterexample_count = {receipt['counterexample_count']}")
    print(f"aggregate_reason_counts = {json.dumps(receipt['aggregate_reason_counts'], sort_keys=True)}")
    if receipt["unknown_reasons"]:
        print("unknown_reasons:")
        for reason in receipt["unknown_reasons"]:
            print(f"- {reason}")
    if receipt["promotion_errors"]:
        print("promotion_errors:")
        for error in receipt["promotion_errors"]:
            print(f"- {error}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check MacOS scout counterexample and promotion regressions.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--run-dir", action="append", required=True, help="Scout output directory to check; repeatable.")
    parser.add_argument("--output", help="Optional path to write JSON receipt.")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    try:
        receipt = build_receipt(args.run_dir, manifest_path=args.manifest)
    except CheckError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.format == "json":
        json.dump(receipt, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(receipt)
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
