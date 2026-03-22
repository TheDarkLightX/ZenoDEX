#!/usr/bin/env python3
from __future__ import annotations

"""Systematic poka-yoke ROI audit (internal).

Goal
  Identify where mistake-proofing yields the highest ROI by:
  - mapping degrees of freedom (user-controllable inputs)
  - enumerating failure modes + risk signals
  - detecting existing guardrails in the UI code
  - ranking missing/weak guardrails via a lightweight FMEA score

This tool is intentionally heuristic: it produces a ranked *experiment queue*,
not proofs. Promotion requires replayable evidence (tests, formal checks, etc).
"""

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Surface:
    surface_id: str
    relpath: str
    flow: str


@dataclass(frozen=True)
class FailureMode:
    failure_id: str
    flow: str
    description: str

    # FMEA-style qualitative ratings: 1..10 (10 = worse)
    severity: int
    occurrence: int
    detectability: int

    # Engineering effort (1..5); rough, used only for ranking.
    effort: int

    # "Signal markers" are regexes whose presence suggests the *signal* exists (warning/notice).
    signal_markers: list[str]

    # "Interlock markers" are regexes whose presence suggests an existing *interlock* (block/confirm/typed confirm).
    interlock_markers: list[str]

    # Candidate pokayoke intervention (treated as an experiment).
    proposed_intervention: str
    representation_shift: str  # equiv|reduce|relax|restrict|heuristic|lift|project|decompose


UI_SURFACES: list[Surface] = [
    Surface(surface_id="swap", relpath="tools/dex-ui/src/components/SwapInterface.jsx", flow="swap"),
    Surface(surface_id="add_liquidity", relpath="tools/dex-ui/src/components/AddLiquidityModal.jsx", flow="liquidity_add"),
    Surface(surface_id="remove_liquidity", relpath="tools/dex-ui/src/components/RemoveLiquidityModal.jsx", flow="liquidity_remove"),
    Surface(surface_id="perps_order", relpath="tools/dex-ui/src/components/perps/PerpOrderForm.jsx", flow="perps_order"),
]


# A deliberately small, high-signal catalog (extend in later cycles).
FAILURE_MODES: list[FailureMode] = [
    FailureMode(
        failure_id="swap_mev_conflict_unacknowledged",
        flow="swap",
        description="User submits a swap when the bounded MEV model indicates MEV/revert conflict (revert-safe slippage is sandwich-profitable).",
        severity=9,
        occurrence=4,
        detectability=8,
        effort=2,
        signal_markers=[
            r"MEV/revert conflict",
            r"mev_conflict",
        ],
        interlock_markers=[
            # Look for explicit gating in the submit path (heuristic; refine as we standardize patterns).
            r"apiSlippageAdvice\?\.(?:pokayoke|pokayokeDecision)|apiSlippageAdvice\?\.\s*pokayoke",
            r"typed_confirm",
            r"typed\s+confirmation",
        ],
        proposed_intervention="Add an interlock: when slippage advisor status is mev_conflict, require typed confirmation (or default to block in non-advanced mode).",
        representation_shift="restrict",
    ),
    FailureMode(
        failure_id="swap_inconclusive_mev_treated_as_safe",
        flow="swap",
        description="User submits a swap when MEV risk is inconclusive under scan cap; unknown risk is not surfaced or gated.",
        severity=8,
        occurrence=3,
        detectability=9,
        effort=2,
        signal_markers=[
            r"inconclusive_mev",
            r"Treat as unknown \(fail-closed\)",
        ],
        interlock_markers=[
            r"apiSlippageAdvice\?\.(?:pokayoke|pokayokeDecision)|apiSlippageAdvice\?\.\s*pokayoke",
        ],
        proposed_intervention="Surface fail-closed semantics: require explicit confirmation when status is inconclusive_mev, and log overrides.",
        representation_shift="restrict",
    ),
    FailureMode(
        failure_id="swap_no_revert_safe_option",
        flow="swap",
        description="User submits a swap when no provided slippage option is revert-safe at the confidence bound (likely revert).",
        severity=6,
        occurrence=5,
        detectability=6,
        effort=2,
        signal_markers=[
            r"no_revert_safe_option",
            r"No provided slippage option is revert-safe",
        ],
        interlock_markers=[
            r"apiSlippageAdvice\?\.(?:pokayoke|pokayokeDecision)|apiSlippageAdvice\?\.\s*pokayoke",
            r"typed_confirm",
        ],
        proposed_intervention="Add an interlock: typed confirm (or block) when no_revert_safe_option; offer a deterministic amount-reduction suggestion.",
        representation_shift="reduce",
    ),
    FailureMode(
        failure_id="swap_high_price_impact_without_interlock",
        flow="swap",
        description="User submits a high price-impact swap without a friction gate (confirm/typed confirm).",
        severity=7,
        occurrence=5,
        detectability=3,
        effort=1,
        signal_markers=[
            r"Confirm Swap",
            r"Proceed Anyway",
            r"High price impact",
        ],
        interlock_markers=[
            r"handleSwapClick[\s\S]*priceImpact\s*>\s*0\.01",
            r"setShowConfirm\(",
        ],
        proposed_intervention="Escalate interlocks by tier: confirm at >=1% impact, typed confirm at >=5% impact (non-advanced mode).",
        representation_shift="restrict",
    ),
    FailureMode(
        failure_id="liquidity_add_imbalanced_amounts",
        flow="liquidity_add",
        description="User adds liquidity with amounts far from pool ratio, leading to suboptimal LP minting or unexpected leftovers.",
        severity=5,
        occurrence=6,
        detectability=4,
        effort=2,
        signal_markers=[
            r"imbalance",
            r"ratio",
            r"lock",
        ],
        interlock_markers=[
            r"Confirm",
            r"setShowConfirm",
        ],
        proposed_intervention="Offer deterministic 'match pool ratio' auto-fill and lock ratio by default; require confirm when deviation exceeds threshold.",
        representation_shift="restrict",
    ),
    FailureMode(
        failure_id="liquidity_remove_near_total",
        flow="liquidity_remove",
        description="User removes almost all liquidity unintentionally (positions wiped).",
        severity=6,
        occurrence=3,
        detectability=3,
        effort=1,
        signal_markers=[
            r">95%",
            r"Confirm",
            r"Remove",
        ],
        interlock_markers=[
            r">95%",
            r"showConfirm",
        ],
        proposed_intervention="Increase friction near boundaries: typed confirm at >=99% remove; keep one-click confirm at >=95%.",
        representation_shift="restrict",
    ),
]


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def _pattern_hits(text: str, patterns: list[str]) -> dict[str, int]:
    hits: dict[str, int] = {}
    for p in patterns:
        try:
            hits[p] = len(re.findall(p, text, flags=re.IGNORECASE | re.MULTILINE))
        except re.error:
            hits[p] = 0
    return hits


def _fmea_rpn(*, severity: int, occurrence: int, detectability: int) -> int:
    s = max(1, min(10, int(severity)))
    o = max(1, min(10, int(occurrence)))
    d = max(1, min(10, int(detectability)))
    return int(s * o * d)


def _roi_score(*, rpn: int, effort: int) -> float:
    e = max(1, min(5, int(effort)))
    return float(rpn) / float(e)


def _coverage_status(*, signal_present: bool, interlock_present: bool) -> str:
    if signal_present and interlock_present:
        return "covered"
    if interlock_present:
        return "partial"
    if signal_present:
        return "signal_only"
    return "uncovered"


def _now_utc_compact() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def main() -> int:
    ap = argparse.ArgumentParser(description="Systematic poka-yoke ROI audit (internal).")
    ap.add_argument("--repo-root", default=".", help="Repo root (default: .)")
    ap.add_argument(
        "--out-dir",
        default="",
        help="Output directory. Default: internal/rd/reports/pokayoke_audit_<timestamp>",
    )
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()
    if not repo_root.exists():
        raise SystemExit(f"repo root not found: {repo_root}")

    out_dir = Path(args.out_dir) if args.out_dir else repo_root / "internal" / "rd" / "reports" / f"pokayoke_audit_{_now_utc_compact()}"
    out_dir = out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    # Inventory: surfaces + hashes + marker hits.
    inventory: dict[str, Any] = {"schema": "zenodex/pokayoke_audit_inventory/v1", "created_at": _now_utc_compact(), "surfaces": []}
    surface_text_by_flow: dict[str, str] = {}
    for s in UI_SURFACES:
        p = (repo_root / s.relpath).resolve()
        text = _read_text(p) if p.exists() else ""
        surface_text_by_flow.setdefault(str(s.flow), "")
        surface_text_by_flow[str(s.flow)] += "\n" + text
        inventory["surfaces"].append(
            {
                "surface_id": s.surface_id,
                "flow": s.flow,
                "relpath": s.relpath,
                "exists": bool(p.exists()),
                "sha256": _sha256_text(text) if p.exists() else None,
                "bytes": len(text.encode("utf-8", errors="replace")),
            }
        )

    opportunities: list[dict[str, Any]] = []
    for fm in FAILURE_MODES:
        text = surface_text_by_flow.get(str(fm.flow), "")
        signal_hits = _pattern_hits(text, fm.signal_markers)
        interlock_hits = _pattern_hits(text, fm.interlock_markers)
        signal_present = any(v > 0 for v in signal_hits.values())
        interlock_present = any(v > 0 for v in interlock_hits.values())
        coverage_status = _coverage_status(
            signal_present=bool(signal_present),
            interlock_present=bool(interlock_present),
        )
        rpn = _fmea_rpn(severity=fm.severity, occurrence=fm.occurrence, detectability=fm.detectability)
        roi = _roi_score(rpn=rpn, effort=fm.effort)
        opportunities.append(
            {
                "failure_id": fm.failure_id,
                "flow": fm.flow,
                "description": fm.description,
                "severity": fm.severity,
                "occurrence": fm.occurrence,
                "detectability": fm.detectability,
                "effort": fm.effort,
                "rpn": rpn,
                "roi": roi,
                "signal_present": bool(signal_present),
                "interlock_present": bool(interlock_present),
                "coverage_status": coverage_status,
                "signal_marker_hits": signal_hits,
                "interlock_marker_hits": interlock_hits,
                "proposed_intervention": fm.proposed_intervention,
                "representation_shift": fm.representation_shift,
            }
        )

    # Rank missing/weak interlocks first (signal present but no interlock),
    # then missing signals entirely, then already-interlocked items.
    def _rank_key(row: dict[str, Any]) -> tuple[int, float, int]:
        if row["coverage_status"] == "signal_only":
            bucket = 0
        elif row["coverage_status"] == "uncovered":
            bucket = 1
        elif row["coverage_status"] == "partial":
            bucket = 2
        else:
            bucket = 3
        return (bucket, -float(row["roi"]), -int(row["rpn"]))

    opportunities.sort(key=_rank_key)

    report_json = {
        "schema": "zenodex/pokayoke_audit_report/v1",
        "created_at": _now_utc_compact(),
        "inventory": inventory,
        "opportunities": opportunities,
    }
    (out_dir / "inventory.json").write_text(json.dumps(inventory, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / "opportunities.json").write_text(json.dumps(opportunities, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / "report.json").write_text(json.dumps(report_json, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Human-readable markdown.
    lines: list[str] = []
    lines.append("# Poka-yoke ROI Audit (Internal)")
    lines.append("")
    lines.append(f"- created_at: `{report_json['created_at']}`")
    lines.append(f"- out_dir: `{out_dir}`")
    lines.append("")
    lines.append("## Top Opportunities (Signal-Only Or Uncovered)")
    lines.append("")
    for row in opportunities:
        if row["coverage_status"] not in {"signal_only", "uncovered"}:
            continue
        lines.append(
            f"- **{row['failure_id']}** (flow `{row['flow']}`) ROI={row['roi']:.1f} "
            f"RPN={row['rpn']} effort={row['effort']} coverage={row['coverage_status']}"
        )
        lines.append(f"  - {row['description']}")
        lines.append(f"  - proposed: {row['proposed_intervention']}")
        lines.append(f"  - transform: `{row['representation_shift']}`")
        lines.append(f"  - signal_present: `{row['signal_present']}`")
    if lines[-1] == "## Top Opportunities (Signal-Only Or Uncovered)":
        lines.append("- (none detected by markers; extend catalog/markers)")
    lines.append("")
    lines.append("## Existing Or Partial Guardrails Detected (By Markers)")
    lines.append("")
    for row in opportunities:
        if row["coverage_status"] not in {"covered", "partial"}:
            continue
        markers = [p for p, n in row["interlock_marker_hits"].items() if n > 0]
        lines.append(
            f"- **{row['failure_id']}** (flow `{row['flow']}`) "
            f"coverage={row['coverage_status']} interlock markers: {', '.join(markers)}"
        )
    lines.append("")
    (out_dir / "report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(str(out_dir))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
