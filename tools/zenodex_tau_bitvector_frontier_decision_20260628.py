#!/usr/bin/env python3
"""Replay the Tau bitvector host-projection frontier decision."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.zenodex_tau_bitvector_frontier_probe_20260628 import (  # noqa: E402
    build_report as build_probe_report,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_bitvector_frontier_decision_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_BITVECTOR_FRONTIER_DECISION_20260628.md"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _decision_from_probe(probe: dict[str, Any]) -> dict[str, Any]:
    rows = probe["tau_binaries"]
    summary = probe["summary"]
    all_equivalent = int(summary["equivalent_count"]) == int(summary["checked_tau_binaries"])
    direct_all_ok = int(summary["direct_ok_count"]) == int(summary["checked_tau_binaries"])
    projected_all_ok = int(summary["projected_ok_count"]) == int(summary["checked_tau_binaries"])
    direct_has_profile_variance = bool(summary["slow_or_worse_direct_labels"])
    direct_more_complete = False
    direct_faster_or_equal_all = all(
        row["direct"]["latency_class"] in {"fast", "moderate"}
        and row["projected"]["latency_class"] in {"fast", "moderate", "slow", "very_slow"}
        for row in rows
    ) and not direct_has_profile_variance

    return {
        "small_direct_bv16_island_supported": bool(
            all_equivalent
            and direct_all_ok
            and projected_all_ok
            and int(summary["invalid_accepts"]) == 0
            and bool(summary["fast_direct_labels"])
        ),
        "broad_host_projection_refuted": bool(direct_more_complete and direct_faster_or_equal_all),
        "host_projection_default_preserved": bool(
            all_equivalent
            and not direct_more_complete
            and direct_has_profile_variance
            and int(summary["invalid_accepts"]) == 0
        ),
        "profile_gate_required": direct_has_profile_variance,
        "direct_more_complete": direct_more_complete,
        "direct_faster_or_equal_all": direct_faster_or_equal_all,
        "fast_direct_labels": list(summary["fast_direct_labels"]),
        "slow_or_worse_direct_labels": list(summary["slow_or_worse_direct_labels"]),
        "checked_tau_binaries": int(summary["checked_tau_binaries"]),
        "invalid_accepts": int(summary["invalid_accepts"]),
    }


def build_report(*, timeout_s: float = 45.0) -> dict[str, Any]:
    probe = build_probe_report(timeout_s=timeout_s)
    decision = _decision_from_probe(probe)
    ok = (
        decision["small_direct_bv16_island_supported"]
        and decision["host_projection_default_preserved"]
        and not decision["broad_host_projection_refuted"]
    )
    report = {
        "schema": "zenodex.tau_bitvector_frontier_decision.v1",
        "date": "2026-06-28",
        "ok": ok,
        "probe_report": {
            "schema": probe["schema"],
            "direct_spec": probe["direct_spec"],
            "projected_spec": probe["projected_spec"],
            "summary": probe["summary"],
        },
        "decision": decision,
        "frontier_resolution": {
            "question": "Does direct Tau-only bitvector arithmetic refute the host-projection default by being more complete and faster-or-equal under the relevant profile budget?",
            "answer": "No for the broad default. Yes for a small profile-gated bv16 sequence-check island.",
            "design_rule": "Use direct Tau bitvectors only for small bounded kernels with replayed profile evidence; keep host projection as the default for broad receipt machinery.",
        },
        "non_claims": [
            "This does not prove arbitrary direct Tau bitvector arithmetic is viable.",
            "This does not make direct bitvectors a production-required receipt gate.",
            "This does not replace host-side hash, signature, membership, history, or chain-binding verifiers.",
            "This does not claim upstream-main performance is acceptable for the direct bv16 island.",
        ],
        "replay_command": "python3 tools/zenodex_tau_bitvector_frontier_decision_20260628.py",
    }
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    decision = report["decision"]
    frontier = report["frontier_resolution"]
    lines.append("# ZenoDEX Tau Bitvector Frontier Decision - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(frontier["answer"])
    lines.append(frontier["design_rule"])
    lines.append("")
    lines.append("## Decision Facts")
    lines.append("")
    for key in (
        "small_direct_bv16_island_supported",
        "broad_host_projection_refuted",
        "host_projection_default_preserved",
        "profile_gate_required",
        "checked_tau_binaries",
        "invalid_accepts",
    ):
        lines.append(f"- `{key}` = `{decision[key]}`")
    lines.append(f"- `fast_direct_labels` = `{', '.join(decision['fast_direct_labels'])}`")
    lines.append(f"- `slow_or_worse_direct_labels` = `{', '.join(decision['slow_or_worse_direct_labels'])}`")
    lines.append("")
    lines.append("## Probe Inputs")
    lines.append("")
    probe = report["probe_report"]
    lines.append(f"- Direct spec: `{probe['direct_spec']}`")
    lines.append(f"- Projected spec: `{probe['projected_spec']}`")
    lines.append(f"- Checked Tau binaries: `{probe['summary']['checked_tau_binaries']}`")
    lines.append(f"- Equivalent direct/projected runs: `{probe['summary']['equivalent_count']}`")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "decision": report["decision"],
                "report_sha256": _sha256(REPORT_JSON),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
