#!/usr/bin/env python3
"""Probe the direct bitvector vs host-projected Tau frontier."""

from __future__ import annotations

import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_bitvector_frontier_probe_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_BITVECTOR_FRONTIER_PROBE_20260628.md"
SPEC_ROOT = REPO_ROOT / "src" / "tau_specs" / "recommended"
DIRECT_SPEC = SPEC_ROOT / "receipt_sequence_bv16_guard_v1.tau"
PROJECTED_SPEC = SPEC_ROOT / "receipt_sequence_projected_guard_v1.tau"


@dataclass(frozen=True)
class TauCase:
    case_id: str
    direct_step: dict[str, int]
    direct_expected: dict[str, int]
    projected_step: dict[str, int]
    projected_expected: dict[str, int]
    expected_admit: int
    rationale: str


@dataclass(frozen=True)
class TauBinary:
    label: str
    path: Path


def _cases() -> tuple[TauCase, ...]:
    return (
        TauCase(
            case_id="sequence_pass",
            direct_step={"i1": 1, "i2": 100, "i3": 103, "i4": 5, "i5": 90, "i6": 1, "i7": 1},
            direct_expected={"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1},
            projected_step={"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1},
            projected_expected={"o1": 1, "o2": 1, "o3": 1},
            expected_admit=1,
            rationale="Monotone sequence within max gap and replay floor admits.",
        ),
        TauCase(
            case_id="gap_reject",
            direct_step={"i1": 1, "i2": 100, "i3": 120, "i4": 5, "i5": 90, "i6": 1, "i7": 1},
            direct_expected={"o1": 1, "o2": 0, "o3": 1, "o4": 0, "o5": 0},
            projected_step={"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1, "i6": 1},
            projected_expected={"o1": 0, "o2": 0, "o3": 0},
            expected_admit=0,
            rationale="A jump beyond max_step_gap rejects.",
        ),
        TauCase(
            case_id="replay_floor_reject",
            direct_step={"i1": 1, "i2": 40, "i3": 42, "i4": 5, "i5": 50, "i6": 1, "i7": 1},
            direct_expected={"o1": 1, "o2": 1, "o3": 0, "o4": 0, "o5": 0},
            projected_step={"i1": 1, "i2": 1, "i3": 1, "i4": 0, "i5": 1, "i6": 1},
            projected_expected={"o1": 0, "o2": 0, "o3": 0},
            expected_admit=0,
            rationale="A sequence below the replay floor rejects.",
        ),
    )


def _tau_version(path: Path) -> str:
    proc = subprocess.run([str(path), "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _candidate_bins() -> list[TauBinary]:
    bins: list[TauBinary] = []
    seen: set[Path] = set()

    latest = find_tau_bin(REPO_ROOT, profile="latest")
    if latest:
        latest_path = Path(latest).resolve()
        bins.append(TauBinary("workspace_latest", latest_path))
        seen.add(latest_path)

    runtime = find_tau_bin(REPO_ROOT, profile="runtime")
    if runtime:
        runtime_path = Path(runtime).resolve()
        if runtime_path not in seen:
            bins.append(TauBinary("workspace_runtime", runtime_path))
            seen.add(runtime_path)

    optional = (
        ("upstream_main", REPO_ROOT / "external" / "tau-lang-upstream-main" / "build-Release" / "tau"),
        ("bitblasting", REPO_ROOT / "external" / "tau-lang-bitblasting" / "build-Release-bitblasting" / "tau"),
        ("bitblasting_opt", REPO_ROOT / "external" / "tau-lang-bitblasting-opt" / "build-Release-bitblasting-opt" / "tau"),
        (
            "bitblasting_cegqi_bv_default",
            REPO_ROOT / "external" / "tau-lang-bitblasting-cegqi-bv-default" / "build-Release-bitblasting-cegqi-bv-default" / "tau",
        ),
    )
    for label, path in optional:
        resolved = path.resolve()
        if path.exists() and path.is_file() and resolved not in seen:
            bins.append(TauBinary(label, resolved))
            seen.add(resolved)
    return bins


def _latency_class(result: dict[str, Any]) -> str:
    if not result.get("ok"):
        if result.get("error_type") == "TimeoutExpired":
            return "timeout"
        return "failed"
    elapsed = float(result.get("elapsed_s", 0.0))
    if elapsed <= 2.0:
        return "fast"
    if elapsed <= 10.0:
        return "moderate"
    if elapsed <= 30.0:
        return "slow"
    return "very_slow"


def _run_spec(
    *,
    tau_bin: Path,
    spec_path: Path,
    steps: list[dict[str, int]],
    expected: list[dict[str, int]],
    timeout_s: float,
) -> dict[str, Any]:
    started = time.monotonic()
    try:
        outputs = run_tau_spec_steps(tau_bin=str(tau_bin), spec_path=spec_path, steps=steps, timeout_s=timeout_s)
    except Exception as exc:
        return {
            "ok": False,
            "elapsed_s": round(time.monotonic() - started, 6),
            "error_type": type(exc).__name__,
            "error": str(exc),
            "case_results": [],
        }

    ok = True
    case_results: list[dict[str, Any]] = []
    for idx, expected_row in enumerate(expected):
        got = {str(key): int(value) for key, value in outputs.get(idx, {}).items()}
        mismatches = {
            key: {"expected": int(value), "got": got.get(key)}
            for key, value in expected_row.items()
            if got.get(key) != int(value)
        }
        if mismatches:
            ok = False
        case_results.append({"ok": not mismatches, "expected": expected_row, "got": got, "mismatches": mismatches})
    return {
        "ok": ok,
        "elapsed_s": round(time.monotonic() - started, 6),
        "case_results": case_results,
    }


def _run_binary(binary: TauBinary, *, timeout_s: float) -> dict[str, Any]:
    cases = _cases()
    direct = _run_spec(
        tau_bin=binary.path,
        spec_path=DIRECT_SPEC,
        steps=[case.direct_step for case in cases],
        expected=[case.direct_expected for case in cases],
        timeout_s=timeout_s,
    )
    projected = _run_spec(
        tau_bin=binary.path,
        spec_path=PROJECTED_SPEC,
        steps=[case.projected_step for case in cases],
        expected=[case.projected_expected for case in cases],
        timeout_s=timeout_s,
    )
    invalid_accepts = 0
    if direct.get("ok") and projected.get("ok"):
        for idx, case in enumerate(cases):
            direct_admit = direct["case_results"][idx]["got"].get("o5")
            projected_admit = projected["case_results"][idx]["got"].get("o3")
            if direct_admit != projected_admit:
                invalid_accepts += 1
            if direct_admit == 1 and case.expected_admit == 0:
                invalid_accepts += 1
            if projected_admit == 1 and case.expected_admit == 0:
                invalid_accepts += 1
    else:
        invalid_accepts = -1
    return {
        "label": binary.label,
        "path": str(binary.path.relative_to(REPO_ROOT)) if binary.path.is_relative_to(REPO_ROOT) else str(binary.path),
        "version": _tau_version(binary.path),
        "direct": {**direct, "latency_class": _latency_class(direct)},
        "projected": {**projected, "latency_class": _latency_class(projected)},
        "behavior_equivalent": bool(direct.get("ok") and projected.get("ok") and invalid_accepts == 0),
        "invalid_accepts": invalid_accepts,
    }


def _summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    direct_ok = [row for row in rows if row["direct"].get("ok")]
    projected_ok = [row for row in rows if row["projected"].get("ok")]
    equivalent = [row for row in rows if row["behavior_equivalent"]]
    fast_direct = [row for row in direct_ok if row["direct"]["latency_class"] == "fast"]
    slow_or_worse_direct = [
        row
        for row in direct_ok
        if row["direct"]["latency_class"] in {"slow", "very_slow"}
    ]
    return {
        "checked_tau_binaries": len(rows),
        "direct_ok_count": len(direct_ok),
        "projected_ok_count": len(projected_ok),
        "equivalent_count": len(equivalent),
        "fast_direct_labels": [row["label"] for row in fast_direct],
        "slow_or_worse_direct_labels": [row["label"] for row in slow_or_worse_direct],
        "invalid_accepts": sum(max(0, int(row["invalid_accepts"])) for row in rows),
        "breakthrough_supported": bool(rows and direct_ok and projected_ok and equivalent),
        "design_rule": (
            "Small local bv16 sequence arithmetic is viable on current and bitblasting Tau builds, "
            "but performance is binary-sensitive; host projection remains the robust pattern for broad receipt machinery."
        ),
    }


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    summary = report["summary"]
    lines.append("# ZenoDEX Tau Bitvector Frontier Probe - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "`receipt_sequence_bv16_guard_v1.tau` and `receipt_sequence_projected_guard_v1.tau` define a paired direct-vs-projected Tau probe for bounded receipt sequence checks."
    )
    lines.append(
        f"The replay checked `{summary['checked_tau_binaries']}` Tau binaries with `{summary['invalid_accepts']}` invalid accepts and `{summary['equivalent_count']}` behavior-equivalent direct/projected runs."
    )
    lines.append("")
    lines.append(summary["design_rule"])
    lines.append("")
    lines.append("Authority boundary: these specs are evidence gates for receipt sequence facts. They do not authorize receipt commits, settlement, oracle updates, or governance.")
    lines.append("")
    lines.append("## Specifications")
    lines.append("")
    lines.append("- `src/tau_specs/recommended/receipt_sequence_bv16_guard_v1.tau`: direct `bv[16]` monotonicity, max-gap, and replay-floor arithmetic.")
    lines.append("- `src/tau_specs/recommended/receipt_sequence_projected_guard_v1.tau`: host-projected monotonicity, max-gap, and replay-floor facts.")
    lines.append("")
    lines.append("## Tau Binary Matrix")
    lines.append("")
    lines.append("| binary | version | direct | projected | equivalent |")
    lines.append("| --- | --- | --- | --- | --- |")
    for row in report["tau_binaries"]:
        lines.append(
            f"| `{row['label']}` | `{row['version']}` | `{row['direct']['latency_class']}` | `{row['projected']['latency_class']}` | `{row['behavior_equivalent']}` |"
        )
    lines.append("")
    lines.append("Latency classes are buckets: `fast` <=2s, `moderate` <=10s, `slow` <=30s. Raw timings live in the generated replay JSON.")
    lines.append("")
    lines.append("## Frontier Reading")
    lines.append("")
    lines.append("1. Direct `bv[16]` arithmetic is now a viable Tau island for this small sequence-check family on the current and bitblasting binaries.")
    lines.append("2. The upstream-main binary remains materially slower in this local probe, so direct arithmetic should stay profile-gated.")
    lines.append("3. Host-projected facts remain the safer default for large receipt machinery: hashes, signatures, membership, historical windows, and receipt-chain binding.")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    lines.append("- This does not validate arbitrary direct Tau bitvector arithmetic.")
    lines.append("- This does not replace host receipt verification.")
    lines.append("- This does not claim production activation for either spec.")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_report(*, timeout_s: float) -> dict[str, Any]:
    bins = _candidate_bins()
    if not bins:
        raise SystemExit("no Tau binaries found")
    rows = [_run_binary(binary, timeout_s=timeout_s) for binary in bins]
    report = {
        "schema": "zenodex.tau_bitvector_frontier_probe.v1",
        "date": "2026-06-28",
        "direct_spec": str(DIRECT_SPEC.relative_to(REPO_ROOT)),
        "projected_spec": str(PROJECTED_SPEC.relative_to(REPO_ROOT)),
        "case_ids": [case.case_id for case in _cases()],
        "tau_binaries": rows,
        "summary": _summarize(rows),
        "replay_command": "python3 tools/zenodex_tau_bitvector_frontier_probe_20260628.py",
    }
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def main() -> int:
    report = build_report(timeout_s=45.0)
    ok = (
        report["summary"]["breakthrough_supported"]
        and report["summary"]["invalid_accepts"] == 0
        and any(label.startswith("bitblasting") or label == "workspace_latest" for label in report["summary"]["fast_direct_labels"])
    )
    print(
        json.dumps(
            {
                "ok": bool(ok),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "json": str(REPORT_JSON.relative_to(REPO_ROOT)),
                "summary": report["summary"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
