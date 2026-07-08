#!/usr/bin/env python3
"""Report ZenoDEX zkVM transition coverage and optional smoke timing."""

from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "docs" / "ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json"
DEFAULT_PROOF_MATRIX = ROOT / "docs" / "ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json"


def build_zk_transition_coverage_report(
    *,
    manifest_path: Path = DEFAULT_MANIFEST,
    proof_matrix_path: Path = DEFAULT_PROOF_MATRIX,
    smoke_report_path: Path | None = None,
    smoke_report_paths: Sequence[Path] | None = None,
) -> dict[str, Any]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    proof_matrix = json.loads(proof_matrix_path.read_text(encoding="utf-8"))
    spot_surface = _surface(manifest, "spot_v1_risc0_supported_transition_kernel")
    full_zk_surface = _surface(manifest, "full_zk_execution_for_all_value_moving_surfaces")

    covered_operations = _str_set(spot_surface.get("covered_operations"))
    not_covered_operations = _str_set(spot_surface.get("not_covered_operations"))
    operation_universe = sorted(covered_operations | not_covered_operations)
    covered_count = len(covered_operations)
    universe_count = len(operation_universe)
    proof_operation_coverage_pct = 100.0 if universe_count == 0 else round(100.0 * covered_count / universe_count, 2)

    supported_proof_surfaces = _ids(proof_matrix.get("supported_surfaces"))
    proof_gap_surfaces = _ids(proof_matrix.get("gap_surfaces"))
    proof_surface_total = len(supported_proof_surfaces) + len(proof_gap_surfaces)
    proof_surface_coverage_pct = (
        100.0 if proof_surface_total == 0 else round(100.0 * len(supported_proof_surfaces) / proof_surface_total, 2)
    )
    value_moving_surface_coverage = _value_moving_surface_coverage(proof_matrix)

    timing_paths: list[Path] = []
    if smoke_report_path is not None:
        timing_paths.append(smoke_report_path)
    if smoke_report_paths is not None:
        timing_paths.extend(smoke_report_paths)
    timing = _timing_report(timing_paths) if timing_paths else None
    return {
        "schema": "zenodex.zk_transition_coverage_report.v0",
        "ok": timing is None or timing["ok"],
        "proof_operation_coverage": {
            "covered_count": covered_count,
            "total_count": universe_count,
            "coverage_pct": proof_operation_coverage_pct,
            "covered_operations": sorted(covered_operations),
            "not_covered_operations": sorted(not_covered_operations),
        },
        "proof_surface_coverage": {
            "supported_count": len(supported_proof_surfaces),
            "gap_count": len(proof_gap_surfaces),
            "coverage_pct": proof_surface_coverage_pct,
            "supported_surface_ids": supported_proof_surfaces,
            "gap_surface_ids": proof_gap_surfaces,
        },
        "value_moving_surface_coverage": value_moving_surface_coverage,
        "succinct_everything_status": full_zk_surface.get("coverage_status"),
        "timing": timing,
        "interpretation": [
            "Current real zkVM coverage is scoped to the spot v1 Risc0 operation family listed in covered_operations.",
            "Full-zk value-moving readiness requires value_moving_surface_coverage.open_surface_ids to be empty.",
            "Deterministic replay remains the performance baseline for ordinary full-node validation.",
            "A smoke timing report measures local prover performance only; production latency needs repeated warm runs on target hardware.",
        ],
    }


def _surface(manifest: Mapping[str, Any], surface_id: str) -> Mapping[str, Any]:
    surfaces = manifest.get("critical_surfaces")
    if not isinstance(surfaces, list):
        raise ValueError("manifest critical_surfaces must be a list")
    for surface in surfaces:
        if isinstance(surface, Mapping) and surface.get("id") == surface_id:
            return surface
    raise ValueError(f"manifest missing surface: {surface_id}")


def _str_set(value: Any) -> set[str]:
    if not isinstance(value, list):
        return set()
    return {item for item in value if isinstance(item, str) and item}


def _ids(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    return sorted(item["id"] for item in value if isinstance(item, Mapping) and isinstance(item.get("id"), str))


def _value_moving_surface_coverage(proof_matrix: Mapping[str, Any]) -> dict[str, Any]:
    surfaces = proof_matrix.get("full_zk_value_moving_surfaces")
    if not isinstance(surfaces, list):
        return {
            "covered_count": 0,
            "total_count": 0,
            "coverage_pct": 0.0,
            "covered_surface_ids": [],
            "open_surface_ids": [],
            "open_gap_surface_ids": [],
        }
    covered_surface_ids: list[str] = []
    open_surface_ids: list[str] = []
    open_gap_surface_ids: set[str] = set()
    for surface in surfaces:
        if not isinstance(surface, Mapping):
            continue
        surface_id = surface.get("id")
        if not isinstance(surface_id, str):
            continue
        gap_ids = _str_items(surface.get("gap_surface_ids"))
        if surface.get("coverage_status") == "covered" and not gap_ids:
            covered_surface_ids.append(surface_id)
        else:
            open_surface_ids.append(surface_id)
            open_gap_surface_ids.update(gap_ids)
    total_count = len(covered_surface_ids) + len(open_surface_ids)
    coverage_pct = 100.0 if total_count == 0 else round(100.0 * len(covered_surface_ids) / total_count, 2)
    return {
        "covered_count": len(covered_surface_ids),
        "total_count": total_count,
        "coverage_pct": coverage_pct,
        "covered_surface_ids": sorted(covered_surface_ids),
        "open_surface_ids": sorted(open_surface_ids),
        "open_gap_surface_ids": sorted(open_gap_surface_ids),
    }


def _str_items(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    return sorted(item for item in value if isinstance(item, str) and item)


def _timing_report(paths: Sequence[Path]) -> dict[str, Any]:
    loaded_cases: list[tuple[Path, Mapping[str, Any]]] = []
    for path in paths:
        try:
            report = json.loads(path.read_text(encoding="utf-8"))
        except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
            return {"ok": False, "error": f"could not load smoke report: {exc}", "paths": [str(item) for item in paths]}
        cases = report.get("cases")
        if not isinstance(cases, list):
            return {"ok": False, "error": "smoke report cases must be a list", "path": str(path)}
        loaded_cases.extend((path, item) for item in cases if isinstance(item, Mapping))
    rows: list[dict[str, Any]] = []
    total_seconds: list[float] = []
    generate_seconds: list[float] = []
    verify_seconds: list[float] = []
    missing_timing: list[str] = []
    for path, raw_case in loaded_cases:
        name = str(raw_case.get("case", "unknown"))
        generated = _number(raw_case.get("generate_seconds"))
        verified = _number(raw_case.get("verify_seconds"))
        total = _number(raw_case.get("total_seconds"))
        if total is None and generated is not None and verified is not None:
            total = generated + verified
        if generated is None or verified is None or total is None:
            missing_timing.append(name)
            continue
        generate_seconds.append(generated)
        verify_seconds.append(verified)
        total_seconds.append(total)
        rows.append(
            {
                "case": name,
                "source_report": str(path),
                "runner_mode": raw_case.get("runner_mode"),
                "generate_seconds": round(generated, 3),
                "verify_seconds": round(verified, 3),
                "total_seconds": round(total, 3),
                "proof_base64_len": raw_case.get("proof_base64_len"),
            }
        )
    if missing_timing:
        return {
            "ok": False,
            "error": "smoke report is missing timing fields",
            "missing_timing_cases": sorted(missing_timing),
            "paths": [str(item) for item in paths],
        }
    return {
        "ok": True,
        "paths": [str(item) for item in paths],
        "case_count": len(rows),
        "cases": rows,
        "summary": {
            "generate_seconds_min": round(min(generate_seconds), 3) if generate_seconds else None,
            "generate_seconds_median": round(statistics.median(generate_seconds), 3) if generate_seconds else None,
            "generate_seconds_max": round(max(generate_seconds), 3) if generate_seconds else None,
            "verify_seconds_min": round(min(verify_seconds), 3) if verify_seconds else None,
            "verify_seconds_median": round(statistics.median(verify_seconds), 3) if verify_seconds else None,
            "verify_seconds_max": round(max(verify_seconds), 3) if verify_seconds else None,
            "total_seconds_min": round(min(total_seconds), 3) if total_seconds else None,
            "total_seconds_median": round(statistics.median(total_seconds), 3) if total_seconds else None,
            "total_seconds_max": round(max(total_seconds), 3) if total_seconds else None,
        },
    }


def _number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int | float):
        return float(value)
    return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--proof-matrix", type=Path, default=DEFAULT_PROOF_MATRIX)
    parser.add_argument("--smoke-report", type=Path, action="append")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = build_zk_transition_coverage_report(
        manifest_path=args.manifest,
        proof_matrix_path=args.proof_matrix,
        smoke_report_paths=args.smoke_report,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
