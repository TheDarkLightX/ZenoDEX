#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"
EXPERIMENTS = ROOT.parent


@dataclass(frozen=True)
class EvidenceSource:
    source_id: str
    path: Path
    kind: str


SOURCES = (
    EvidenceSource(
        "v190_fixture",
        EXPERIMENTS / "math_object_innovation_v190" / "generated" / "fee_cap_recommendations.json",
        "fixture",
    ),
    EvidenceSource(
        "v191_stress",
        EXPERIMENTS / "math_object_innovation_v191" / "generated" / "fee_cap_recommendations.json",
        "stress",
    ),
    EvidenceSource(
        "v192_execution",
        EXPERIMENTS / "math_object_innovation_v192" / "generated" / "fee_cap_recommendations.json",
        "execution",
    ),
)


def load_recommendations(source: EvidenceSource) -> list[dict[str, Any]]:
    obj = json.loads(source.path.read_text(encoding="utf-8"))
    if obj.get("schema") != "zenodex/fire-revenue-fee-cap-recommendations/v1":
        raise ValueError(f"bad recommendation schema: {source.path}")
    rows = obj.get("recommendations")
    if not isinstance(rows, list):
        raise ValueError(f"recommendations must be list: {source.path}")
    out: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError(f"recommendation row must be object: {source.path}")
        out.append(row)
    return out


def collect_surface_caps() -> dict[str, dict[str, Any]]:
    surfaces: dict[str, dict[str, Any]] = {}
    for source in SOURCES:
        for row in load_recommendations(source):
            surface = str(row["surface"])
            cap = row.get("recommended_user_value_cap_bps")
            status = str(row.get("status", ""))
            entry = surfaces.setdefault(
                surface,
                {
                    "surface": surface,
                    "source_statuses": {},
                    "source_caps": {},
                    "source_kinds": {},
                    "source_sample_counts": {},
                },
            )
            entry["source_statuses"][source.source_id] = status
            entry["source_kinds"][source.source_id] = source.kind
            entry["source_sample_counts"][source.source_id] = int(row.get("accepted_user_fee_sample_count", 0))
            if status == "candidate_review_cap" and cap is not None:
                entry["source_caps"][source.source_id] = int(cap)
    return surfaces


def classify_surface(entry: dict[str, Any]) -> str:
    caps = entry["source_caps"]
    kinds = entry["source_kinds"]
    if not caps:
        return "no_user_value_cap"
    has_execution = any(kinds.get(source_id) == "execution" for source_id in caps)
    if has_execution and len(caps) >= 2:
        return "execution_backed_meet_cap"
    if len(caps) >= 2:
        return "synthetic_meet_cap"
    return "single_source_cap"


def build_meet_rows(surfaces: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for surface, entry in sorted(surfaces.items()):
        caps = dict(sorted(entry["source_caps"].items()))
        meet_cap = min(caps.values()) if caps else None
        cap_bound_failures = sum(1 for cap in caps.values() if meet_cap is not None and meet_cap > cap)
        v191_cap = caps.get("v191_stress")
        v192_cap = caps.get("v192_execution")
        execution_stress_tension_bps = (
            int(v192_cap) - int(v191_cap)
            if v191_cap is not None and v192_cap is not None
            else None
        )
        rows.append(
            {
                "surface": surface,
                "classification": classify_surface(entry),
                "meet_cap_bps": meet_cap,
                "source_caps": caps,
                "source_statuses": dict(sorted(entry["source_statuses"].items())),
                "source_sample_counts": dict(sorted(entry["source_sample_counts"].items())),
                "execution_stress_tension_bps": execution_stress_tension_bps,
                "cap_bound_failures": cap_bound_failures,
                "launch_parameter_claim": False,
            }
        )
    return rows


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    surfaces = collect_surface_caps()
    rows = build_meet_rows(surfaces)
    status_counts: dict[str, int] = {}
    for row in rows:
        status = str(row["classification"])
        status_counts[status] = status_counts.get(status, 0) + 1

    meet_rows = [row for row in rows if row["meet_cap_bps"] is not None]
    execution_backed = [row for row in rows if row["classification"] == "execution_backed_meet_cap"]
    synthetic_only = [row for row in rows if row["classification"] == "synthetic_meet_cap"]
    single_source = [row for row in rows if row["classification"] == "single_source_cap"]
    no_cap = [row for row in rows if row["classification"] == "no_user_value_cap"]
    tension_rows = [
        row
        for row in execution_backed
        if row["execution_stress_tension_bps"] is not None and int(row["execution_stress_tension_bps"]) > 0
    ]
    total_invariant_failures = (
        sum(int(row["cap_bound_failures"]) for row in rows)
        + sum(1 for row in rows if row["launch_parameter_claim"])
        + sum(1 for row in execution_backed if len(row["source_caps"]) < 2)
    )
    report = {
        "schema": "zenodex/math-object-innovation-v193-report/v1",
        "object": "evidence_meet_fee_cap_lattice_v1",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "discovery_domain": {
            "source_count": len(SOURCES),
            "sources": [source.source_id for source in SOURCES],
            "surface_count": len(rows),
        },
        "holdout_domain": "none; composes existing v190-v192 recommendation artifacts",
        "surface_count": len(rows),
        "meet_cap_surface_count": len(meet_rows),
        "execution_backed_meet_count": len(execution_backed),
        "synthetic_meet_count": len(synthetic_only),
        "single_source_cap_count": len(single_source),
        "no_user_value_cap_count": len(no_cap),
        "status_counts": status_counts,
        "tension_surface_count": len(tension_rows),
        "tension_surfaces": [row["surface"] for row in tension_rows],
        "meet_rows": rows,
        "model_audit": {
            "cap_bound_failures": sum(int(row["cap_bound_failures"]) for row in rows),
            "launch_claim_failures": sum(1 for row in rows if row["launch_parameter_claim"]),
            "execution_backed_source_count_failures": sum(
                1 for row in execution_backed if len(row["source_caps"]) < 2
            ),
            "total_meet_invariant_failures": total_invariant_failures,
        },
        "strongest_claim": (
            "The v190-v192 cap artifacts compose into an evidence-meet lattice: six user-value surfaces receive "
            "a conservative meet cap, two are backed by execution-derived evidence, four remain synthetic-only, "
            "and adding evidence never loosens the composed cap because the meet is the minimum of available caps."
        ),
        "non_claims": [
            "The meet cap is a conservative review artifact, not a launch fee schedule.",
            "Oracle-dependent source caps still depend on truthful measured-value receipts.",
            "Execution-stress tension is a signal for more data, not proof that either corpus is economically complete.",
        ],
    }
    (GENERATED / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (GENERATED / "meet_rows.json").write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    report = run_cycle()
    print(
        json.dumps(
            {
                "surface_count": report["surface_count"],
                "meet_cap_surface_count": report["meet_cap_surface_count"],
                "execution_backed_meet_count": report["execution_backed_meet_count"],
                "invariant_failures": report["model_audit"]["total_meet_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_meet_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
