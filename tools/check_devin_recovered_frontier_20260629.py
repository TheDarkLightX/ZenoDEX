#!/usr/bin/env python3
"""Build a deterministic inventory from recovered Devin ZenoDEX session logs.

The logs stay local.  The generated report stores only filenames, hashes,
bounded signal counts, and current repo artifact status.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEVIN_EVENTS = Path.home() / ".config" / "Devin" / "User" / "acp-events"
OUT_DIR = ROOT / "generated" / "zenodex_devin_recovered_frontier_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = ROOT / "docs" / "research" / "ZENODEX_DEVIN_RECOVERED_FRONTIER_20260629.md"

LOG_FILES = [
    "d21e2326-b832-4531-8cd9-9454d926c6c7.ndjson",
    "99dd7182-753c-4b7d-b37f-d17c590c5ec3.ndjson",
    "b328da3f-5847-4024-9e2e-8e0e8b401dff.ndjson",
    "5adee746-7a25-4789-85b7-5e6ebf551511.ndjson",
    "6dd67f0d-6ba3-4bb3-9aa8-5673c256d765.ndjson",
]

SIGNALS = {
    "discrete_argmax_proximity": re.compile(
        r"discrete argmax|ArgmaxProximity|floor rounding|false discrete concavity",
        re.IGNORECASE,
    ),
    "kpool_argmax_proximity": re.compile(
        r"KPoolDiscreteArgmax|k[- ]pool.*argmax|k-pool.*floor",
        re.IGNORECASE,
    ),
    "tauspec_ebrm_frontier": re.compile(
        r"TauSpecEBRM|compounding frontier|frontier selector|frontier window",
        re.IGNORECASE,
    ),
    "concavity_min_out_cap": re.compile(
        r"min_out|no-gain|collusion|Nash|concavity conservation",
        re.IGNORECASE,
    ),
    "nc_bipartite_matching": re.compile(
        r"bipartite matching is in NC|maximum weight perfect matching|non-commutative rank",
        re.IGNORECASE,
    ),
    "spectral_commutative_candidate": re.compile(
        r"Spectral Liquidity|Commutative Consensus",
        re.IGNORECASE,
    ),
}

CANDIDATES = [
    {
        "id": "discrete_argmax_proximity",
        "abstraction_move": "R4 encode/compress plus C2 strengthen",
        "invariant": "floor-rounded split value is within an epsilon band of the continuous optimum",
        "status": "materialized",
        "artifacts": [
            "lean-mathlib/Proofs/DiscreteArgmaxProximity.lean",
            "tests/formal/test_lean_discrete_argmax_proximity.py",
            "tests/research/test_discrete_argmax_proximity.py",
            "docs/research/DISCRETE_ARGMAX_PROXIMITY_BREAKTHROUGH.md",
        ],
        "value": "Replaces the false discrete-concavity target with a provable argmax-proximity theorem.",
    },
    {
        "id": "kpool_argmax_proximity",
        "abstraction_move": "D4 invariant-driven generalization",
        "invariant": "floor error scales with pool count k under the abstract proximity theorem",
        "status": "materialized",
        "artifacts": [
            "lean-mathlib/Proofs/KPoolDiscreteArgmaxProximity.lean",
            "tests/formal/test_lean_kpool_discrete_argmax_proximity.py",
            "docs/research/k_pool_discrete_argmax_proximity_test.py",
        ],
        "value": "Lifts the 2-pool proximity shape into a K-pool proof obligation.",
    },
    {
        "id": "tauspec_ebrm_frontier",
        "abstraction_move": "R4 frontier compression plus C5 shadow-price ranking",
        "invariant": "advisory selector cannot authorize settlement or state mutation",
        "status": "materialized",
        "artifacts": [
            "src/tau_specs/recommended/tauspec_ebrm_compounding_frontier_certificate_v1.tau",
            "tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py",
            "tests/tau/test_zenodex_tauspec_ebrm_compounding_frontier_20260628.py",
            "docs/research/ZENODEX_TAUSPEC_EBRM_COMPOUNDING_FRONTIER_20260628.md",
        ],
        "value": "Keeps high-value Tau specification candidates visible in a bounded, replayable selector.",
    },
    {
        "id": "concavity_min_out_cap",
        "abstraction_move": "C2 strengthen mechanism constraint",
        "invariant": "filled users have no profitable lower-min-out deviation in the fixed-order model",
        "status": "materialized_research_only",
        "artifacts": [
            "docs/research/nash_equilibrium_min_out_cap_test.py",
            "docs/research/concavity_conservation_law_test.py",
            "lean-mathlib/Proofs/ConcavityConservationLaw.lean",
        ],
        "value": "Turns collusion mitigation into bounded no-gain and curvature-bound checks.",
    },
    {
        "id": "nc_bipartite_matching_for_cow",
        "abstraction_move": "R2 graphify plus R5 algebraic basis",
        "invariant": "unverified hypothesis; pairwise CoW settlement may reduce to max-weight bipartite matching",
        "status": "open_candidate_from_logs",
        "artifacts": [],
        "value": "Potential path from Hungarian-style exact matching to parallel matching certificates.",
    },
    {
        "id": "spectral_liquidity_commutative_consensus",
        "abstraction_move": "R5 spectral/change-basis",
        "invariant": "unverified; session title only in recovered logs",
        "status": "open_candidate_from_logs",
        "artifacts": [],
        "value": "Needs reconstruction before it can be treated as a research claim.",
    },
]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _line_count(path: Path) -> int:
    with path.open("rb") as fh:
        return sum(1 for _ in fh)


def _pattern_count(path: Path, pattern: re.Pattern[str]) -> int:
    count = 0
    with path.open("r", encoding="utf-8", errors="ignore") as fh:
        for line in fh:
            if pattern.search(line):
                count += 1
    return count


def _git_status(path: str) -> str:
    proc = subprocess.run(
        ["git", "status", "--short", "--", path],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    text = proc.stdout.strip()
    return "tracked_or_clean" if text == "" else text


def _candidate_status(candidate: dict[str, Any]) -> dict[str, Any]:
    artifacts = []
    for item in candidate["artifacts"]:
        path = ROOT / item
        artifacts.append(
            {
                "path": item,
                "exists": path.exists(),
                "sha256": _sha256(path) if path.exists() and path.is_file() else None,
                "git_status": _git_status(item) if path.exists() else "missing",
            }
        )
    # Empty artifact lists identify open candidates, not completed evidence bundles.
    all_present = len(artifacts) > 0 and all(artifact["exists"] for artifact in artifacts)
    return {
        **candidate,
        "artifact_count": len(artifacts),
        "all_artifacts_present": all_present,
        "artifacts": artifacts,
    }


def build_report() -> dict[str, Any]:
    logs = []
    total_signal_counts = {name: 0 for name in SIGNALS}
    for name in LOG_FILES:
        path = DEVIN_EVENTS / name
        exists = path.exists()
        signal_counts = {}
        if exists:
            for signal_name, pattern in SIGNALS.items():
                signal_counts[signal_name] = _pattern_count(path, pattern)
                total_signal_counts[signal_name] += signal_counts[signal_name]
        logs.append(
            {
                "filename": name,
                "exists": exists,
                "line_count": _line_count(path) if exists else 0,
                "sha256": _sha256(path) if exists else None,
                "signal_counts": signal_counts,
            }
        )

    candidates = [_candidate_status(candidate) for candidate in CANDIDATES]
    materialized = [
        c["id"]
        for c in candidates
        if c["status"].startswith("materialized") and c["all_artifacts_present"]
    ]
    open_candidates = [c["id"] for c in candidates if c["status"].startswith("open_")]
    ok = all(log["exists"] for log in logs) and len(materialized) >= 4

    return {
        "schema": "zenodex.devin_recovered_frontier_inventory.v1",
        "date": "2026-06-29",
        "ok": ok,
        "source_scope": "local Devin ACP event logs, summarized by filename and hash only",
        "signal_counts": total_signal_counts,
        "logs": logs,
        "candidates": candidates,
        "summary": {
            "log_count": len(logs),
            "logs_present": sum(1 for log in logs if log["exists"]),
            "materialized_candidate_count": len(materialized),
            "materialized_candidates": materialized,
            "open_candidates": open_candidates,
            "highest_value_next": "nc_bipartite_matching_for_cow",
        },
        "non_claims": [
            "The inventory does not treat Devin log text as proof.",
            "Open candidates require fresh replayable artifacts before promotion.",
            "Model-selector metadata is recorded only as source context, not as research evidence.",
            "No settlement, state-root, governance, production, routing, matching, or pool-mutation authority is derived.",
        ],
        "replay_command": "python3 tools/check_devin_recovered_frontier_20260629.py",
    }


def write_report(report: dict[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines = [
        "# ZenoDEX Devin Recovered Frontier Inventory - 2026-06-29",
        "",
        "## Executive Result",
        "",
        "A bounded inventory of recovered Devin ACP event logs maps prior ZenoDEX research sessions to current repo artifacts and open candidate directions.",
        "",
        f"- Logs present: `{report['summary']['logs_present']}` / `{report['summary']['log_count']}`",
        f"- Materialized candidates: `{report['summary']['materialized_candidate_count']}`",
        f"- Highest-value next open candidate: `{report['summary']['highest_value_next']}`",
        "",
        "## Signal Counts",
        "",
    ]
    for key, value in report["signal_counts"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Candidates", ""])
    for candidate in report["candidates"]:
        lines.extend(
            [
                f"### `{candidate['id']}`",
                "",
                f"- Status: `{candidate['status']}`",
                f"- Abstraction move: `{candidate['abstraction_move']}`",
                f"- Invariant: {candidate['invariant']}",
                f"- Value: {candidate['value']}",
                f"- All artifacts present: `{candidate['all_artifacts_present']}`",
                "",
            ]
        )

    lines.extend(["## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", report["replay_command"], "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    write_report(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "json": str(REPORT_JSON.relative_to(ROOT)),
                "report": str(REPORT_MD.relative_to(ROOT)),
                "logs_present": report["summary"]["logs_present"],
                "materialized_candidate_count": report["summary"]["materialized_candidate_count"],
                "highest_value_next": report["summary"]["highest_value_next"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
