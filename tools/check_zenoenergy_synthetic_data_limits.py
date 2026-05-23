#!/usr/bin/env python3
"""Check the ZenoEnergy synthetic-data limits note."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


REQUIRED_SOURCE_URLS = {
    "curse_of_recursion": "https://arxiv.org/abs/2305.17493",
    "nature_model_collapse": "https://www.nature.com/articles/s41586-024-07566-y",
    "go_mad": "https://arxiv.org/abs/2307.01850",
    "statistical_collapse": "https://arxiv.org/abs/2404.05090",
    "accumulation": "https://arxiv.org/abs/2404.01413",
    "domain_randomization": "https://arxiv.org/abs/1703.06907",
    "ml_for_co": "https://arxiv.org/abs/1811.06128",
    "ebm_training": "https://arxiv.org/abs/2101.03288",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument(
        "--note",
        type=Path,
        default=Path("docs/ZENO_ENERGY_SYNTHETIC_DATA_LIMITS.md"),
    )
    parser.add_argument("--output-json", type=Path)
    args = parser.parse_args()

    report = check_synthetic_data_limits(root=args.root, note_path=args.note)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def check_synthetic_data_limits(
    *,
    root: Path = ROOT,
    note_path: Path = Path("docs/ZENO_ENERGY_SYNTHETIC_DATA_LIMITS.md"),
) -> dict[str, Any]:
    note = (root / note_path).read_text(encoding="utf-8")
    note_lower = note.lower()
    checks = [
        _check(
            "sources.model_collapse",
            all(
                REQUIRED_SOURCE_URLS[key] in note
                for key in (
                    "curse_of_recursion",
                    "nature_model_collapse",
                    "go_mad",
                    "statistical_collapse",
                    "accumulation",
                )
            ),
            "model-collapse and accumulation sources are linked",
        ),
        _check(
            "sources.transfer_and_solver_guidance",
            REQUIRED_SOURCE_URLS["domain_randomization"] in note
            and REQUIRED_SOURCE_URLS["ml_for_co"] in note
            and REQUIRED_SOURCE_URLS["ebm_training"] in note,
            "simulation-transfer, learned-optimization, and EBM training sources are linked",
        ),
        _check(
            "boundary.verifier_labels",
            "labels come from the" in note_lower
            and "verifier" in note_lower
            and "policy gate" in note_lower
            and "model outputs as authoritative labels" in note_lower,
            "note requires deterministic labels instead of model self-labels",
        ),
        _check(
            "boundary.no_real_replay_replacement",
            "do not replace real replay" in note_lower
            and "real_upba_replay_report_ok" in note
            and "coverage_profile_ok" in note,
            "note blocks replacing real replay with synthetic evidence",
        ),
        _check(
            "coverage.tail_families",
            "near-tie valid candidates" in note_lower
            and "output-mismatch" in note_lower
            and "suffix-bound adversaries" in note_lower
            and "rare-tail coverage" in note_lower,
            "note requires explicit rare-tail and adversarial-family coverage",
        ),
        _check(
            "gate.research_vs_production",
            "SyntheticResearchSupported :=" in note
            and "ProductionPromotionAllowed :=" in note
            and "does not satisfy" in note_lower
            and "real-replay" in note_lower
            and "production promotion gate" in note_lower,
            "research and production gates are separated",
        ),
    ]
    return {
        "schema": "zenodex/energy/synthetic_data_limits_receipt/v1",
        "ok": all(item["passed"] for item in checks),
        "passed_count": sum(1 for item in checks if item["passed"]),
        "failed_count": sum(1 for item in checks if not item["passed"]),
        "source_count": len(REQUIRED_SOURCE_URLS),
        "required_source_urls": REQUIRED_SOURCE_URLS,
        "decision": "synthetic_data_research_only_until_real_replay_gate",
        "checks": checks,
        "negative_knowledge": [
            "Synthetic verifier-labeled data can improve advisory ranking, but it is not production distribution evidence by itself.",
            "Recursive synthetic replacement and self-consuming model loops can lose tails or diversity.",
            "Real replay, source manifests, secret scans, and coverage profiles remain required for production-adjacent promotion.",
        ],
    }


def _check(check_id: str, passed: bool, detail: str) -> dict[str, Any]:
    return {"check_id": check_id, "passed": bool(passed), "detail": detail}


if __name__ == "__main__":
    sys.exit(main())
