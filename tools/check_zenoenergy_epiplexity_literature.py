#!/usr/bin/env python3
"""Check the ZenoEnergy epiplexity literature boundary note."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


REQUIRED_SOURCE_URLS = {
    "epiplexity": "https://arxiv.org/abs/2601.03220",
    "proxy_counterexample": "https://arxiv.org/abs/2605.11554",
    "thermodynamic_epiplexity": "https://arxiv.org/abs/2602.05463",
    "ebm_training": "https://arxiv.org/abs/2101.03288",
    "gcn_branching": "https://arxiv.org/abs/1906.01629",
    "graph_pointer_branching": "https://arxiv.org/abs/2307.01434",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument(
        "--note",
        type=Path,
        default=Path("docs/ZENO_ENERGY_EPIPLEXITY_LITERATURE.md"),
    )
    parser.add_argument(
        "--curriculum",
        type=Path,
        default=Path("data/upba_energy/zenoenergy_negative_curriculum_seed20260545.json"),
    )
    parser.add_argument("--output-json", type=Path)
    args = parser.parse_args()

    report = check_epiplexity_literature(
        root=args.root,
        note_path=args.note,
        curriculum_path=args.curriculum,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def check_epiplexity_literature(
    *,
    root: Path = ROOT,
    note_path: Path = Path("docs/ZENO_ENERGY_EPIPLEXITY_LITERATURE.md"),
    curriculum_path: Path = Path("data/upba_energy/zenoenergy_negative_curriculum_seed20260545.json"),
) -> dict[str, Any]:
    note = (root / note_path).read_text(encoding="utf-8")
    curriculum = json.loads((root / curriculum_path).read_text(encoding="utf-8"))
    note_lower = note.lower()
    proxy = curriculum["bounded_epiplexity_proxy"]

    checks = [
        _check(
            "sources.primary_epiplexity",
            REQUIRED_SOURCE_URLS["epiplexity"] in note
            and "submitted 2026-01-06" in note
            and "revised 2026-03-16" in note,
            "Finzi et al. epiplexity source and version dates are recorded",
        ),
        _check(
            "sources.proxy_counterexample",
            REQUIRED_SOURCE_URLS["proxy_counterexample"] in note
            and "structure proxy need not agree with OOD" in note,
            "controlled counterexample source is recorded as a task-relevance caveat",
        ),
        _check(
            "sources.companions",
            all(url in note for url in REQUIRED_SOURCE_URLS.values()),
            "all required companion sources are linked",
        ),
        _check(
            "mapping.bounded_observer",
            "observer t" in note_lower
            and "tiny ranker" in note_lower
            and "feature extractor" in note_lower
            and "bounded training loop" in note_lower,
            "ZenoEnergy observer budget is made explicit",
        ),
        _check(
            "mapping.task_relevance_gate",
            "task_metric_improves" in note
            and "mean verifier calls" in note_lower
            and "invalid accepts" in note_lower,
            "task-relevance gate requires verifier-call and safety metrics",
        ),
        _check(
            "mapping.proxy_boundary",
            "epiplexity_proxy -/-> correctness_certificate" in note
            and "epiplexity_proxy -/-> production_readiness" in note
            and "epiplexity_proxy -/-> bounded_grid_completeness" in note,
            "note forbids treating proxy as a certificate or production claim",
        ),
        _check(
            "curriculum.proxy_receipt",
            curriculum["schema"] == "zenodex/energy/negative_curriculum/v1"
            and proxy["schema"] == "zenodex/energy/bounded_epiplexity_proxy/v1"
            and proxy["classification"] == "measurable_bounded_structure"
            and float(proxy["score"]) == 0.358265
            and float(proxy["policy_separation"]) == 0.375,
            "committed curriculum proxy remains stable",
        ),
    ]

    return {
        "schema": "zenodex/energy/epiplexity_literature_receipt/v1",
        "ok": all(item["passed"] for item in checks),
        "source_count": len(REQUIRED_SOURCE_URLS),
        "required_source_urls": REQUIRED_SOURCE_URLS,
        "note": str(note_path),
        "curriculum": str(curriculum_path),
        "proxy": {
            "classification": proxy["classification"],
            "score": proxy["score"],
            "label_entropy_bits": proxy["label_entropy_bits"],
            "policy_separation": proxy["policy_separation"],
            "rare_label_headroom": proxy["rare_label_headroom"],
        },
        "decision": "use_epiplexity_for_training_data_selection_only",
        "negative_knowledge": [
            "A high epiplexity proxy is insufficient without task-relevant heldout ranking improvement.",
            "The epiplexity proxy is not a correctness certificate, production-readiness claim, or bounded-grid completeness proof.",
        ],
        "checks": checks,
        "failed_count": sum(1 for item in checks if not item["passed"]),
        "passed_count": sum(1 for item in checks if item["passed"]),
    }


def _check(check_id: str, passed: bool, detail: str) -> dict[str, object]:
    return {
        "check_id": check_id,
        "passed": bool(passed),
        "detail": detail,
    }


if __name__ == "__main__":
    sys.exit(main())
