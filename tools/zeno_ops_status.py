#!/usr/bin/env python3
"""Emit ZenoOps status metrics as JSON or Prometheus text."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.metrics_v0 import (
    build_metrics_snapshot_v0,
    build_minimal_operator_samples_v0,
    render_prometheus_text_v0,
    samples_from_chaos_report_v0,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chaos-report", type=Path)
    parser.add_argument("--prometheus", action="store_true")
    parser.add_argument("--ledger-height", type=int, default=0)
    parser.add_argument("--peer-count", type=int, default=0)
    parser.add_argument("--gossip-rejections", type=int, default=0)
    parser.add_argument("--slashing-evidence", type=int, default=0)
    parser.add_argument("--proof-metadata-mismatches", type=int, default=0)
    parser.add_argument("--key-admission-rejections", type=int, default=0)
    args = parser.parse_args(argv)

    if args.chaos_report is not None:
        report = json.loads(args.chaos_report.read_text(encoding="utf-8"))
        samples = samples_from_chaos_report_v0(report)
        source = str(args.chaos_report)
    else:
        samples = build_minimal_operator_samples_v0(
            ledger_height=args.ledger_height,
            peer_count=args.peer_count,
            gossip_rejection_count=args.gossip_rejections,
            slashing_evidence_count=args.slashing_evidence,
            proof_metadata_mismatch_count=args.proof_metadata_mismatches,
            key_admission_rejection_count=args.key_admission_rejections,
        )
        source = "cli"

    if args.prometheus:
        print(render_prometheus_text_v0(samples), end="")
        return 0
    snapshot = build_metrics_snapshot_v0(samples=samples, source=source)
    print(json.dumps(snapshot, indent=2, sort_keys=True))
    return 0 if snapshot["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
