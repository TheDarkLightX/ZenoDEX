#!/usr/bin/env python3
"""Build the future O-008 V2 JSON and Markdown artifacts from an exact Git subject."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.global_settlement_abi_v2_o008_evidence_v2 import (
    EvidenceV2Error,
    build_evidence_v2,
    canonical_json_bytes_v2,
    render_markdown_v2,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--stage-a-commit", required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-md", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        evidence = build_evidence_v2(args.root, args.stage_a_commit)
        outputs = ((args.output_json, canonical_json_bytes_v2(evidence)), (args.output_md, render_markdown_v2(evidence).encode()))
        for path, expected in outputs:
            if args.check:
                if path.read_bytes() != expected:
                    raise EvidenceV2Error(f"generated artifact drift: {path}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(expected)
    except (EvidenceV2Error, OSError) as exc:
        print(f"O008_V2_BUILD_REJECTED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
