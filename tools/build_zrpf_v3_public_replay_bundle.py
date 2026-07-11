#!/usr/bin/env python3
"""Build the source-frozen ZRPF V3 public artifact replay bundle."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if __name__ == "__main__" and not sys.flags.isolated:
    os.execv(
        sys.executable,
        [sys.executable, "-I", str(Path(__file__).resolve()), *sys.argv[1:]],
    )
sys.path.insert(0, str(ROOT))

from src.integration import zrpf_public_replay_bundle as replay  # noqa: E402

if Path(replay.__file__).resolve() != ROOT / "src/integration/zrpf_public_replay_bundle.py":
    raise RuntimeError("public replay implementation import escaped the repository root")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof-source-closure", type=Path, required=True)
    parser.add_argument("--verifier-source-closure", type=Path, required=True)
    parser.add_argument("--verifier-binary", type=Path, required=True)
    parser.add_argument("--proof-target-root", type=Path, required=True)
    parser.add_argument("--verifier-target-root", type=Path, required=True)
    parser.add_argument("--evidence-root", type=Path, required=True)
    parser.add_argument("--source-proof-root", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--reference-out", type=Path, required=True)
    parser.add_argument("--evidence-date", required=True)
    args = parser.parse_args()
    try:
        report = replay.build_bundle(
            repository_root=ROOT,
            verifier_binary_path=args.verifier_binary,
            proof_source_closure_path=args.proof_source_closure,
            verifier_source_closure_path=args.verifier_source_closure,
            proof_target_root=args.proof_target_root,
            verifier_target_root=args.verifier_target_root,
            evidence_root=args.evidence_root,
            source_proof_root=args.source_proof_root,
            output_directory=args.out_dir,
            reference_output=args.reference_out,
            evidence_date=args.evidence_date,
        )
    except (OSError, replay.PublicReplayError, ValueError) as exc:
        print(
            json.dumps(
                {
                    "errors": [str(exc)],
                    "ok": False,
                    "schema": replay.BUNDLE_SCHEMA,
                    "status": "rejected",
                },
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 1
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
