from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.verifier.esso_kernels_v1 import (  # noqa: E402
    default_fire_esso_kernel_models,
    verify_fire_esso_kernels,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Maintainer-only fail-closed ESSO verification gate for the admitted FIRE kernels."
    )
    parser.add_argument(
        "--model",
        action="append",
        default=[],
        help="Optional model path override; may be repeated. Defaults to the admitted FIRE ESSO kernels.",
    )
    parser.add_argument("--solvers", default="z3,cvc5", help="Comma-separated solver list for ESSO verify-multi")
    parser.add_argument("--determinism-trials", type=int, default=2, help="ESSO determinism trial count")
    parser.add_argument("--timeout-ms", type=int, default=5000, help="ESSO solver timeout in milliseconds")
    parser.add_argument("--output-dir", type=Path, help="Optional directory to write per-model ESSO JSON artifacts")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    model_paths = tuple(args.model) if args.model else default_fire_esso_kernel_models()
    if args.output_dir is not None:
        args.output_dir.mkdir(parents=True, exist_ok=True)
    ok, err, payload = verify_fire_esso_kernels(
        model_paths=model_paths,
        solvers=args.solvers,
        determinism_trials=args.determinism_trials,
        timeout_ms=args.timeout_ms,
        output_dir=args.output_dir,
    )
    if args.output_dir is not None:
        summary_path = args.output_dir / "report.json"
        summary_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
        payload = {
            **payload,
            "output_dir": str(args.output_dir.resolve()),
            "report_path": str(summary_path.resolve()),
        }
    rendered = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True)
    if ok:
        sys.stdout.write(rendered + "\n")
        return 0
    payload = {
        **payload,
        "error": err or "fire_esso_kernel_check_failed",
    }
    sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
