from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.kernel.settlement_v1 import apply_fire_object_package_settlement  # noqa: E402
from src.fire.verifier.settlement_apply_artifact_v1 import (  # noqa: E402
    write_fire_settlement_apply_artifact_receipt,
)
from src.fire.verifier.settlement_apply_report_v1 import (  # noqa: E402
    FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
    build_fire_settlement_apply_report,
)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Apply a persisted FIRE settlement bundle through the verified receipt and settlement-packet path."
    )
    parser.add_argument("--bundle-dir", type=Path, required=True, help="Persisted FIRE bundle directory")
    parser.add_argument("--holder-posted", type=int, required=True, help="Holder collateral posted into settlement")
    parser.add_argument("--writer-posted", type=int, required=True, help="Writer collateral posted into settlement")
    parser.add_argument("--holder-balance", type=int, required=True, help="Holder balance before settlement apply")
    parser.add_argument("--writer-balance", type=int, required=True, help="Writer balance before settlement apply")
    parser.add_argument("--witness-final", type=int, help="Single-index witness final value for BurnBoostCall/FeeNote")
    parser.add_argument("--witness-hodl-final", type=int, help="HODL witness final value for LPLossCover")
    parser.add_argument("--witness-lpv-final", type=int, help="LP value witness final value for LPLossCover")
    parser.add_argument(
        "--output-report-file",
        type=Path,
        help="Optional path to write the JSON apply report before printing it to stdout",
    )
    parser.add_argument(
        "--output-artifact-receipt-file",
        type=Path,
        help="Optional path to write a pinned receipt for the emitted apply report; requires --output-report-file",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON apply report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    if args.output_artifact_receipt_file is not None and args.output_report_file is None:
        print("--output-artifact-receipt-file requires --output-report-file", file=sys.stderr)
        return 1
    witness_inputs: dict[str, int] = {}
    if args.witness_final is not None:
        witness_inputs["witness_final"] = args.witness_final
    if args.witness_hodl_final is not None:
        witness_inputs["witness_hodl_final"] = args.witness_hodl_final
    if args.witness_lpv_final is not None:
        witness_inputs["witness_lpv_final"] = args.witness_lpv_final

    ok, err, result = apply_fire_object_package_settlement(
        bundle_dir=args.bundle_dir,
        holder_posted=args.holder_posted,
        writer_posted=args.writer_posted,
        holder_balance=args.holder_balance,
        writer_balance=args.writer_balance,
        witness_inputs=witness_inputs,
    )
    if not ok or result is None:
        print(err or "fire settlement apply failed", file=sys.stderr)
        return 1

    report = build_fire_settlement_apply_report(
        {
            "schema": FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA,
            "ok": True,
            **result.to_dict(),
        }
    )
    rendered = (
        json.dumps(report, indent=2, sort_keys=True)
        if args.pretty
        else json.dumps(report, sort_keys=True, separators=(",", ":"))
    )
    if args.output_report_file is not None:
        args.output_report_file.parent.mkdir(parents=True, exist_ok=True)
        args.output_report_file.write_text(rendered, encoding="utf-8")
    if args.output_artifact_receipt_file is not None and args.output_report_file is not None:
        try:
            write_fire_settlement_apply_artifact_receipt(
                args.output_artifact_receipt_file,
                args.output_report_file,
                args.bundle_dir,
            )
        except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
            print(str(exc), file=sys.stderr)
            return 1
    print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
