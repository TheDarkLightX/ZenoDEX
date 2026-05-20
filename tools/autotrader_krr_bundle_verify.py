#!/usr/bin/env python3
"""Verify a reviewed, signed offline KRR bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import (  # noqa: E402
    derive_source_quality,
    load_autotrader_krr_bundle_file,
)
from tools.krr_reasoner_engine import normalize_krr_kb_object  # noqa: E402


def _load_json(path: str | Path) -> object:
    return json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bundle-file", required=True)
    ap.add_argument("--allow-unsigned", action="store_true")
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        raw_obj = _load_json(args.bundle_file)
        if not isinstance(raw_obj, dict):
            raise ValueError("bundle file must be a JSON object")
        bundle = load_autotrader_krr_bundle_file(
            args.bundle_file,
            require_signature=not bool(args.allow_unsigned),
            require_review=True,
        )
        if bundle.runtime_krr_kb is not None:
            normalize_krr_kb_object(bundle.runtime_krr_kb, kb_path=Path(args.bundle_file))
        recomputed_quality = derive_source_quality(
            history=bundle.runtime_history,
            review_records=bundle.review_records,
        )
        derived_quality_ok = [row.to_dict() for row in recomputed_quality] == [
            row.to_dict() for row in bundle.derived_source_quality
        ]
        if not derived_quality_ok:
            raise ValueError("derived source quality rows do not match recomputed values")
        payload = {
            "schema": "zenodex/autotrader-krr-bundle-verify/v1",
            "ok": True,
            "bundle_name": bundle.bundle_name,
            "bundle_hash": bundle.bundle_hash_hex(),
            "signature_present": bundle.signature is not None,
            "review_gate_ok": bundle.runtime_approved(),
            "runtime_artifacts": {
                "krr_kb_present": bundle.runtime_krr_kb is not None,
                "external_signals_present": bundle.runtime_external_signals is not None,
                "signal_source_registry_present": bundle.runtime_signal_source_registry is not None,
                "history_present": bundle.runtime_history is not None,
            },
            "counts": {
                "source_snapshots": len(bundle.source_snapshots),
                "evidence_records": len(bundle.evidence_records),
                "canonical_claims": len(bundle.canonical_claims),
                "review_records": len(bundle.review_records),
                "derived_source_quality": len(bundle.derived_source_quality),
            },
        }
        sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/autotrader-krr-bundle-verify/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
