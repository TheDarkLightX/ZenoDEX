#!/usr/bin/env python3
"""Build a reviewed, signed offline KRR bundle for autotrader runtime use."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import (  # noqa: E402
    AUTOTRADER_KRR_BUNDLE_SCHEMA,
    AutoTraderKRRBundle,
    build_autotrader_krr_bundle,
    krr_canonical_claim_from_dict,
    krr_evidence_record_from_dict,
    krr_review_record_from_dict,
    krr_source_snapshot_from_dict,
    sign_autotrader_krr_bundle,
    verify_autotrader_krr_bundle_signature,
)


def _iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _load_json(path: str | Path) -> Any:
    return json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bundle-name", required=True)
    ap.add_argument("--built-at", help="Optional build timestamp (defaults to now)")
    ap.add_argument("--compiler-version", default="autotrader_krr_bundle_build_v1")
    ap.add_argument("--policy-version", default="krr_import_policy_v1")
    ap.add_argument("--krr-kb")
    ap.add_argument("--external-signals-file")
    ap.add_argument("--signal-source-registry-file")
    ap.add_argument("--history-file")
    ap.add_argument("--source-snapshot-file", action="append", default=[])
    ap.add_argument("--evidence-record-file", action="append", default=[])
    ap.add_argument("--claim-file", action="append", default=[])
    ap.add_argument("--review-record-file", action="append", default=[])
    ap.add_argument("--parent-bundle-file")
    ap.add_argument("--signer-privkey", required=True)
    ap.add_argument("--bundle-out", required=True)
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def _load_optional_mapping(path: str | None, *, name: str) -> Mapping[str, Any] | None:
    if path is None:
        return None
    obj = _load_json(path)
    if not isinstance(obj, Mapping):
        raise ValueError(f"{name} must be a JSON object")
    return obj


def _load_rows(paths: list[str], *, loader, name: str) -> tuple[Any, ...]:
    rows = []
    for raw_path in paths:
        obj = _load_json(raw_path)
        if not isinstance(obj, Mapping):
            raise ValueError(f"{name} file must be a JSON object: {raw_path}")
        rows.append(loader(obj))
    return tuple(rows)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        runtime_krr_kb = _load_optional_mapping(args.krr_kb, name="krr-kb")
        runtime_external_signals = _load_optional_mapping(
            args.external_signals_file,
            name="external-signals-file",
        )
        runtime_signal_source_registry = _load_optional_mapping(
            args.signal_source_registry_file,
            name="signal-source-registry-file",
        )
        runtime_history = _load_optional_mapping(args.history_file, name="history-file")
        source_snapshots = _load_rows(
            list(args.source_snapshot_file),
            loader=krr_source_snapshot_from_dict,
            name="source snapshot",
        )
        evidence_records = _load_rows(
            list(args.evidence_record_file),
            loader=krr_evidence_record_from_dict,
            name="evidence record",
        )
        canonical_claims = _load_rows(
            list(args.claim_file),
            loader=krr_canonical_claim_from_dict,
            name="canonical claim",
        )
        review_records = _load_rows(
            list(args.review_record_file),
            loader=krr_review_record_from_dict,
            name="review record",
        )
        parent_bundle_hash = None
        if args.parent_bundle_file:
            parent_obj = _load_json(args.parent_bundle_file)
            if not isinstance(parent_obj, Mapping):
                raise ValueError("parent bundle file must be a JSON object")
            parent_bundle_hash = str(parent_obj.get("bundle_hash") or "").strip() or None
        bundle = build_autotrader_krr_bundle(
            bundle_name=str(args.bundle_name),
            built_at=str(args.built_at or _iso_now()),
            compiler_version=str(args.compiler_version),
            policy_version=str(args.policy_version),
            runtime_krr_kb=runtime_krr_kb,
            runtime_external_signals=runtime_external_signals,
            runtime_signal_source_registry=runtime_signal_source_registry,
            runtime_history=runtime_history,
            source_snapshots=source_snapshots,
            evidence_records=evidence_records,
            canonical_claims=canonical_claims,
            review_records=review_records,
            parent_bundle_hash=parent_bundle_hash,
        )
        signed_bundle = sign_autotrader_krr_bundle(bundle, privkey=args.signer_privkey)
        if not verify_autotrader_krr_bundle_signature(signed_bundle):
            raise ValueError("signed bundle failed self-verification")
        payload = {
            "schema": "zenodex/autotrader-krr-bundle-build/v1",
            "ok": True,
            "bundle_schema": AUTOTRADER_KRR_BUNDLE_SCHEMA,
            "bundle_hash": signed_bundle.bundle_hash_hex(),
            "runtime_approved": signed_bundle.runtime_approved(),
            "counts": {
                "source_snapshots": len(signed_bundle.source_snapshots),
                "evidence_records": len(signed_bundle.evidence_records),
                "canonical_claims": len(signed_bundle.canonical_claims),
                "review_records": len(signed_bundle.review_records),
                "derived_source_quality": len(signed_bundle.derived_source_quality),
            },
            "bundle": signed_bundle.to_dict(),
        }
        text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stdout.write(text)
        bundle_out = Path(args.bundle_out).expanduser().resolve()
        bundle_out.parent.mkdir(parents=True, exist_ok=True)
        bundle_out.write_text(
            json.dumps(signed_bundle.to_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/autotrader-krr-bundle-build/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
