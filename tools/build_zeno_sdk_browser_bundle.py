#!/usr/bin/env python3
"""Build a structural-diagnostic browser checkpoint bundle for Zeno SDK clients."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_sdk_browser_bundle_v0 import (  # noqa: E402
    BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    build_browser_checkpoint_bundle_v0,
    validate_browser_checkpoint_bundle_v0,
)
from tools.check_zeno_ledger_light_client_checkpoint import (  # noqa: E402
    validate_light_client_checkpoint_v0,
)
from tools.zeno_ledger_verify import ZERO_ROOT  # noqa: E402

BUILD_REPORT_SCHEMA_V0 = "zenodex.zeno_sdk.browser_checkpoint_bundle_build_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def build_browser_bundle_from_files(
    *,
    headers_dir: Path,
    bodies_dir: Path,
    checkpoints_dir: Path,
    registry_path: Path,
    envelope_paths: list[Path],
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str = ZERO_ROOT,
    profile_path: Path | None = None,
    proof_metadata_dir: Path | None = None,
    proof_verification_report_dir: Path | None = None,
    require_proof_verification_report: bool = False,
    builder_id: str = "zenoctl",
) -> dict[str, Any]:
    registry = _load_json_object(registry_path)
    envelopes = [_load_json_object(path) for path in envelope_paths]
    report = validate_light_client_checkpoint_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry=registry,
        envelopes=envelopes,
        from_height=from_height,
        to_height=to_height,
        trusted_prev_header_hash=trusted_prev_header_hash,
        profile_path=profile_path,
        proof_metadata_dir=proof_metadata_dir,
        proof_verification_report_dir=proof_verification_report_dir,
        require_proof_verification_report=require_proof_verification_report,
    )
    if report.get("ok") is not True:
        raise ValueError("light client checkpoint verification rejected")

    target_header = _load_json_object(headers_dir / f"{to_height}.json")
    target_checkpoint = _load_json_object(checkpoints_dir / f"{to_height}.json")
    header_chain = [_load_json_object(headers_dir / f"{height}.json") for height in range(from_height, to_height + 1)]
    bundle = build_browser_checkpoint_bundle_v0(
        target_header=target_header,
        target_checkpoint=target_checkpoint,
        header_chain=header_chain,
        signer_registry=registry,
        signature_envelopes=envelopes,
        light_client_report=report,
        builder_id=builder_id,
    )
    validate_browser_checkpoint_bundle_v0(bundle)
    return bundle


def _build_rejection(*, error: str, light_client_report: Mapping[str, Any] | None = None) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema": BUILD_REPORT_SCHEMA_V0,
        "ok": False,
        "status": "rejected",
        "error": error,
    }
    if light_client_report is not None:
        payload["light_client_report"] = dict(light_client_report)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--headers-dir", required=True, type=Path)
    parser.add_argument("--bodies-dir", required=True, type=Path)
    parser.add_argument("--checkpoints-dir", required=True, type=Path)
    parser.add_argument("--registry", required=True, type=Path)
    parser.add_argument("--envelope", required=True, action="append", type=Path)
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT)
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--proof-metadata-dir", type=Path)
    parser.add_argument("--proof-verification-report-dir", type=Path)
    parser.add_argument("--require-proof-verification-report", action="store_true")
    parser.add_argument("--builder-id", default="zenoctl")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        bundle = build_browser_bundle_from_files(
            headers_dir=args.headers_dir,
            bodies_dir=args.bodies_dir,
            checkpoints_dir=args.checkpoints_dir,
            registry_path=args.registry,
            envelope_paths=list(args.envelope),
            from_height=args.from_height,
            to_height=args.to_height,
            trusted_prev_header_hash=args.trusted_prev_header_hash,
            profile_path=args.profile,
            proof_metadata_dir=args.proof_metadata_dir,
            proof_verification_report_dir=args.proof_verification_report_dir,
            require_proof_verification_report=args.require_proof_verification_report,
            builder_id=args.builder_id,
        )
    except Exception as exc:
        print(json.dumps(_build_rejection(error=str(exc)), indent=2 if args.pretty else None, sort_keys=True))
        return 1

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report = {
        "schema": BUILD_REPORT_SCHEMA_V0,
        "ok": True,
        "status": "structural_diagnostic_packaged",
        "bundle_schema": BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
        "bundle_hash": bundle["bundle_hash"],
        "out": str(args.out),
        "chain_id": bundle["chain_id"],
        "from_height": bundle["from_height"],
        "to_height": bundle["to_height"],
        "capabilities": bundle["capabilities"],
        "non_claims": bundle["non_claims"],
    }
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
