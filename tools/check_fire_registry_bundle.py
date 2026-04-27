from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.bundle_v1 import verify_fire_registry_bundle  # noqa: E402
from src.fire.registry.instance_v1 import verify_fire_object_instance_against_manifest  # noqa: E402
from src.fire.verifier.cert_v1 import FireIntervalCertificate  # noqa: E402


CHECK_REPORT_SCHEMA = "zenodex/fire-registry-bundle-check-report/v1"


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Fail-closed checker for a FIRE registry bundle directory.")
    parser.add_argument("--bundle-dir", type=Path, required=True, help="Path to the FIRE registry bundle directory")
    parser.add_argument("--expected-bundle-hash", help="Optional expected bundle_hash from bundle_manifest.json")
    parser.add_argument("--expected-bundle-file-sha256", help="Optional expected SHA-256 of bundle_manifest.json")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON verification report")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)

    ok, err, bundle_manifest, object_manifest, object_instance, object_lock = verify_fire_registry_bundle(
        args.bundle_dir,
        expected_bundle_hash=args.expected_bundle_hash,
        expected_bundle_file_sha256=args.expected_bundle_file_sha256,
    )
    if ok and bundle_manifest is not None and object_manifest is not None and object_instance is not None and object_lock is not None:
        _gate_ok, _gate_err, gate_report = verify_fire_object_instance_against_manifest(
            object_instance,
            object_manifest=object_manifest,
        )
        cert_payload = json.loads((args.bundle_dir / bundle_manifest.certificate_path).read_text(encoding="utf-8"))
        certificate = FireIntervalCertificate.from_dict(cert_payload)
        object_card_text = (args.bundle_dir / bundle_manifest.object_card_path).read_text(encoding="utf-8")
        payload = {
            "schema": CHECK_REPORT_SCHEMA,
            "ok": True,
            "bundle_dir": str(args.bundle_dir.resolve()),
            "bundle_hash": bundle_manifest.bundle_hash,
            "object_name": object_manifest.object_name,
            "object_version": object_manifest.object_version,
            "object_family": object_manifest.object_family,
            "object_hash": object_manifest.manifest_hash,
            "manifest_hash": object_manifest.manifest_hash,
            "instance_hash": object_instance.instance_hash,
            "lock_hash": object_lock.lock_hash,
            "cert_sha256": object_manifest.cert_sha256,
            "object_card_noncanonical": True,
            "object_card_text": object_card_text,
            "certificate_instance_gate_claims": (
                None
                if certificate.instance_gate_claims is None
                else certificate.instance_gate_claims.to_dict()
            ),
            "artifact_lower": object_manifest.artifact_lower,
            "artifact_upper": object_manifest.artifact_upper,
            "instance_gates": gate_report.to_dict(),
        }
        sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 0

    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": False,
        "bundle_dir": str(args.bundle_dir.resolve()),
        "error": err or "bundle_verification_failed",
    }
    sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
