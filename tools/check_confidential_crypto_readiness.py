#!/usr/bin/env python3
"""Emit or gate the confidential crypto readiness report."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.confidential_crypto_readiness import build_confidential_crypto_readiness_v1
from src.integration.confidential_feature_status import load_confidential_feature_status_from_env


def _read_mapping(path: str | None, *, label: str) -> Mapping[str, Any] | None:
    if path is None:
        return None
    obj = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{label} must be a JSON object")
    return obj


def _read_backend_descriptors(paths: list[str]) -> tuple[Mapping[str, Any], ...]:
    out: list[Mapping[str, Any]] = []
    for index, path in enumerate(paths):
        obj = _read_mapping(path, label=f"key backend descriptor {index}")
        if obj is not None:
            out.append(obj)
    return tuple(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--confidential-status",
        help="optional confidential feature status JSON; defaults to env-derived status",
    )
    parser.add_argument("--attestation-status", help="optional confidential attestation status JSON")
    parser.add_argument("--encrypted-sss-status", help="optional encrypted SSS backup status JSON")
    parser.add_argument(
        "--key-backend-descriptor",
        action="append",
        default=[],
        help="optional key backend descriptor JSON; may be repeated",
    )
    parser.add_argument("--out", help="write report JSON to this path instead of stdout")
    parser.add_argument(
        "--require-production-ready",
        action="store_true",
        help="exit nonzero unless production_ready and host_independent_ready are both true",
    )
    args = parser.parse_args(argv)

    confidential_status = _read_mapping(args.confidential_status, label="confidential status")
    if confidential_status is None:
        confidential_status = load_confidential_feature_status_from_env().to_public_dict()
    report = build_confidential_crypto_readiness_v1(
        confidential_status=confidential_status,
        attestation_status=_read_mapping(args.attestation_status, label="attestation status"),
        encrypted_sss_backup_status=_read_mapping(args.encrypted_sss_status, label="encrypted SSS status"),
        key_backend_descriptors=_read_backend_descriptors(args.key_backend_descriptor),
    )
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(encoded, encoding="utf-8")
    else:
        sys.stdout.write(encoded)
    if args.require_production_ready and not (
        report.get("production_ready") is True and report.get("host_independent_ready") is True
    ):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
