#!/usr/bin/env python3
"""Replay the ZenoOracle devnet alpha package builder and validator."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zeno_oracle_rc_package import check_package  # noqa: E402

RESULT_SCHEMA = "zenodex.oracle.devnet_package_replay.v1"
REPLAY_VERSION = "zeno-oracle-devnet-package-replay-rc"
NOT_CLAIMED = [
    "does_not_claim_production_oracle_network",
    "does_not_claim_onchain_feed_governance",
    "does_not_claim_platform_native_binary",
    "does_not_claim_production_code_signing",
]


def _cleanup_package(version: str) -> None:
    dist = ROOT / "dist"
    for path in (
        dist / version,
        dist / f"{version}.tar.gz",
        dist / f"{version}.receipt.json",
        dist / f"{version}.sig",
    ):
        if path.is_dir():
            shutil.rmtree(path, ignore_errors=True)
        elif path.exists():
            path.unlink()


def build_devnet_package_replay() -> dict[str, Any]:
    physical_version = f"{REPLAY_VERSION}-{os.getpid()}"
    package_dir = ROOT / "dist" / physical_version
    receipt_path = ROOT / "dist" / f"{physical_version}.receipt.json"
    sig_path = ROOT / "dist" / f"{physical_version}.sig"
    errors: list[str] = []
    package_result: dict[str, Any] | None = None
    try:
        _cleanup_package(physical_version)
        proc = subprocess.run(
            ["bash", "scripts/package_zeno_oracle_rc.sh", physical_version],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if proc.returncode != 0:
            errors.append(f"package_builder_failed:{proc.returncode}")
            if proc.stderr:
                errors.append(f"package_builder_stderr:{proc.stderr.strip()[:500]}")
        else:
            package_result = check_package(
                package_dir=package_dir,
                receipt_path=receipt_path,
                sig_path=sig_path,
            )
            if package_result.get("status") != "accepted":
                errors.extend(f"package_check:{error}" for error in package_result.get("errors", []))
    finally:
        _cleanup_package(physical_version)

    accepted = not errors and package_result is not None and package_result.get("status") == "accepted"
    raw_manifest = package_result.get("manifest") if isinstance(package_result, dict) else None
    manifest = None
    if isinstance(raw_manifest, dict):
        manifest = {
            "entrypoint": raw_manifest.get("entrypoint"),
            "file_count": raw_manifest.get("file_count"),
            "required_file_count": raw_manifest.get("required_file_count"),
            "version": REPLAY_VERSION,
        }
    return {
        "schema": RESULT_SCHEMA,
        "ok": accepted,
        "status": "accepted" if accepted else "rejected",
        "package_version": REPLAY_VERSION,
        "package_check_schema": None if package_result is None else package_result.get("schema"),
        "manifest": manifest,
        "receipt_checked": bool(package_result and package_result.get("receipt_checked") is True),
        "signature_checked": bool(package_result and package_result.get("signature_checked") is True),
        "cleanup_complete": not package_dir.exists()
        and not receipt_path.exists()
        and not sig_path.exists()
        and not (ROOT / "dist" / f"{physical_version}.tar.gz").exists(),
        "errors": errors,
        "not_claimed": NOT_CLAIMED,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--output", help="optional output path for the JSON replay receipt")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    receipt = build_devnet_package_replay()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    if args.format == "json":
        sys.stdout.write(text)
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"schema = {receipt['schema']}",
                    f"status = {receipt['status']}",
                    f"receipt_checked = {receipt['receipt_checked']}",
                    f"signature_checked = {receipt['signature_checked']}",
                    f"cleanup_complete = {receipt['cleanup_complete']}",
                ]
            )
            + "\n"
        )
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
