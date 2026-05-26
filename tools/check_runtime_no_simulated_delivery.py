#!/usr/bin/env python3
"""Reject simulated external-delivery success paths in runtime code."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
REPORT_SCHEMA = "zenodex/runtime_no_simulated_delivery_report/v1"
DEFAULT_TARGETS = (
    ROOT / "src" / "integration" / "perps_wallet_api.py",
    ROOT / "tools" / "zenoctl_testnet_local" / "lifecycle.py",
    ROOT / "tools" / "dex-ui" / "src" / "lib" / "api.js",
)

FORBIDDEN_MARKERS = (
    "local_testnet_provider_simulation",
    "local_testnet_provider_delivery_simulation",
    "local-smtp:",
    "local-smtp-message:",
    "local-dropbox:",
    "local-box:",
    "local-offline-export:",
    "deliver-local",
    "apiDeliverPerpsEncryptedSssBackupLocal",
    "local provider receipts ready",
    "local provider delivery",
    "shares are encrypted before email/cloud/offline transport",
)


def scan_no_simulated_delivery(paths: Iterable[Path] = DEFAULT_TARGETS) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []
    scanned: list[str] = []
    for path in paths:
        scanned.append(str(path))
        try:
            text = path.read_text(encoding="utf-8")
        except Exception as exc:
            findings.append({"path": str(path), "marker": "<read_error>", "line": 0, "detail": str(exc)})
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            for marker in FORBIDDEN_MARKERS:
                if marker in line:
                    findings.append(
                        {
                            "path": str(path),
                            "line": line_no,
                            "marker": marker,
                            "detail": line.strip(),
                        }
                    )
    return {
        "schema": REPORT_SCHEMA,
        "ok": not findings,
        "scanned": scanned,
        "forbidden_markers": list(FORBIDDEN_MARKERS),
        "findings": findings,
        "negative_knowledge": (
            "This gate blocks known simulated provider-delivery success markers. "
            "It does not prove all runtime paths are production-complete."
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    report = scan_no_simulated_delivery(args.paths or DEFAULT_TARGETS)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["ok"]:
        print("ok")
    else:
        print("error: simulated external-delivery runtime marker found")
        for finding in report["findings"]:
            print(
                f"  - {finding['path']}:{finding['line']} "
                f"{finding['marker']}: {finding['detail']}"
            )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
