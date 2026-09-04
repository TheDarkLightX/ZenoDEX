#!/usr/bin/env python3
"""Closed source-manifest and deterministic-report gate."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from run_experiments import build_report

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "MATHEMATICAL_ASSESSMENT.md",
    "README.md",
    "check_packet.py",
    "named_choice_fiber.py",
    "report.json",
    "run_experiments.py",
    "test_named_choice_fiber.py",
}
FORBIDDEN_PUBLIC_TEXT = (
    "/" + "home" + "/",
    "/" + "tmp" + "/",
    "sandbox" + ":/",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _manifest() -> dict[str, str]:
    rows: dict[str, str] = {}
    for line in (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        digest, separator, path_text = line.partition("  ")
        if not separator or path_text in rows:
            raise SystemExit("MALFORMED_OR_DUPLICATE_MANIFEST_ROW")
        path = Path(path_text)
        if path.is_absolute() or ".." in path.parts or path.as_posix() != path_text:
            raise SystemExit(f"UNSAFE_MANIFEST_PATH:{path_text}")
        rows[path_text] = digest
    return rows


def main() -> int:
    rows = _manifest()
    if set(rows) != EXPECTED:
        raise SystemExit("MANIFEST_CLOSED_WORLD_MISMATCH")
    for path_text, expected_digest in rows.items():
        path = ROOT / path_text
        if not path.is_file():
            raise SystemExit(f"MANIFEST_FILE_MISSING:{path_text}")
        if _sha256(path) != expected_digest:
            raise SystemExit(f"MANIFEST_SHA256_MISMATCH:{path_text}")
        if path.suffix in {".md", ".py", ".json"}:
            text = path.read_text(encoding="utf-8")
            if any(marker in text for marker in FORBIDDEN_PUBLIC_TEXT):
                raise SystemExit(f"MACHINE_LOCAL_PATH:{path_text}")

    report = json.loads((ROOT / "report.json").read_text(encoding="utf-8"))
    if report != build_report():
        raise SystemExit("REPORT_REGENERATION_MISMATCH")
    if (
        report.get("claim_ceiling") != "BOUNDED_RESEARCH_ONLY"
        or report.get("classification") != "USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL"
    ):
        raise SystemExit("CLAIM_CEILING_VIOLATION")

    print(
        json.dumps(
            {
                "authority": "NONE",
                "classification": report["classification"],
                "manifest_entries": len(rows),
                "report_sha256": _sha256(ROOT / "report.json"),
                "status": "PASS",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
