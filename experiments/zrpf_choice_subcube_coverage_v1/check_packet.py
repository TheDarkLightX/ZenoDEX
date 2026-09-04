#!/usr/bin/env python3
"""Closed source-manifest and deterministic campaign gate."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from run_experiment import attack_campaign, exhaustive_campaign
from search_nonrecursive_partition import classify_all

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "README.md",
    "check_packet.py",
    "deterministic_receipt.json",
    "run_experiment.py",
    "search_nonrecursive_partition.py",
    "subcube_certificate.py",
    "test_subcube_certificate.py",
}
FORBIDDEN_PUBLIC_TEXT = (
    "/" + "home" + "/",
    "/" + "tmp" + "/",
    "sandbox" + ":/",
)


def _canonical(value: object) -> bytes:
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_receipt() -> dict[str, object]:
    attacks = attack_campaign()
    receipt: dict[str, object] = {
        "attack_summary": {
            "killed": len(attacks),
            "named_attacks": len(attacks),
            "survived": 0,
        },
        "attacks": attacks,
        "authority": "NONE",
        "claim_status": "BOUNDED_RESEARCH_ONLY",
        "classification": "USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL",
        "exhaustive_campaign": exhaustive_campaign(),
        "object": "named_choice_subcube_coverage_v1",
        "partition_classification": [classify_all(nchoices) for nchoices in (1, 2, 3)],
        "schema": "zenodex.choice-subcube-coverage.receipt.v1",
    }
    receipt["content_sha256_without_this_field"] = hashlib.sha256(_canonical(receipt)).hexdigest()
    return receipt


def _manifest() -> dict[str, str]:
    rows: dict[str, str] = {}
    for line in (ROOT / "MANIFEST.sha256").read_text(encoding="utf-8").splitlines():
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

    expected = build_receipt()
    actual = json.loads((ROOT / "deterministic_receipt.json").read_text(encoding="utf-8"))
    if actual != expected:
        raise SystemExit("CAMPAIGN_REGENERATION_MISMATCH")
    if actual.get("authority") != "NONE" or actual.get("claim_status") != "BOUNDED_RESEARCH_ONLY":
        raise SystemExit("CLAIM_CEILING_VIOLATION")

    print(
        json.dumps(
            {
                "authority": "NONE",
                "manifest_entries": len(rows),
                "mutants_killed": actual["attack_summary"]["killed"],
                "receipt_sha256": _sha256(ROOT / "deterministic_receipt.json"),
                "status": "PASS",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
