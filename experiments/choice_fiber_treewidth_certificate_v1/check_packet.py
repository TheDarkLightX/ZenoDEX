#!/usr/bin/env python3
"""Closed manifest, dependency pin, and deterministic report gate."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from experiments.choice_fiber_treewidth_certificate_v1.run_experiment import build_report
from experiments.choice_fiber_treewidth_certificate_v1.source_identity import (
    TREEWIDTH_SOURCE_SHA256,
)
from experiments.choice_fiber_treewidth_certificate_v1.treewidth_certificate import (
    DEFAULT_PROFILE,
    ROBUSTNESS_SOURCE_SHA256,
    ZRPF_SOURCE_SHA256,
)

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[1]
EXPECTED = {
    "MATHEMATICAL_ASSESSMENT.md",
    "README.md",
    "check_packet.py",
    "report.json",
    "run_experiment.py",
    "source_identity.py",
    "test_treewidth_certificate.py",
    "treewidth_certificate.py",
}
DEPENDENCIES = {
    "experiments/choice_fiber_robustness_v1/named_choice_fiber.py": (ROBUSTNESS_SOURCE_SHA256),
    "experiments/zrpf_choice_subcube_coverage_v1/subcube_certificate.py": (ZRPF_SOURCE_SHA256),
}
REPORT_FIELDS = {
    "attack_summary",
    "attacks",
    "authority",
    "checked_claims",
    "claim_status",
    "classification",
    "content_sha256_without_this_field",
    "demonstrations",
    "exhaustive_campaign",
    "nonclaims",
    "object",
    "receipt_backend",
    "schema",
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
        if len(digest) != 64 or any(character not in "0123456789abcdef" for character in digest):
            raise SystemExit(f"INVALID_MANIFEST_DIGEST:{path_text}")
        rows[path_text] = digest
    return rows


def _validate_content_hash(report: dict[str, object]) -> None:
    retained = dict(report)
    claimed = retained.pop("content_sha256_without_this_field", None)
    actual = hashlib.sha256(
        json.dumps(retained, separators=(",", ":"), sort_keys=True).encode("ascii")
    ).hexdigest()
    if claimed != actual:
        raise SystemExit("REPORT_CONTENT_HASH_MISMATCH")


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

    for path_text, expected_digest in DEPENDENCIES.items():
        path = REPOSITORY / path_text
        if not path.is_file():
            raise SystemExit(f"DEPENDENCY_MISSING:{path_text}")
        if _sha256(path) != expected_digest:
            raise SystemExit(f"DEPENDENCY_SHA256_MISMATCH:{path_text}")

    if (
        _sha256(ROOT / "treewidth_certificate.py") != TREEWIDTH_SOURCE_SHA256
        or DEFAULT_PROFILE.treewidth_source_sha256 != TREEWIDTH_SOURCE_SHA256
        or DEFAULT_PROFILE.robustness_source_sha256 != ROBUSTNESS_SOURCE_SHA256
        or DEFAULT_PROFILE.zrpf_source_sha256 != ZRPF_SOURCE_SHA256
    ):
        raise SystemExit("PROFILE_DEPENDENCY_PIN_MISMATCH")

    report = json.loads((ROOT / "report.json").read_text(encoding="utf-8"))
    if type(report) is not dict or set(report) != REPORT_FIELDS:
        raise SystemExit("REPORT_SCHEMA_MISMATCH")
    if report != build_report():
        raise SystemExit("REPORT_REGENERATION_MISMATCH")
    _validate_content_hash(report)
    if (
        report.get("authority") != "NONE"
        or report.get("claim_status") != "BOUNDED_RESEARCH_ONLY"
        or report.get("classification") != "USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL"
        or report.get("receipt_backend") != "PYTHON_REFERENCE_REPLAY"
    ):
        raise SystemExit("CLAIM_CEILING_VIOLATION")
    attack_summary = report.get("attack_summary")
    if type(attack_summary) is not dict or (
        attack_summary.get("killed") != attack_summary.get("named_attacks")
        or attack_summary.get("survived") != 0
    ):
        raise SystemExit("ATTACK_CAMPAIGN_INCOMPLETE")

    print(
        json.dumps(
            {
                "authority": "NONE",
                "dependency_pins": len(DEPENDENCIES),
                "manifest_entries": len(rows),
                "mutants_killed": attack_summary["killed"],
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
