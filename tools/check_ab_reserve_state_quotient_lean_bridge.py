#!/usr/bin/env python3
"""Emit a deterministic receipt for the AB reserve-state quotient Lean bridge.

This evidence tool is research-only.  It checks that the Lean proof component
names the reserve-state quotient contract, verifies the focused formal test
exists, scans for forbidden proof placeholders, and writes a machine-readable
receipt plus a short report.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LEAN_PATH = ROOT / "lean-mathlib" / "Proofs" / "ABReserveStateQuotient.lean"
TEST_PATH = ROOT / "tests" / "formal" / "test_lean_ab_reserve_state_quotient.py"
OUT_DIR = ROOT / "generated" / "zenodex_ab_reserve_state_quotient_lean_bridge_20260629"
REPORT_PATH = OUT_DIR / "report.json"
DOC_PATH = ROOT / "docs" / "research" / "ZENODEX_AB_RESERVE_STATE_QUOTIENT_LEAN_BRIDGE_20260629.md"

SCHEMA = "zenodex/ab_reserve_state_quotient_lean_bridge/v1"
AUTHORITY_BOUNDARY = (
    "Research proof component only; no settlement, state-root, production, "
    "governance, routing, matching, or transaction authority."
)
FORBIDDEN_PROOF_WORDS = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")

REQUIRED_LEAN_MARKERS = [
    "structure ReserveState",
    "def ReserveState.toRecord",
    "def ReserveState.afterStep",
    "def reserveStateEquivalent",
    "theorem reserveStateEquivalent_same_finalReserveOut",
    "theorem reserveStateEquivalent_same_suffixOutput",
    "theorem reserveState_minReserve_dominates_suffixOutput",
    "def quotientFullBestSuffixOutput",
    "def reserveStateQuotientInvariant",
    "theorem reserveState_afterStep_same_processed",
    "theorem reserveState_afterStep_minReserve",
    "theorem reserveStateQuotientInvariant_afterStep",
    "theorem strictStepExecutable_mono_reserveOut",
    "theorem suffixExecutable_mono_reserveOut",
    "theorem reserveStateQuotientInvariant_candidateSuffixExecutable",
    "theorem reserveStateQuotientInvariant_familySuffixExecutable",
    "theorem quotientFullBestSuffixOutput_le_selected",
    "def quotientFullFrontierZeroMinEconomicKey",
    "def quotientSelectedZeroMinEconomicKey",
    "theorem reserveStateQuotientInvariant_bounds_zeroMinEconomicKey",
    "structure ReserveStateQuotientHostTable",
    "def reserveStateQuotientHostTableValid",
    "theorem reserveStateQuotientHostTable_validates",
    "structure ReserveStateQuotientObservedSummary",
    "def reserveStateQuotientObservedSummaryValid",
    "def reserveStateQuotientObservedSummaryFullKey",
    "def reserveStateQuotientObservedSummarySelectedKey",
    "theorem reserveStateQuotientObservedSummary_to_hostTableValid",
    "theorem reserveStateQuotientObservedSummary_validates",
    "theorem witness_reserveStateEquivalent_same_suffixOutput",
    "theorem witness_reserveStateQuotientHostTable_validates",
    "theorem witness_reserveStateQuotientInvariant_afterStep",
    "theorem witness_reserveStateQuotientInvariant_familySuffixExecutable",
    "theorem witness_reserveStateQuotientObservedSummary_validates",
]

REQUIRED_TEST_MARKERS = [
    "test_lean_ab_reserve_state_quotient_typechecks_without_placeholders",
    "Proofs/ABReserveStateQuotient.lean",
    "reserveStateQuotientHostTable_validates",
    "reserveStateQuotientObservedSummary_validates",
]

NON_CLAIMS = [
    "No Python-to-Lean refinement proof is claimed.",
    "No JSON canonicalization or packet-hash computation is proved in Lean.",
    "No canonical tie order or order-history preservation is claimed.",
    "No nonzero min_amount_out coverage is claimed.",
    "No settlement, state-root, production, governance, routing, matching, or transaction authority is derived.",
]


def _sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _sha256_path(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _missing_markers(text: str, markers: list[str]) -> list[str]:
    return [marker for marker in markers if marker not in text]


def build_report() -> dict[str, Any]:
    lean_text = LEAN_PATH.read_text(encoding="utf-8")
    test_text = TEST_PATH.read_text(encoding="utf-8")
    missing_lean = _missing_markers(lean_text, REQUIRED_LEAN_MARKERS)
    missing_test = _missing_markers(test_text, REQUIRED_TEST_MARKERS)
    forbidden_lean = sorted(set(FORBIDDEN_PROOF_WORDS.findall(lean_text)))

    checks = {
        "lean_file_exists": LEAN_PATH.exists(),
        "test_file_exists": TEST_PATH.exists(),
        "required_lean_markers_present": not missing_lean,
        "required_test_markers_present": not missing_test,
        "lean_placeholder_scan_clean": not forbidden_lean,
    }

    ok = all(checks.values())
    return {
        "schema": SCHEMA,
        "ok": ok,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "claim_scope": (
            "A Lean proof component formalizes the reserve-state quotient bridge "
            "for the AB strict zero-min research surface: same reserve-state "
            "quotient rows have identical fixed-suffix behavior, and a selected "
            "minimum reserve-out state dominates a finite quotient family at "
            "fixed executed input. It also proves the selected representative "
            "remains valid after one common exact-in step is applied to every "
            "family member, and that selected suffix executability lifts to all "
            "higher-reserve family members. The observed-summary layer binds "
            "host-visible count and selected-state metadata to the validated "
            "Lean table."
        ),
        "artifacts": {
            "lean_file": str(LEAN_PATH.relative_to(ROOT)),
            "lean_sha256": _sha256_path(LEAN_PATH),
            "lean_line_count": len(lean_text.splitlines()),
            "formal_test": str(TEST_PATH.relative_to(ROOT)),
            "formal_test_sha256": _sha256_path(TEST_PATH),
            "formal_test_line_count": len(test_text.splitlines()),
        },
        "checks": checks,
        "missing": {
            "lean_markers": missing_lean,
            "test_markers": missing_test,
            "forbidden_lean_terms": forbidden_lean,
        },
        "required_lean_markers": REQUIRED_LEAN_MARKERS,
        "non_claims": NON_CLAIMS,
        "replay_commands": [
            "cd lean-mathlib && lake env lean Proofs/ABReserveStateQuotient.lean",
            "cd lean-mathlib && lake build Proofs.ABReserveStateQuotient",
            "python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABReserveStateQuotient.lean",
            "PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_reserve_state_quotient.py",
            "python3 tools/check_ab_reserve_state_quotient_lean_bridge.py",
            "python3 tools/check_public_claim_scope.py --root . --json",
            "python3 tools/check_claims_registry.py",
        ],
    }


def write_report(report: dict[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines = [
        "# AB Reserve-State Quotient Lean Bridge",
        "",
        "Research-only proof component; no settlement, state-root, production, governance, routing, matching, or transaction authority.",
        "",
        "## Claim Scope",
        "",
        str(report["claim_scope"]),
        "",
        "## Checks",
        "",
    ]
    checks: dict[str, bool] = report["checks"]
    for key, value in checks.items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Artifacts",
            "",
            f"- Lean file: `{report['artifacts']['lean_file']}`",
            f"- Lean SHA-256: `{report['artifacts']['lean_sha256']}`",
            f"- Lean line count: `{report['artifacts']['lean_line_count']}`",
            f"- Formal test: `{report['artifacts']['formal_test']}`",
            f"- Formal test SHA-256: `{report['artifacts']['formal_test_sha256']}`",
            "",
            "## Replay",
            "",
        ]
    )
    for command in report["replay_commands"]:
        lines.append(f"- `{command}`")
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.append("")
    DOC_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Print the report JSON to stdout")
    args = parser.parse_args()

    report = build_report()
    write_report(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"ok={report['ok']} report={REPORT_PATH.relative_to(ROOT)} doc={DOC_PATH.relative_to(ROOT)}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
