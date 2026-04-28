#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]

FORMAL_PROOF_HYGIENE_SCHEMA = "zenodex/formal-proof-hygiene/v1"

CRITICAL_FORMAL_PROOF_ARTIFACTS: tuple[str, ...] = (
    "lean-mathlib/Proofs/ZenoDEXUniqueCanonicalWinnerEverywhere.lean",
    "lean-mathlib/Proofs/ZenoDEXExactInRouteCertificate.lean",
    "lean-mathlib/Proofs/ZenoDEXExactInRouteRankProjection.lean",
    "lean-mathlib/Proofs/ZenoDEXExactInTrueKeyWinner.lean",
    "lean-mathlib/Proofs/ZenoDEXExactOutBruteforceCompleteness.lean",
    "lean-mathlib/Proofs/ZenoDEXExactOutCanonicalMinimizer.lean",
    "lean-mathlib/Proofs/ZenoDEXExactOutRouteCertificate.lean",
    "lean-mathlib/Proofs/ZenoDEXExactOutManyPoolCandidateDomainContract.lean",
    "lean-mathlib/Proofs/ZenoDEXExactOutManyPoolCertifiedWinnerPacket.lean",
    "lean-mathlib/Proofs/ZenoDEXSettlementCompactBundle.lean",
    "lean-mathlib/Proofs/ZenoDEXSettlementEndToEndCertificatePacket.lean",
    "lean-mathlib/Proofs/ZenoDEXSettlementPriceHistoryCertificate.lean",
    "lean-mathlib/Proofs/SettlementNetting.lean",
    "lean-mathlib/Proofs/AMMIntegerRuntimeBridge.lean",
    "lean-mathlib/Proofs/DisasterAntichainBasis.lean",
    "lean-mathlib/Proofs/CertificateGluing.lean",
    "lean-mathlib/Proofs/ForbiddenTraceMinor.lean",
    "lean-mathlib/Proofs/PerpEpochSafety.lean",
    "lean-mathlib/Proofs/PerpOracleGuard.lean",
    "lean-mathlib/Proofs/PerpFundingAlgebra.lean",
)

PLACEHOLDER_RE = re.compile(r"\b(sorry|admit|Admitted|Abort|oops)\b")


def _resolve(path: str | Path) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return REPO_ROOT / candidate


def strip_lean_comments(text: str) -> str:
    """Remove Lean line and nested block comments while preserving code layout."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            newline = text.find("\n", i)
            if newline == -1:
                break
            out.append("\n")
            i = newline + 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def build_formal_proof_hygiene_report(
    *,
    proof_files: Sequence[str] = CRITICAL_FORMAL_PROOF_ARTIFACTS,
) -> dict[str, Any]:
    errors: list[str] = []
    rows: list[dict[str, Any]] = []
    for proof_file in proof_files:
        path = _resolve(proof_file)
        row: dict[str, Any] = {
            "path": str(proof_file),
            "exists": path.is_file(),
            "active_placeholder_count": 0,
            "active_placeholders": [],
        }
        if not path.is_file():
            errors.append(f"missing proof artifact: {proof_file}")
            rows.append(row)
            continue
        stripped = strip_lean_comments(path.read_text(encoding="utf-8"))
        placeholders: list[dict[str, Any]] = []
        for line_no, line in enumerate(stripped.splitlines(), start=1):
            for match in PLACEHOLDER_RE.finditer(line):
                placeholders.append({"line": line_no, "token": match.group(1)})
        row["active_placeholder_count"] = len(placeholders)
        row["active_placeholders"] = placeholders
        if placeholders:
            details = ", ".join(f"{item['token']}@{item['line']}" for item in placeholders[:8])
            errors.append(f"{proof_file}: active proof placeholder(s): {details}")
        rows.append(row)
    return {
        "schema": FORMAL_PROOF_HYGIENE_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "proof_file_count": len(rows),
        "active_placeholder_count": sum(int(row["active_placeholder_count"]) for row in rows),
        "proof_files": rows,
    }


def _print_text(payload: dict[str, Any]) -> None:
    print("Formal Proof Hygiene")
    print(f"ok: {'yes' if payload['ok'] else 'no'}")
    print(f"proof_file_count: {payload['proof_file_count']}")
    print(f"active_placeholder_count: {payload['active_placeholder_count']}")
    if payload.get("errors"):
        print("errors:")
        for error in payload["errors"]:
            print(f"- {error}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Ratchet critical Lean proof artifacts against active placeholders.")
    parser.add_argument("proof_files", nargs="*", help="Proof files to check; defaults to critical ZenoDEX proof artifacts")
    parser.add_argument("--output", help="Optional path to write the report JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    proof_files = args.proof_files or list(CRITICAL_FORMAL_PROOF_ARTIFACTS)
    payload = build_formal_proof_hygiene_report(proof_files=proof_files)
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.format == "json":
        json.dump(payload, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(payload)
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
