#!/usr/bin/env python3
"""Generate or verify the research-only proof-market game-theory packet V2."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT: Final = REPO_ROOT / "docs/research/PROOF_MARKET_GAME_THEORY_V2.json"
SOURCE_PATHS: Final = (
    "tools/check_proof_market_game_theory_v2.py",
    "tools/proof_market_game_theory_packet_v2.py",
    "tools/proof_market_formal_evidence_v2.py",
    "tools/proof_market_game_theory_checks_v2.py",
    "tools/proof_market_v1_refutation_v2.py",
    "tools/proof_market_game_theory_v2.py",
    "tools/proof_market_game_theory_economics_v2.py",
    "tools/check_proof_market_calibration_v1.py",
    "tools/proof_market_calibration_v1.py",
    "docs/research/PROOF_MARKET_CALIBRATION_V1.json",
    "docs/research/PROOF_MARKET_GAME_THEORY_V2.md",
    "docs/research/PROOF_MARKET_PRIMARY_SOURCE_MANIFEST_V2.json",
    "src/kernels/dex/proof_market_procurement_v2.yaml",
    "docs/research/PROOF_MARKET_PROCUREMENT_ESSO_V2.json",
    "docs/research/PROOF_MARKET_PROCUREMENT_ESSO_REPORT_V2.json",
    "docs/research/PROOF_MARKET_PROCUREMENT_ESSO_BUNDLE_RESULT_V2.json",
    "docs/research/PROOF_MARKET_PROCUREMENT_FAULT_RACE_MUTANT_V2.yaml",
    "docs/research/PROOF_MARKET_PROCUREMENT_FAULT_RACE_MUTANT_ESSO_REPORT_V2.json",
    "docs/research/PROOF_MARKET_PROCUREMENT_FAULT_RACE_MUTANT_ESSO_BUNDLE_RESULT_V2.json",
    "lean-mathlib/Proofs/ZenoProofProcurementGameV2.lean",
    "lean-mathlib/Proofs.lean",
    "docs/research/PROOF_MARKET_GAME_THEORY_LEAN_V2.json",
)

sys.path.insert(0, str(REPO_ROOT))

from tools import proof_market_game_theory_packet_v2 as packet  # noqa: E402


def _canonical_bytes(document: dict[str, Any]) -> bytes:
    return json.dumps(document, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _source_pins() -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for relative_path in SOURCE_PATHS:
        path = REPO_ROOT / relative_path
        if not path.is_file():
            raise ValueError(f"missing game-theory source: {relative_path}")
        result.append({"path": relative_path, "sha256": _sha256(path.read_bytes())})
    return result


def _document() -> dict[str, Any]:
    return packet.build_document(
        source_pins=_source_pins(),
        checker_sha256=_sha256(Path(__file__).read_bytes()),
    )


def _write_or_check(path: Path, write: bool) -> tuple[bool, dict[str, Any]]:
    document = _document()
    expected = _canonical_bytes(document)
    if not document["ok"]:
        return False, {"ok": False, "error": "semantic checks failed"}
    if write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(expected)
        return True, {
            "ok": True,
            "mode": "write",
            "path": str(path),
            "sha256": _sha256(expected),
        }
    if not path.is_file():
        return False, {"ok": False, "error": f"missing artifact: {path}"}
    actual = path.read_bytes()
    return actual == expected, {
        "ok": actual == expected,
        "mode": "check",
        "path": str(path),
        "expected_sha256": _sha256(expected),
        "actual_sha256": _sha256(actual),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    ok, report = _write_or_check(args.output, args.write)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif ok:
        print(f"PASS: {report['path']}")
    else:
        print(f"FAIL: {report}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
