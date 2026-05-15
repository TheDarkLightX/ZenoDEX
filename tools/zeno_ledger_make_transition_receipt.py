#!/usr/bin/env python3
"""Build a ZenoLedger scaling transition receipt from a header."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_scaling_v0 import (
    ZERO_ROOT_V0,
    build_execution_journal_from_header_v0,
    build_transition_receipt_v0,
    execution_journal_hash_v0,
    validate_header_transition_receipt_binding_v0,
)
from src.integration.zeno_ledger_v0 import validate_header_v0


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_transition_receipt_report_v0(
    *,
    header: Mapping[str, Any],
    program_id: str,
    proof_policy_id: str,
    feature_suite_hash: str,
    token_registry_hash: str,
    rejection_receipt_root: str,
    verifier_kind: str,
    verifier_version: str,
    proof_commitment: str,
    receipt_metadata_hash: str,
) -> dict[str, Any]:
    validate_header_v0(dict(header))
    journal = build_execution_journal_from_header_v0(
        header=header,
        program_id=program_id,
        proof_policy_id=proof_policy_id,
        feature_suite_hash=feature_suite_hash,
        token_registry_hash=token_registry_hash,
        rejection_receipt_root=rejection_receipt_root,
    )
    receipt = build_transition_receipt_v0(
        execution_journal=journal,
        verifier_kind=verifier_kind,
        verifier_version=verifier_version,
        proof_commitment=proof_commitment,
        receipt_metadata_hash=receipt_metadata_hash,
    )
    journal_hash = execution_journal_hash_v0(journal)
    binding_ok = True
    binding_error = None
    try:
        validate_header_transition_receipt_binding_v0(header, receipt)
    except Exception as exc:
        binding_ok = False
        binding_error = str(exc)

    return {
        "schema": "zenodex.zeno_ledger.transition_receipt_report.v0",
        "status": "accepted",
        "ok": True,
        "header_binding": {
            "ok": binding_ok,
            "error": binding_error,
            "header_proof_journal_hash": header["proof_journal_hash"],
            "required_proof_journal_hash": journal_hash,
        },
        "execution_journal": journal,
        "execution_journal_hash": journal_hash,
        "transition_receipt": receipt,
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--header", required=True, type=Path, help="Path to a ZenoLedger header JSON file")
    parser.add_argument("--out", required=True, type=Path, help="Path for the transition receipt report JSON")
    parser.add_argument("--program-id", default="zenodex.scaling.replay.v0")
    parser.add_argument("--proof-policy-id", default="public-testnet-replay-v0")
    parser.add_argument("--feature-suite-hash", default=ZERO_ROOT_V0)
    parser.add_argument("--token-registry-hash", default=ZERO_ROOT_V0)
    parser.add_argument("--rejection-receipt-root", default=ZERO_ROOT_V0)
    parser.add_argument("--verifier-kind", default="deterministic_replay_v0")
    parser.add_argument("--verifier-version", default="zeno-ledger-replay-0")
    parser.add_argument("--proof-commitment", default=ZERO_ROOT_V0)
    parser.add_argument("--receipt-metadata-hash", default=ZERO_ROOT_V0)
    parser.add_argument(
        "--require-header-binding",
        action="store_true",
        help="Fail if header.proof_journal_hash does not already equal the journal hash",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    report = build_transition_receipt_report_v0(
        header=_load_json_object(args.header),
        program_id=args.program_id,
        proof_policy_id=args.proof_policy_id,
        feature_suite_hash=args.feature_suite_hash,
        token_registry_hash=args.token_registry_hash,
        rejection_receipt_root=args.rejection_receipt_root,
        verifier_kind=args.verifier_kind,
        verifier_version=args.verifier_version,
        proof_commitment=args.proof_commitment,
        receipt_metadata_hash=args.receipt_metadata_hash,
    )
    if args.require_header_binding and not report["header_binding"]["ok"]:
        print(json.dumps(report, indent=2, sort_keys=True), file=sys.stderr)
        return 2
    _write_json(args.out, report)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

