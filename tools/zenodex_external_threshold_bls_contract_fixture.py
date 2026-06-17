#!/usr/bin/env python3
"""Contract-test fixture for the external threshold-BLS signer boundary.

This command is deliberately not a production signer. It lets integration tests
exercise the same stdin/stdout contract that a real drand/ssv signer command
must implement.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenodex_external_threshold_bls import (  # noqa: E402
    build_external_threshold_bls_signature_receipt_v0,
    validate_external_threshold_bls_evidence_v0,
    validate_external_threshold_bls_sign_request_v0,
)
from src.integration.zenodex_threshold_bls import (  # noqa: E402
    build_threshold_bls_partial_signature_v0,
    combine_threshold_bls_partial_signatures_v0,
)


def _load_json(path: str) -> Mapping[str, Any]:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(payload, Mapping):
        raise ValueError(f"{path} must contain a JSON object")
    return payload


def _cmd_sign(args: argparse.Namespace) -> int:
    if not args.contract_test_only:
        raise ValueError("--contract-test-only is required; this command is not a production signer")
    evidence = _load_json(args.evidence)
    public_bundle = _load_json(args.public_bundle)
    shares = [_load_json(path) for path in args.share]
    request = json.loads(sys.stdin.buffer.read().decode("utf-8"))
    if not isinstance(request, Mapping):
        raise ValueError("stdin must contain an external threshold-BLS sign request")

    validate_external_threshold_bls_evidence_v0(evidence)
    validate_external_threshold_bls_sign_request_v0(request)
    if request.get("evidence_hash") != evidence.get("evidence_hash"):
        raise ValueError("request evidence_hash does not match fixture evidence")

    payload = request["payload"]
    if not isinstance(payload, Mapping):
        raise ValueError("request payload must be a JSON object")
    partials = [
        build_threshold_bls_partial_signature_v0(share, public_bundle=public_bundle, payload=payload)
        for share in shares
    ]
    aggregate = combine_threshold_bls_partial_signatures_v0(partials, public_bundle=public_bundle, payload=payload)
    receipt = build_external_threshold_bls_signature_receipt_v0(
        evidence=evidence,
        payload=payload,
        participant_ids=[str(item) for item in aggregate["participant_ids"]],
        partial_signature_hashes=[str(item) for item in aggregate["partial_signature_hashes"]],
        signature=str(aggregate["signature"]),
    )
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract-test-only", action="store_true")
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--public-bundle", required=True)
    parser.add_argument("--share", action="append", required=True)
    args = parser.parse_args(argv)
    return _cmd_sign(args)


if __name__ == "__main__":
    raise SystemExit(main())
