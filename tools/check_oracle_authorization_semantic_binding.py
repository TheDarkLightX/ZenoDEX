#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_oracle_authorization import (  # noqa: E402
    CRITICAL_CONSUMER_PROFILES,
    SCHEMA,
    OracleAuthorization,
    RuntimeActionFacts,
    check_authorization_for_runtime,
    check_authorization_payload,
    check_critical_consumer_authorization,
    economic_envelope_hash,
    oracle_value_hash,
    semantic_hash,
    verify_opaque_authorization,
    verify_typed_authorization,
)

__all__ = [
    "SCHEMA",
    "CRITICAL_CONSUMER_PROFILES",
    "OracleAuthorization",
    "RuntimeActionFacts",
    "check_critical_consumer_authorization",
    "check_authorization_for_runtime",
    "check_authorization_payload",
    "economic_envelope_hash",
    "oracle_value_hash",
    "semantic_hash",
    "verify_opaque_authorization",
    "verify_typed_authorization",
]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check typed OracleAuthorization semantic binding.")
    parser.add_argument("payload", help="JSON file with authorization and runtime_action objects")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    payload = json.loads(Path(args.payload).read_text(encoding="utf-8"))
    if not isinstance(payload, Mapping):
        raise SystemExit("payload root must be an object")
    result = check_authorization_payload(payload)
    if args.format == "json":
        json.dump(result, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        print("OracleAuthorization Semantic Binding")
        print(f"opaque_ok: {'yes' if result['opaque_ok'] else 'no'}")
        print(f"typed_ok: {'yes' if result['typed_ok'] else 'no'}")
        for error in result["typed_errors"]:
            print(f"typed_error: {error}")
    return 0 if result["typed_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
