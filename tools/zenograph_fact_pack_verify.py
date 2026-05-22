#!/usr/bin/env python3
"""Verify a reviewed, signed ZenoGraph fact pack."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.zenograph_fact_pack import (  # noqa: E402
    load_zenograph_fact_pack_file,
    zenograph_runtime_facts,
)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--pack-file", required=True)
    ap.add_argument("--allow-unsigned", action="store_true")
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        pack = load_zenograph_fact_pack_file(
            args.pack_file,
            require_signature=not bool(args.allow_unsigned),
            require_review=True,
        )
        runtime_facts = zenograph_runtime_facts(pack)
        payload = {
            "schema": "zenodex/zenograph-fact-pack-verify/v1",
            "ok": True,
            "pack_name": pack.pack_name,
            "pack_hash": pack.pack_hash_hex(),
            "signature_present": pack.signature is not None,
            "review_gate_ok": pack.runtime_approved(),
            "runtime_fact_count": len(runtime_facts),
            "fact_ids": [row.fact_id for row in pack.facts],
            "subject_predicates": [
                f"{row.subject_id}.{row.predicate}" for row in pack.facts
            ],
        }
        sys.stdout.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/zenograph-fact-pack-verify/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
