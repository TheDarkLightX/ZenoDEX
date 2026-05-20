#!/usr/bin/env python3
"""Build a reviewed, signed ZenoGraph fact pack for advisory runtime use."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import krr_review_record_from_dict  # noqa: E402
from src.agents.zenograph_fact_pack import (  # noqa: E402
    ZENOGRAPH_FACT_PACK_SCHEMA,
    build_zenograph_fact_pack,
    sign_zenograph_fact_pack,
    verify_zenograph_fact_pack_signature,
    zenograph_fact_record_from_dict,
)


def _iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _load_json(path: str | Path) -> Any:
    return json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--pack-name", required=True)
    ap.add_argument("--built-at", help="Optional build timestamp (defaults to now)")
    ap.add_argument("--compiler-version", default="zenograph_fact_pack_build_v1")
    ap.add_argument("--fact-file", action="append", default=[])
    ap.add_argument("--review-record-file", action="append", default=[])
    ap.add_argument("--parent-pack-file")
    ap.add_argument("--signer-privkey", required=True)
    ap.add_argument("--pack-out", required=True)
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def _load_rows(paths: list[str], *, loader, name: str) -> tuple[Any, ...]:
    rows = []
    for raw_path in paths:
        obj = _load_json(raw_path)
        if not isinstance(obj, Mapping):
            raise ValueError(f"{name} file must be a JSON object: {raw_path}")
        rows.append(loader(obj))
    return tuple(rows)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        facts = _load_rows(
            list(args.fact_file),
            loader=zenograph_fact_record_from_dict,
            name="fact record",
        )
        review_records = _load_rows(
            list(args.review_record_file),
            loader=krr_review_record_from_dict,
            name="review record",
        )
        parent_pack_hash = None
        if args.parent_pack_file:
            parent_obj = _load_json(args.parent_pack_file)
            if not isinstance(parent_obj, Mapping):
                raise ValueError("parent pack file must be a JSON object")
            parent_pack_hash = str(parent_obj.get("pack_hash") or "").strip() or None
        pack = build_zenograph_fact_pack(
            pack_name=str(args.pack_name),
            built_at=str(args.built_at or _iso_now()),
            compiler_version=str(args.compiler_version),
            facts=facts,
            review_records=review_records,
            parent_pack_hash=parent_pack_hash,
        )
        signed_pack = sign_zenograph_fact_pack(pack, privkey=args.signer_privkey)
        if not verify_zenograph_fact_pack_signature(signed_pack):
            raise ValueError("signed fact pack failed self-verification")
        payload = {
            "schema": "zenodex/zenograph-fact-pack-build/v1",
            "ok": True,
            "pack_schema": ZENOGRAPH_FACT_PACK_SCHEMA,
            "pack_hash": signed_pack.pack_hash_hex(),
            "runtime_approved": signed_pack.runtime_approved(),
            "counts": {
                "facts": len(signed_pack.facts),
                "review_records": len(signed_pack.review_records),
            },
            "pack": signed_pack.to_dict(),
        }
        text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stdout.write(text)
        pack_out = Path(args.pack_out).expanduser().resolve()
        pack_out.parent.mkdir(parents=True, exist_ok=True)
        pack_out.write_text(
            json.dumps(signed_pack.to_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/zenograph-fact-pack-build/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
