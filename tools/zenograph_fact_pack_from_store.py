#!/usr/bin/env python3
"""Build a reviewed, signed ZenoGraph fact pack from accepted store facts."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import krr_review_record_from_dict  # noqa: E402
from src.agents.zenograph_fact_pack import (  # noqa: E402
    ZENOGRAPH_FACT_PACK_SCHEMA,
    build_zenograph_fact_pack,
    sign_zenograph_fact_pack,
    verify_zenograph_fact_pack_signature,
    zenograph_fact_record_from_accepted_fact,
)
from src.agents.zenograph_schema import ZGFactStatus  # noqa: E402
from src.agents.zenograph_store import ZenoGraphStore  # noqa: E402


def _iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _load_json(path: str | Path) -> object:
    return json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--store-root", required=True)
    ap.add_argument("--pack-name", required=True)
    ap.add_argument("--built-at", help="Optional build timestamp (defaults to now)")
    ap.add_argument("--compiler-version", default="zenograph_fact_pack_from_store_v1")
    ap.add_argument("--review-record-file", action="append", default=[])
    ap.add_argument("--subject-id-prefix", action="append", default=[])
    ap.add_argument("--predicate", action="append", default=[])
    ap.add_argument("--source-id", action="append", default=[])
    ap.add_argument("--signer-privkey", required=True)
    ap.add_argument("--pack-out", required=True)
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def _load_review_rows(paths: list[str]) -> tuple[object, ...]:
    rows = []
    for raw_path in paths:
        obj = _load_json(raw_path)
        if not isinstance(obj, dict):
            raise ValueError(f"review record file must be a JSON object: {raw_path}")
        rows.append(krr_review_record_from_dict(obj))
    return tuple(rows)


def _matches_filters(
    *,
    subject_id: str,
    predicate: str,
    source_id: str,
    subject_prefixes: tuple[str, ...],
    predicates: tuple[str, ...],
    source_ids: tuple[str, ...],
) -> bool:
    if subject_prefixes and not any(subject_id.startswith(prefix) for prefix in subject_prefixes):
        return False
    if predicates and predicate not in predicates:
        return False
    if source_ids and source_id not in source_ids:
        return False
    return True


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        store = ZenoGraphStore(args.store_root)
        subject_prefixes = tuple(str(value) for value in args.subject_id_prefix)
        predicates = tuple(str(value) for value in args.predicate)
        source_ids = tuple(str(value) for value in args.source_id)
        accepted_facts = tuple(
            fact
            for fact in store.iter_facts(status=ZGFactStatus.ACCEPTED)
            if _matches_filters(
                subject_id=fact.subject_id,
                predicate=fact.predicate,
                source_id=fact.source_id,
                subject_prefixes=subject_prefixes,
                predicates=predicates,
                source_ids=source_ids,
            )
        )
        if not accepted_facts:
            raise ValueError("no accepted facts matched the requested export filters")
        facts = tuple(zenograph_fact_record_from_accepted_fact(fact) for fact in accepted_facts)
        review_records = _load_review_rows(list(args.review_record_file))
        pack = build_zenograph_fact_pack(
            pack_name=str(args.pack_name),
            built_at=str(args.built_at or _iso_now()),
            compiler_version=str(args.compiler_version),
            facts=facts,
            review_records=review_records,
        )
        signed_pack = sign_zenograph_fact_pack(pack, privkey=args.signer_privkey)
        if not verify_zenograph_fact_pack_signature(signed_pack):
            raise ValueError("signed fact pack failed self-verification")
        payload = {
            "schema": "zenodex/zenograph-fact-pack-from-store/v1",
            "ok": True,
            "pack_schema": ZENOGRAPH_FACT_PACK_SCHEMA,
            "pack_hash": signed_pack.pack_hash_hex(),
            "runtime_approved": signed_pack.runtime_approved(),
            "counts": {
                "accepted_facts_scanned": len(tuple(store.iter_facts(status=ZGFactStatus.ACCEPTED))),
                "facts_exported": len(signed_pack.facts),
                "review_records": len(signed_pack.review_records),
            },
            "filters": {
                "subject_id_prefix": list(subject_prefixes),
                "predicate": list(predicates),
                "source_id": list(source_ids),
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
            "schema": "zenodex/zenograph-fact-pack-from-store/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
