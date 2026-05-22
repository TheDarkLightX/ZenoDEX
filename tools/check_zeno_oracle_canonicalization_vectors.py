#!/usr/bin/env python3
"""Check public ZenoOracle canonicalization vectors."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_VECTOR_FILE = REPO_ROOT / "docs" / "zeno_oracle" / "canonicalization_vectors_v1.json"


def _canonical_json(payload: Mapping[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _semantic_hash(domain: str, payload: Mapping[str, Any]) -> str:
    canonical = _canonical_json(payload)
    digest = hashlib.sha256(domain.encode("utf-8") + b"\x00" + canonical.encode("utf-8")).hexdigest()
    return "sha256:" + digest


def check_vectors(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    errors: list[str] = []
    vectors = data.get("vectors")
    if not isinstance(vectors, list) or not vectors:
        errors.append("vectors must be a non-empty list")
        vectors = []
    seen_ids: set[str] = set()
    for index, vector in enumerate(vectors):
        if not isinstance(vector, dict):
            errors.append(f"vector[{index}] must be an object")
            continue
        vector_id = vector.get("id")
        if not isinstance(vector_id, str) or not vector_id:
            errors.append(f"vector[{index}] missing id")
            vector_id = f"index:{index}"
        if vector_id in seen_ids:
            errors.append(f"duplicate vector id: {vector_id}")
        seen_ids.add(vector_id)
        domain = vector.get("domain")
        payload = vector.get("payload")
        expected_canonical = vector.get("canonical_json")
        expected_hash = vector.get("expected_hash")
        if not isinstance(domain, str) or not domain:
            errors.append(f"{vector_id} domain must be a non-empty string")
            continue
        if not isinstance(payload, dict):
            errors.append(f"{vector_id} payload must be an object")
            continue
        actual_canonical = _canonical_json(payload)
        actual_hash = _semantic_hash(domain, payload)
        if expected_canonical != actual_canonical:
            errors.append(f"{vector_id} canonical_json mismatch")
        if expected_hash != actual_hash:
            errors.append(f"{vector_id} expected_hash mismatch")
    return {
        "schema": "zenodex.oracle.canonicalization_vector_check.v1",
        "ok": not errors,
        "vector_file": str(path),
        "vector_count": len(vectors),
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="check_zeno_oracle_canonicalization_vectors.py")
    parser.add_argument("vector_file", nargs="?", default=str(DEFAULT_VECTOR_FILE))
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    result = check_vectors(Path(args.vector_file))
    if args.json:
        print(json.dumps(result, sort_keys=True))
    elif result["ok"]:
        print(f"ok: {result['vector_count']} vectors")
    else:
        for error in result["errors"]:
            print(error, file=sys.stderr)
    return 0 if result["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
