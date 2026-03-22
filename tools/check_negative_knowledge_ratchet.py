#!/usr/bin/env python3
"""Fail-closed ratchet check for promoted ShapeForge negative knowledge."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.shapeforge_validate import validate_artifact


DEFAULT_NEGATIVE_KNOWLEDGE = (
    ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_negative_knowledge.seed.json"
)
EXPECTED_NEGATIVE_KNOWLEDGE_SCHEMA = "shapeforge/negative-knowledge-seed/v2"

REQUIRES_SCOPED_REPLACEMENT_STATUSES = {
    "narrowed",
}

EXPECTED_NARROWED_HYPOTHESIS_IDS = {
    "exact_out_runtime_order_is_semantic_canonicality_v1",
}

EXPECTED_NARROWED_BASELINES = {
    "exact_out_runtime_order_is_semantic_canonicality_v1": {
        "replacement_claim": "Canonicality comes from minimizing route_key_out = (input_total, leg_count, legs_lex) over complete candidates; the repaired two-pool runtime now reflects that key on the bounded emitted candidate set.",
        "replay_pointer": "docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json#scenario_id=drop_exact_out_canonical_minimizer_tie_break",
        "remaining_excluded_domain": "Candidate domains outside the repaired bounded emitted set remain excluded: stable runtime enumeration is still not a semantic canonicality argument without explicit total-key minimization plus candidate completeness.",
    }
}


def check_negative_knowledge_ratchet(
    *,
    negative_knowledge_path: Path = DEFAULT_NEGATIVE_KNOWLEDGE,
) -> dict[str, Any]:
    errors = validate_artifact(negative_knowledge_path)
    if errors:
        raise ValueError("\n".join(errors))

    data = json.loads(negative_knowledge_path.read_text(encoding="utf-8"))
    schema = str(data.get("schema") or "").strip()
    if schema != EXPECTED_NEGATIVE_KNOWLEDGE_SCHEMA:
        raise ValueError(
            f"{negative_knowledge_path}: schema {schema!r} != {EXPECTED_NEGATIVE_KNOWLEDGE_SCHEMA!r}"
        )

    records = data["records"]

    narrowed_ids: list[str] = []
    for record in records:
        hypothesis_id = str(record["hypothesis_id"])
        status = str(record["status"])
        if status not in REQUIRES_SCOPED_REPLACEMENT_STATUSES:
            continue

        narrowed_ids.append(hypothesis_id)

        replacement_claim = str(record.get("replacement_claim") or "").strip()
        replay_pointer = str(record.get("replay_pointer") or "").strip()
        remaining_excluded_domain = str(record.get("remaining_excluded_domain") or "").strip()
        claim = str(record.get("claim") or "").strip()

        if not replacement_claim:
            errors.append(f"{negative_knowledge_path}: record {hypothesis_id} missing replacement_claim")
        elif replacement_claim == claim:
            errors.append(
                f"{negative_knowledge_path}: record {hypothesis_id} replacement_claim must narrow or replace the original claim"
            )

        if not replay_pointer:
            errors.append(f"{negative_knowledge_path}: record {hypothesis_id} missing replay_pointer")

        if not remaining_excluded_domain:
            errors.append(
                f"{negative_knowledge_path}: record {hypothesis_id} missing remaining_excluded_domain"
            )

        expected_fields = EXPECTED_NARROWED_BASELINES.get(hypothesis_id)
        if expected_fields is None:
            errors.append(
                f"{negative_knowledge_path}: record {hypothesis_id} missing pinned narrowed baseline"
            )
        else:
            for field_name, expected_value in expected_fields.items():
                actual_value = str(record.get(field_name) or "").strip()
                if actual_value != expected_value:
                    errors.append(
                        f"{negative_knowledge_path}: record {hypothesis_id} field {field_name} drifted from pinned baseline"
                    )

    if errors:
        raise ValueError("\n".join(errors))

    actual_narrowed_ids = set(narrowed_ids)
    if actual_narrowed_ids != EXPECTED_NARROWED_HYPOTHESIS_IDS:
        raise ValueError(
            f"{negative_knowledge_path}: narrowed hypothesis ids {sorted(actual_narrowed_ids)} != "
            f"{sorted(EXPECTED_NARROWED_HYPOTHESIS_IDS)}"
        )

    return {
        "ok": True,
        "negative_knowledge_path": str(negative_knowledge_path),
        "expected_schema": EXPECTED_NEGATIVE_KNOWLEDGE_SCHEMA,
        "narrowed_count": len(narrowed_ids),
        "narrowed_hypothesis_ids": narrowed_ids,
        "expected_narrowed_hypothesis_ids": sorted(EXPECTED_NARROWED_HYPOTHESIS_IDS),
        "expected_narrowed_baselines": EXPECTED_NARROWED_BASELINES,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Fail-closed negative-knowledge ratchet check.")
    parser.add_argument(
        "--negative-knowledge-path",
        type=Path,
        default=DEFAULT_NEGATIVE_KNOWLEDGE,
        help="Path to the promoted negative-knowledge artifact",
    )
    args = parser.parse_args()

    report = check_negative_knowledge_ratchet(
        negative_knowledge_path=args.negative_knowledge_path.resolve(),
    )
    print(
        "OK NEGATIVE_KNOWLEDGE "
        f"narrowed={report['narrowed_count']} "
        + ",".join(report["narrowed_hypothesis_ids"])
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
