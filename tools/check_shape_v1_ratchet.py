#!/usr/bin/env python3
"""Fail-closed ratchet check for the current SHAPE_V1 baseline."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.shapeforge_target_shape_eval import evaluate_target_shapes
from tools.shapeforge_validate import validate_artifact


DEFAULT_TARGET_SHAPES = ROOT / "docs" / "zenodex" / "shapeforge_promoted" / "zenodex_target_shapes.seed.json"
DEFAULT_MANIFEST = ROOT / "docs" / "zenodex" / "SHAPE_V1.md"

EXPECTED_COUNTS = {
    "shape_pp_candidate_v1": {"support_count": 10, "blocked_count": 0},
    "dex_kernel_candidate_v1": {"support_count": 6, "blocked_count": 0},
    "runtime_boundary_candidate_v1": {"support_count": 5, "blocked_count": 0},
}

REQUIRED_CLAUSE_IDS = {
    "cbc_validity",
    "unique_canonical_winner_everywhere",
    "exact_fee_aware_accounting",
    "value_aware_settlement_safety",
    "proof_carrying_optimizer_certificates",
    "anti_fragmentation_by_theorem",
    "non_commutativity_quarantine",
    "oracle_divergence_safety",
    "liquidation_spiral_containment",
    "cross_layer_replay_parity",
}


def _check_manifest(path: Path) -> list[str]:
    errors: list[str] = []
    if not path.exists():
        return [f"missing manifest: {path}"]
    text = path.read_text(encoding="utf-8")
    if "`D_v1`" not in text:
        errors.append(f"{path}: missing audited-domain D_v1 scope marker")
    for clause_id in sorted(REQUIRED_CLAUSE_IDS):
        if f"`{clause_id}`" not in text:
            errors.append(f"{path}: missing clause manifest entry for {clause_id}")
    return errors


def check_shape_v1_ratchet(
    *,
    target_shapes_path: Path = DEFAULT_TARGET_SHAPES,
    manifest_path: Path = DEFAULT_MANIFEST,
) -> dict[str, Any]:
    errors: list[str] = []

    errors.extend(validate_artifact(target_shapes_path))
    errors.extend(_check_manifest(manifest_path))
    if errors:
        raise ValueError("\n".join(errors))

    report = evaluate_target_shapes(target_shapes_path)
    result_by_id = {result["target_shape_id"]: result for result in report["results"]}
    for target_shape_id, expected in EXPECTED_COUNTS.items():
        result = result_by_id.get(target_shape_id)
        if result is None:
            raise ValueError(f"missing target shape result for {target_shape_id}")
        support_count = int(result["support_count"])
        blocked_count = int(result["blocked_count"])
        gap_count = int(result["gap_count"])
        if support_count != int(expected["support_count"]):
            raise ValueError(
                f"{target_shape_id}: support_count {support_count} != {expected['support_count']}"
            )
        if blocked_count != int(expected["blocked_count"]):
            raise ValueError(
                f"{target_shape_id}: blocked_count {blocked_count} != {expected['blocked_count']}"
            )
        if gap_count != 0:
            raise ValueError(f"{target_shape_id}: gap_count {gap_count} != 0")

    return {
        "ok": True,
        "target_shapes_path": str(target_shapes_path),
        "manifest_path": str(manifest_path),
        "expected_counts": EXPECTED_COUNTS,
        "results": report["results"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Fail-closed SHAPE_V1 ratchet check.")
    parser.add_argument(
        "--target-shapes-path",
        type=Path,
        default=DEFAULT_TARGET_SHAPES,
        help="Path to the promoted target-shapes artifact",
    )
    parser.add_argument(
        "--manifest-path",
        type=Path,
        default=DEFAULT_MANIFEST,
        help="Path to the SHAPE_V1 manifest",
    )
    args = parser.parse_args()

    report = check_shape_v1_ratchet(
        target_shapes_path=args.target_shapes_path.resolve(),
        manifest_path=args.manifest_path.resolve(),
    )
    print(
        "OK SHAPE_V1 "
        + " ".join(
            f"{result['target_shape_id']}={result['support_count']}/{result['clause_count']}"
            for result in report["results"]
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
