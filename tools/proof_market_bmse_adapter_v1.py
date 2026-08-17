#!/usr/bin/env python3
"""Evaluate ZenoProof candidates with BMSE's certified Pareto primitive.

BMSE's stock evaluator has generic SaaS/marketplace/fintech dimensions. This
adapter preserves ZenoProof's exact domain simulation and uses BMSE only for
frontier admission and decision-certificate construction. The receipt is
advisory, research-only, and grants no economic or proof authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import types
from pathlib import Path
from typing import Any, Final

SCHEMA: Final = "zenodex/proof-market-bmse-evaluation/v1"
EXPECTED_INPUT_SCHEMA: Final = "zenodex/proof-market-business-model/v1"
BMSE_SOURCE_PATHS: Final = (
    "bmse_runtime/core.py",
    "tools/bmse_runtime_explore.py",
    "bmse_refine/family_profiles.json",
    "bmse_refine/objective_profiles.json",
)


def _canonical_bytes(value: object) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _canonical_compact_bytes(value: object) -> bytes:
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode("utf-8")


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _git_head(repo_root: Path) -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError(f"JSON root must be an object: {path}")
    return raw


def _bmse_source_snapshot(bmse_root: Path) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    for relative_path in BMSE_SOURCE_PATHS:
        path = bmse_root / relative_path
        if not path.is_file():
            raise ValueError(f"missing BMSE source: {relative_path}")
        result[relative_path] = path.read_bytes()
    return result


def _bmse_source_pins(snapshot: dict[str, bytes]) -> list[dict[str, str]]:
    return [
        {"path": relative_path, "sha256": _sha256(snapshot[relative_path])}
        for relative_path in BMSE_SOURCE_PATHS
    ]


def _load_bmse_core(*, bmse_root: Path, source: bytes) -> types.ModuleType:
    source_path = bmse_root / "bmse_runtime/core.py"
    module_name = f"_zenodex_bmse_core_{_sha256(source)[:16]}"
    module = types.ModuleType(module_name)
    module.__file__ = str(source_path)
    sys.modules[module_name] = module
    exec(compile(source, str(source_path), "exec"), module.__dict__)  # noqa: S102
    return module


def _generic_baseline_summary(path: Path | None) -> dict[str, Any] | None:
    if path is None:
        return None
    payload = _load_json(path)
    top_candidates = payload.get("top_candidates")
    records = payload.get("records")
    if not isinstance(top_candidates, list) or not top_candidates:
        raise ValueError("BMSE generic baseline has no top candidate")
    if not isinstance(records, list):
        raise ValueError("BMSE generic baseline has no records")
    top_fingerprint = top_candidates[0].get("candidate_fingerprint")
    top_record = next(
        (
            row
            for row in records
            if isinstance(row, dict)
            and row.get("candidate_fingerprint") == top_fingerprint
        ),
        None,
    )
    if not isinstance(top_record, dict):
        raise ValueError("BMSE generic top candidate record is missing")
    return {
        "sha256": _sha256(path.read_bytes()),
        "ok": payload.get("ok"),
        "grid_profile": payload.get("grid_profile"),
        "objective_profile": (
            payload.get("objective_profile", {}).get("id")
            if isinstance(payload.get("objective_profile"), dict)
            else None
        ),
        "candidate_count": payload.get("candidate_count"),
        "eligible_count": payload.get("eligible_count"),
        "top_candidate": top_record.get("z"),
        "top_objectives": top_record.get("objectives"),
        "interpretation": (
            "The stock BMSE grid preferred a subscription, self-serve, two-sided "
            "network row under its generic priors. It cannot choose ZenoProof fees "
            "because proof verification, counterexamples, reuse, ZRPF, and token "
            "reserve dimensions are absent."
        ),
    }


def _evaluate_frontier(
    *,
    evaluations: list[dict[str, Any]],
    input_sha256: str,
    core: types.ModuleType,
) -> tuple[list[dict[str, Any]], tuple[Any, ...]]:
    frontier: tuple[Any, ...] = ()
    rows: list[dict[str, Any]] = []
    for evaluation in sorted(evaluations, key=lambda row: str(row["candidate_id"])):
        candidate_id = str(evaluation["candidate_id"])
        fingerprint = _sha256(
            _canonical_compact_bytes(
                {
                    "candidate_id": candidate_id,
                    "evaluation": evaluation,
                    "input_sha256": input_sha256,
                }
            )
        )
        point = core.FrontierPoint(
            candidate_fingerprint=fingerprint,
            objectives={
                "expected_npv": float(
                    int(evaluation["expected_monthly_surplus_after_bonus_atoms"])
                    * 24
                ),
                "p_npv_gt_0": int(evaluation["probability_positive_bps"])
                / 10_000.0,
                "neg_cvar_0_95_loss": float(
                    -int(evaluation["worst_monthly_loss_atoms"])
                ),
                "neg_complexity": float(
                    int(evaluation["negative_complexity_units"])
                ),
            },
            hard_ok=bool(evaluation["manipulation_safe"]),
            chance_ok=int(evaluation["probability_positive_bps"]) >= 6_000,
        )
        decision = core.frontier_step(frontier, point)
        if not core.verify_decision_certificate(decision.certificate):
            raise AssertionError("BMSE frontier decision certificate does not verify")
        frontier = decision.frontier
        rows.append(
            {
                "candidate_id": candidate_id,
                "candidate_fingerprint": fingerprint,
                "objectives": point.objectives,
                "hard_ok": point.hard_ok,
                "chance_ok": point.chance_ok,
                "accepted": decision.accepted,
                "reason": decision.reason,
                "dominated_by": list(decision.dominated_by),
                "removed": list(decision.removed),
                "certificate": {
                    "kind": decision.certificate.certificate_kind,
                    "payload_json": decision.certificate.payload_json,
                    "payload_hash": decision.certificate.payload_hash,
                },
            }
        )
    return rows, frontier


def build_receipt(
    *,
    input_path: Path,
    bmse_root: Path,
    generic_baseline_path: Path | None,
) -> dict[str, Any]:
    input_payload = _load_json(input_path)
    if input_payload.get("schema") != EXPECTED_INPUT_SCHEMA:
        raise ValueError("unexpected ZenoProof business-model schema")
    business_model = input_payload.get("bounded_model", {}).get("business_model")
    if not isinstance(business_model, dict):
        raise ValueError("input lacks bounded_model.business_model")
    evaluations = business_model.get("evaluations")
    if not isinstance(evaluations, list) or not evaluations:
        raise ValueError("input has no candidate evaluations")

    input_bytes = input_path.read_bytes()
    input_sha256 = _sha256(input_bytes)
    bmse_snapshot = _bmse_source_snapshot(bmse_root)
    core = _load_bmse_core(
        bmse_root=bmse_root,
        source=bmse_snapshot["bmse_runtime/core.py"],
    )
    rows, frontier = _evaluate_frontier(
        evaluations=evaluations,
        input_sha256=input_sha256,
        core=core,
    )
    for relative_path, source in bmse_snapshot.items():
        if (bmse_root / relative_path).read_bytes() != source:
            raise ValueError(f"BMSE source changed during evaluation: {relative_path}")
    by_fingerprint = {
        row["candidate_fingerprint"]: row["candidate_id"] for row in rows
    }
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_ADVISORY",
        "input": {
            "schema": input_payload["schema"],
            "sha256": input_sha256,
        },
        "bmse": {
            "repository": "TheDarkLightX/BMSE",
            "commit": _git_head(bmse_root),
            "source_pins": _bmse_source_pins(bmse_snapshot),
            "generic_marketplace_baseline": _generic_baseline_summary(
                generic_baseline_path
            ),
        },
        "objective_mapping": {
            "expected_npv": (
                "24 * exact expected monthly contribution after bootstrap bonus; "
                "undiscounted proxy, not accounting NPV"
            ),
            "p_npv_gt_0": "exact scenario weight with positive monthly cash surplus",
            "neg_cvar_0_95_loss": "negative worst modeled monthly cash loss proxy",
            "neg_complexity": "negative ordinal feature-complexity units",
            "hard_ok": "buyer-seller raw-volume coalition attack is not profitable in the bounded rule",
            "chance_ok": "positive monthly cash surplus in at least 6000 bps of scenario weight",
        },
        "rows": rows,
        "frontier_candidate_ids": [
            by_fingerprint[point.candidate_fingerprint] for point in frontier
        ],
        "certificate_ok": True,
        "promotion_boundary": {
            "claim": "BMSE replayed exact Pareto admission over ZenoProof's domain evaluations.",
            "nonclaims": [
                "The mapped expected_npv field is an undiscounted contribution proxy.",
                "BMSE did not verify ZenoProof economic assumptions or forecast demand.",
                "The certificate authenticates a deterministic decision payload, not its real-world premises.",
                "This receipt grants no payment, token, proof, settlement, finality, or release authority.",
            ],
            "selected": False,
            "production_ready": False,
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--bmse-root", required=True)
    parser.add_argument("--generic-baseline")
    parser.add_argument("--output", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    try:
        receipt = build_receipt(
            input_path=Path(args.input).resolve(),
            bmse_root=Path(args.bmse_root).resolve(),
            generic_baseline_path=(
                Path(args.generic_baseline).resolve()
                if args.generic_baseline
                else None
            ),
        )
        output_path = Path(args.output).resolve()
        expected = _canonical_bytes(receipt)
        if args.write:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_bytes(expected)
        actual = output_path.read_bytes() if output_path.is_file() else b""
        ok = actual == expected
        report = {
            "schema": SCHEMA,
            "ok": ok,
            "output": str(output_path),
            "sha256": _sha256(expected),
            "frontier_candidate_ids": receipt["frontier_candidate_ids"],
            "selected": False,
            "production_ready": False,
        }
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0 if ok else 2
    except Exception as exc:
        print(json.dumps({"schema": SCHEMA, "ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
