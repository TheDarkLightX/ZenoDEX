#!/usr/bin/env python3
"""Validate the ranked ZenoDEX theorem-to-code ledger.

This validates the ledger's structure and fail-closed research posture.  It does
not decide whether a cited theorem is correct or whether its assumptions apply
to ZenoDEX; those remain explicit review and refinement obligations.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEDGER = ROOT / "docs" / "research" / "ZENODEX_THEOREM_LEDGER_V1.json"
SCHEMA = "zenodex.theorem_ledger.v1"
TIERS = frozenset({"S", "A", "B", "C"})
LOCAL_EVIDENCE_STATUSES = frozenset(
    {
        "proved_in_pr",
        "abstract_cas_lemmas_proved_in_pr",
        "partially_formalized",
        "related_repo_proofs_exist",
        "existence_to_runtime_bridge_open",
    }
)
REQUIRED_ASSURANCE_CHAIN = (
    "unique_authority_bytes",
    "unique_typed_command",
    "immutable_owned_pre_state",
    "pure_total_transition",
    "sound_read_write_footprint",
    "independent_patch_commutation",
    "canonical_join_and_error_order",
    "expected_root_atomic_commit",
    "canonical_receipt_and_trace_commitment",
    "cross_implementation_refinement",
)
REQUIRED_THEOREM_IDS = frozenset(
    {
        "PARSER-UNIQUE-001",
        "PARSER-NORMALIZE-002",
        "ENCODING-INJECTIVE-003",
        "OWNERSHIP-ALIAS-004",
        "REFERENCE-IMMUTABILITY-005",
        "TYPESTATE-LIFECYCLE-006",
        "EFFECT-SOUNDNESS-007",
        "KAHN-DETERMINACY-008",
        "PATCH-COMMUTATION-009",
        "LINEARIZABLE-COMMIT-010",
        "HASH-DOMAIN-011",
        "LIGHTCLIENT-BISECTION-012",
        "CFMM-CHARACTERIZATION-013",
        "FEE-SPLIT-NEUTRALITY-014",
        "WALRAS-EQUILIBRIUM-015",
        "BATCH-DECOMPOSITION-016",
        "DOUBLE-AUCTION-EFFICIENCY-017",
        "SELF-STABILIZATION-018",
    }
)
REQUIRED_IDEA_IDS = frozenset(
    {
        "TYPED-AUTHORITY-PIPELINE",
        "EFFECT-CAPABILITIES",
        "DETERMINISTIC-PARALLEL-PLAN",
        "ATOMIC-CANDIDATE",
        "TRACE-BISECTION",
        "CERTIFIED-WALRAS-SOLVER",
    }
)
REQUIRED_CORRECTION_STATUSES = frozenset(
    {"not_verified_as_stated", "domain_mismatch", "reject_for_consensus_core"}
)


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _text(value: Any, name: str, errors: list[str]) -> str | None:
    if type(value) is not str or not value.strip():
        errors.append(f"{name} must be a non-empty exact string")
        return None
    if value != value.strip():
        errors.append(f"{name} must not have surrounding whitespace")
    return value


def _validate_theorems(raw: Any, errors: list[str], *, root: Path) -> list[dict[str, Any]]:
    theorems = _list(raw, "theorems", errors)
    reports: list[dict[str, Any]] = []
    ids: set[str] = set()
    ranks: set[int] = set()
    seen_lower_tier = False

    for index, raw_item in enumerate(theorems):
        item_errors: list[str] = []
        item = _mapping(raw_item, f"theorems[{index}]", item_errors)
        theorem_id = _text(item.get("id"), f"theorems[{index}].id", item_errors)
        tier = _text(item.get("tier"), f"theorems[{index}].tier", item_errors)
        source = _text(item.get("source"), f"theorems[{index}].source", item_errors)
        _text(item.get("statement"), f"theorems[{index}].statement", item_errors)
        _text(item.get("zenodex_use"), f"theorems[{index}].zenodex_use", item_errors)
        _text(item.get("proof_obligation"), f"theorems[{index}].proof_obligation", item_errors)
        status = _text(item.get("status"), f"theorems[{index}].status", item_errors)

        rank = item.get("rank")
        if type(rank) is not int or rank <= 0:
            item_errors.append(f"theorems[{index}].rank must be a positive exact int")
        elif rank in ranks:
            item_errors.append(f"duplicate theorem rank: {rank}")
        else:
            ranks.add(rank)

        if theorem_id is not None:
            if theorem_id in ids:
                item_errors.append(f"duplicate theorem id: {theorem_id}")
            ids.add(theorem_id)

        if tier not in TIERS:
            item_errors.append(f"theorems[{index}].tier must be one of {sorted(TIERS)}")
        elif tier == "S" and seen_lower_tier:
            item_errors.append("S-tier theorem appears after a lower-tier theorem")
        elif tier != "S":
            seen_lower_tier = True

        if source is not None and not any(
            marker in source for marker in ("DOI:", "arXiv:", "IFIP", "ZenoDEX")
        ):
            item_errors.append(
                "source must contain a DOI, arXiv locator, IFIP locator, or ZenoDEX artifact"
            )

        artifact = item.get("artifact")
        if artifact is not None:
            if (
                type(artifact) is not str
                or not artifact
                or artifact.startswith("/")
                or ".." in artifact.split("/")
            ):
                item_errors.append(
                    "artifact must be a safe non-empty repository-relative path or null"
                )
            elif status in LOCAL_EVIDENCE_STATUSES and not (root / artifact).is_file():
                item_errors.append(f"branch-local artifact does not exist: {artifact}")

        reports.append(
            {
                "id": theorem_id,
                "rank": rank,
                "tier": tier,
                "status": status,
                "ok": not item_errors,
                "errors": item_errors,
            }
        )
        errors.extend(item_errors)

    missing_ids = sorted(REQUIRED_THEOREM_IDS - ids)
    unknown_ids = sorted(ids - REQUIRED_THEOREM_IDS)
    if missing_ids:
        errors.append("missing required theorem ids: " + ",".join(missing_ids))
    if unknown_ids:
        errors.append("unknown theorem ids: " + ",".join(unknown_ids))
    expected_ranks = set(range(1, len(theorems) + 1))
    if ranks != expected_ranks:
        errors.append(
            "theorem ranks must be contiguous from 1: "
            f"expected={sorted(expected_ranks)} actual={sorted(ranks)}"
        )
    return reports


def _validate_ideas(raw: Any, errors: list[str]) -> list[dict[str, Any]]:
    ideas = _list(raw, "ideas", errors)
    ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    for index, raw_item in enumerate(ideas):
        item_errors: list[str] = []
        item = _mapping(raw_item, f"ideas[{index}]", item_errors)
        idea_id = _text(item.get("id"), f"ideas[{index}].id", item_errors)
        tier = _text(item.get("tier"), f"ideas[{index}].tier", item_errors)
        _text(item.get("design"), f"ideas[{index}].design", item_errors)
        if idea_id is not None:
            if idea_id in ids:
                item_errors.append(f"duplicate idea id: {idea_id}")
            ids.add(idea_id)
        if tier not in TIERS:
            item_errors.append(f"ideas[{index}].tier must be one of {sorted(TIERS)}")
        reports.append(
            {"id": idea_id, "tier": tier, "ok": not item_errors, "errors": item_errors}
        )
        errors.extend(item_errors)
    missing = sorted(REQUIRED_IDEA_IDS - ids)
    if missing:
        errors.append("missing required idea ids: " + ",".join(missing))
    return reports


def validate_ledger(
    value: Any,
    *,
    root: Path = ROOT,
    require_reviewed: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "ledger", errors)
    if obj.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")
    if obj.get("claim_status") not in {"research_candidate", "reviewed"}:
        errors.append("claim_status must be research_candidate or reviewed")
    if require_reviewed and obj.get("claim_status") != "reviewed":
        errors.append("review gate requires claim_status=reviewed")
    _text(obj.get("generated_at"), "generated_at", errors)
    _text(obj.get("research_question"), "research_question", errors)

    tiers = _mapping(obj.get("tiers"), "tiers", errors)
    if set(tiers) != TIERS:
        errors.append(f"tiers must define exactly {sorted(TIERS)}")
    for tier in sorted(TIERS):
        _text(tiers.get(tier), f"tiers.{tier}", errors)

    chain = _list(obj.get("assurance_chain"), "assurance_chain", errors)
    if tuple(chain) != REQUIRED_ASSURANCE_CHAIN:
        errors.append("assurance_chain must match the required ordered proof chain exactly")

    theorem_reports = _validate_theorems(obj.get("theorems"), errors, root=root)
    idea_reports = _validate_ideas(obj.get("ideas"), errors)

    corrections = _list(obj.get("citation_corrections"), "citation_corrections", errors)
    correction_statuses: set[str] = set()
    for index, raw_item in enumerate(corrections):
        item = _mapping(raw_item, f"citation_corrections[{index}]", errors)
        _text(item.get("supplied"), f"citation_corrections[{index}].supplied", errors)
        status = _text(item.get("status"), f"citation_corrections[{index}].status", errors)
        _text(item.get("replacement"), f"citation_corrections[{index}].replacement", errors)
        if status is not None:
            correction_statuses.add(status)
    missing_corrections = sorted(REQUIRED_CORRECTION_STATUSES - correction_statuses)
    if missing_corrections:
        errors.append("missing required correction statuses: " + ",".join(missing_corrections))

    non_claims = _list(obj.get("non_claims"), "non_claims", errors)
    if len(non_claims) < 5:
        errors.append("non_claims must contain at least five explicit limitations")
    for index, item in enumerate(non_claims):
        _text(item, f"non_claims[{index}]", errors)

    return {
        "schema": "zenodex.theorem_ledger.validation_report.v1",
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "claim_status": obj.get("claim_status"),
        "theorem_count": len(theorem_reports),
        "idea_count": len(idea_reports),
        "errors": errors,
        "theorems": theorem_reports,
        "ideas": idea_reports,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--require-reviewed", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)
    try:
        value = json.loads(args.ledger.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        report = {
            "schema": "zenodex.theorem_ledger.validation_report.v1",
            "ok": False,
            "status": "rejected",
            "errors": [f"ledger load failed: {exc}"],
        }
    else:
        report = validate_ledger(
            value,
            root=args.root.resolve(),
            require_reviewed=args.require_reviewed,
        )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
