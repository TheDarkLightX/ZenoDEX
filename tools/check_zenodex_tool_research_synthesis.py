#!/usr/bin/env python3
"""Validate the Research Kernel, Morph, and ESSO ZenoDEX synthesis ledger."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEDGER = ROOT / "docs" / "research" / "ZENODEX_RK_MORPH_ESSO_SYNTHESIS_V1.json"
SCHEMA = "zenodex.rk_morph_esso_synthesis.v1"
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")

REQUIRED_TOOL_IDS = frozenset({"research_kernel", "morph", "esso"})
REQUIRED_REFUTATIONS = frozenset(
    {"claim_disjoint_writes_suffice", "claim_any_matching_is_canonical"}
)
REQUIRED_ESSO_QUERIES = frozenset(
    {
        "init_implies_inv",
        "inductive_prepare",
        "inductive_worker_fail",
        "inductive_reject_stale_or_invalid",
        "inductive_commit_atomic",
        "inductive_deliver",
    }
)
REQUIRED_DECISIONS = frozenset(
    {
        "instrument_and_certify_dynamic_footprint_containment_before_value_moving_parallelism",
        "implement_one_atomic_candidate_commit_boundary",
        "model_remaining_zusd_lifecycles_separately_then_compose",
        "generate_typed_authority_parsers_from_one_grammar",
        "admit_matching_or_flow_only_through_a_canonical_finite_certificate",
    }
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


def _string(value: Any, name: str, errors: list[str]) -> str | None:
    if type(value) is not str or not value:
        errors.append(f"{name} must be a non-empty exact string")
        return None
    if value != value.strip():
        errors.append(f"{name} must not have surrounding whitespace")
    return value


def _match(value: Any, pattern: re.Pattern[str], name: str, errors: list[str]) -> None:
    parsed = _string(value, name, errors)
    if parsed is not None and pattern.fullmatch(parsed) is None:
        errors.append(f"{name} has invalid format")


def validate_synthesis(value: Any, *, root: Path = ROOT) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "ledger", errors)
    if obj.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")
    if obj.get("authority") != "research_evidence_only":
        errors.append("authority must remain research_evidence_only")

    parent = _mapping(obj.get("parent"), "parent", errors)
    _match(parent.get("head_sha"), SHA_RE, "parent.head_sha", errors)
    if type(parent.get("pr")) is not int or int(parent.get("pr", 0)) <= 0:
        errors.append("parent.pr must be a positive exact int")

    tools = _mapping(obj.get("tool_sources"), "tool_sources", errors)
    if set(tools) != REQUIRED_TOOL_IDS:
        errors.append(f"tool_sources must contain exactly {sorted(REQUIRED_TOOL_IDS)}")
    for tool_id in sorted(REQUIRED_TOOL_IDS):
        tool = _mapping(tools.get(tool_id), f"tool_sources.{tool_id}", errors)
        _string(tool.get("repository"), f"tool_sources.{tool_id}.repository", errors)
        _match(tool.get("source_sha"), SHA_RE, f"tool_sources.{tool_id}.source_sha", errors)
        _match(
            tool.get("study_head_sha"),
            SHA_RE,
            f"tool_sources.{tool_id}.study_head_sha",
            errors,
        )
        _match(
            tool.get("artifact_digest"),
            DIGEST_RE,
            f"tool_sources.{tool_id}.artifact_digest",
            errors,
        )
        if tool.get("workflow_conclusion") != "success":
            errors.append(f"tool_sources.{tool_id}.workflow_conclusion must be success")
        for int_field in ("pull_request", "workflow_run"):
            if type(tool.get(int_field)) is not int or int(tool.get(int_field, 0)) <= 0:
                errors.append(f"tool_sources.{tool_id}.{int_field} must be a positive exact int")

    rk = _mapping(obj.get("research_kernel_result"), "research_kernel_result", errors)
    if rk.get("supported_scoped_claim") != "claim_typed_parser_boundary":
        errors.append("Research Kernel scoped promotion changed")
    refuted = frozenset(_list(rk.get("refuted_overbroad_claims"), "refuted_overbroad_claims", errors))
    if refuted != REQUIRED_REFUTATIONS:
        errors.append("Research Kernel refuted claim set mismatch")

    morph = _mapping(obj.get("morph_result"), "morph_result", errors)
    if morph.get("all_candidates_promotable") is not False:
        errors.append("Morph candidates must remain non-promotable")
    if morph.get("problem_count") != 5:
        errors.append("Morph problem_count must remain 5")
    reformulations = _list(
        morph.get("top_cross_problem_reformulations"),
        "morph_result.top_cross_problem_reformulations",
        errors,
    )
    if len(reformulations) < 4:
        errors.append("at least four cross-problem reformulations are required")

    esso = _mapping(obj.get("esso_result"), "esso_result", errors)
    naive = _mapping(esso.get("naive_model"), "esso_result.naive_model", errors)
    repaired = _mapping(esso.get("repaired_model"), "esso_result.repaired_model", errors)
    if naive.get("verdict") != "FAILED":
        errors.append("naive ESSO model must remain FAILED")
    if repaired.get("verdict") != "VERIFIED":
        errors.append("repaired ESSO model must remain VERIFIED")
    _match(naive.get("fingerprint"), SHA256_RE, "naive_model.fingerprint", errors)
    _match(repaired.get("fingerprint"), SHA256_RE, "repaired_model.fingerprint", errors)
    if naive.get("counterexample_query") != "inductive_publish_state":
        errors.append("naive counterexample query mismatch")
    projection = _mapping(
        naive.get("counterexample_projection"),
        "naive_model.counterexample_projection",
        errors,
    )
    publication_flags = (
        projection.get("post_state_published"),
        projection.get("post_effects_published"),
        projection.get("post_receipt_published"),
        projection.get("post_outbox_published"),
    )
    if publication_flags != (True, False, False, False):
        errors.append("naive counterexample must exhibit state-only partial publication")
    repaired_queries = frozenset(_list(repaired.get("queries"), "repaired_model.queries", errors))
    if repaired_queries != REQUIRED_ESSO_QUERIES:
        errors.append("repaired ESSO query set mismatch")

    formal = _mapping(obj.get("new_formal_result"), "new_formal_result", errors)
    artifact = _string(formal.get("artifact"), "new_formal_result.artifact", errors)
    if artifact is not None:
        path = Path(artifact)
        if path.is_absolute() or ".." in path.parts:
            errors.append("new_formal_result.artifact must be a safe repository-relative path")
        elif not (root / path).is_file():
            errors.append(f"new formal artifact does not exist: {artifact}")

    decisions = _list(obj.get("decisions"), "decisions", errors)
    decision_ids: set[str] = set()
    priorities: set[int] = set()
    for index, raw in enumerate(decisions):
        item = _mapping(raw, f"decisions[{index}]", errors)
        decision = _string(item.get("decision"), f"decisions[{index}].decision", errors)
        _string(item.get("promotion_gate"), f"decisions[{index}].promotion_gate", errors)
        priority = item.get("priority")
        if type(priority) is not int or priority <= 0:
            errors.append(f"decisions[{index}].priority must be a positive exact int")
        elif priority in priorities:
            errors.append(f"duplicate decision priority: {priority}")
        else:
            priorities.add(priority)
        if decision is not None:
            if decision in decision_ids:
                errors.append(f"duplicate decision id: {decision}")
            decision_ids.add(decision)
    if decision_ids != REQUIRED_DECISIONS:
        errors.append("decision set mismatch")
    if priorities != set(range(1, len(decisions) + 1)):
        errors.append("decision priorities must be contiguous from 1")

    nonclaims = _list(obj.get("nonclaims"), "nonclaims", errors)
    if len(nonclaims) < 6:
        errors.append("at least six explicit nonclaims are required")
    for index, item in enumerate(nonclaims):
        _string(item, f"nonclaims[{index}]", errors)

    return {
        "schema": "zenodex.rk_morph_esso_synthesis.validation_report.v1",
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "tool_count": len(tools),
        "decision_count": len(decisions),
        "nonclaim_count": len(nonclaims),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)
    try:
        value = json.loads(args.ledger.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        report = {
            "schema": "zenodex.rk_morph_esso_synthesis.validation_report.v1",
            "ok": False,
            "status": "rejected",
            "errors": [f"ledger load failed: {exc}"],
        }
    else:
        report = validate_synthesis(value, root=args.root.resolve())
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
