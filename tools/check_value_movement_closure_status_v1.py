#!/usr/bin/env python3
"""Fail-closed checker for the value-movement semantic closure ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STATUS_PATH = Path(
    "docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_STATUS_V1.json"
)
M6_ATDD_PATH = Path("docs/research/m6_global_economic_core_atdd_bdd_v1.json")
EXPECTED_GATE_IDS = tuple(f"VM-{index:02d}" for index in range(1, 13))
EXPECTED_SEMANTIC_KEYS = frozenset(
    {
        "asset_precision",
        "autonomous_governance",
        "buy_and_burn",
        "buy_and_burn_exclusions",
        "external_registry_default",
        "hosting_compensation",
        "hyperdeflation",
        "rescaling",
        "self_custody_language",
    }
)
EXPECTED_BUY_AND_BURN = (
    "Atomically spend the governed quote-asset fee allocation through the "
    "selected authenticated Spot route and burn the exact ZDEX atoms received."
)
EXPECTED_HYPERDEFLATION = (
    "No arbitrary fixed percentage of initial supply is required as a floor. "
    "Bind a retained-supply rule such as R(S)=ceil(p*S/q), 0<p<q, and "
    "burn<=S-R(S)."
)
EXPECTED_M6_ZDEX_PRODUCTION_RULE = (
    "Only the exact ZDEX atoms produced by atomically spending a governed "
    "quote-asset fee allocation through the selected authenticated Spot route "
    "may burn. Each burn preserves R(S)=ceil(p*S/q), with 0<p<q and "
    "burn<=S-R(S); no fixed initial-supply percentage floor is authoritative."
)


def _object_without_duplicate_keys(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_exact_json(path: Path) -> Mapping[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_object_without_duplicate_keys,
    )
    if type(value) is not dict:
        raise TypeError("closure status root must be an object")
    return value


def _mapping(value: object, name: str, findings: list[str]) -> Mapping[str, object]:
    if type(value) is not dict:
        findings.append(f"{name} must be an object")
        return {}
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_m6_zdex_semantic_anchor_v1(value: object) -> list[str]:
    """Reject the historical fixed-floor or shortcut-burn M6 semantics."""

    if type(value) is not dict:
        return ["M6 ATDD contract must be an object"]
    policies = value.get("managed_asset_policy")
    if type(policies) is not list or any(type(policy) is not dict for policy in policies):
        return ["M6 ATDD managed_asset_policy must be a list of objects"]
    zdex_rows = [
        policy for policy in policies if policy.get("asset_class") == "zdex_protocol_token"
    ]
    if len(zdex_rows) != 1:
        return ["M6 ATDD must contain exactly one ZDEX managed-asset policy"]
    row = zdex_rows[0]
    findings: list[str] = []
    if row.get("burn_authority") != "fee-funded protocol buy-and-burn transition":
        findings.append("M6 ATDD ZDEX burn authority drift")
    if row.get("production_rule") != EXPECTED_M6_ZDEX_PRODUCTION_RULE:
        findings.append("M6 ATDD ZDEX retained-supply or purchase-and-burn drift")
    return findings


def check_value_movement_closure_status_v1(
    root: Path = REPO_ROOT,
    status_path: Path | None = None,
) -> dict[str, object]:
    findings: list[str] = []
    source = status_path or root / DEFAULT_STATUS_PATH
    try:
        status = _load_exact_json(source)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        return {
            "schema": "zenodex/value-movement-closure-status-check/v1",
            "ok": False,
            "findings": [f"status ledger cannot be loaded: {type(exc).__name__}: {exc}"],
        }

    if status.get("schema") != "zenodex/value-movement-closure-status/v1":
        findings.append("closure status schema mismatch")

    subject = _mapping(status.get("subject"), "subject", findings)
    commit = subject.get("commit")
    if type(commit) is not str or re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        findings.append("subject commit must be exact lowercase 40-hex")
    if subject.get("scoped_worktree_clean_before_this_ledger") is not True:
        findings.append("ledger subject was not recorded from a clean scoped worktree")

    authority = _mapping(status.get("authority"), "authority", findings)
    expected_authority: dict[str, object] = {
        "claim_authority": "NONE",
        "production_authority": "NONE",
        "production_ready": False,
        "release_ready": False,
    }
    if dict(authority) != expected_authority:
        findings.append("authority or readiness nonclaim drift")

    claim = _mapping(status.get("claim_contract"), "claim contract", findings)
    claim_path = claim.get("path")
    claim_sha = claim.get("sha256")
    if type(claim_path) is not str or type(claim_sha) is not str:
        findings.append("claim contract path and sha256 must be strings")
    else:
        resolved_claim = root / claim_path
        if not resolved_claim.is_file() or _sha256(resolved_claim) != claim_sha:
            findings.append("claim contract hash mismatch")
    if claim.get("status") != "DRAFT_REVISED_AFTER_MAX_REVIEW":
        findings.append("claim status drift")
    if claim.get("verdict") != "UNPROVED":
        findings.append("claim verdict must remain UNPROVED")

    semantics = _mapping(status.get("semantic_anchors"), "semantic anchors", findings)
    if frozenset(semantics) != EXPECTED_SEMANTIC_KEYS:
        findings.append("semantic anchor key set mismatch")
    if semantics.get("buy_and_burn") != EXPECTED_BUY_AND_BURN:
        findings.append("buy-and-burn semantic anchor drift")
    if semantics.get("hyperdeflation") != EXPECTED_HYPERDEFLATION:
        findings.append("hyperdeflation semantic anchor drift")

    try:
        m6_atdd = _load_exact_json(root / M6_ATDD_PATH)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        findings.append(f"M6 ATDD semantic source cannot be loaded: {type(exc).__name__}: {exc}")
    else:
        findings.extend(validate_m6_zdex_semantic_anchor_v1(m6_atdd))

    gate_rows = status.get("gate_status")
    if type(gate_rows) is not list or any(type(row) is not dict for row in gate_rows):
        findings.append("gate status must be a list of objects")
    else:
        gate_ids = tuple(row.get("id") for row in gate_rows)
        if gate_ids != EXPECTED_GATE_IDS:
            findings.append("VM gate IDs must be complete and ordered")
        if any(row.get("status") not in {"GAP", "PARTIAL"} for row in gate_rows):
            findings.append("a VM gate exceeds the currently supported claim ceiling")
        if any(type(row.get("evidence")) is not str or not row["evidence"] for row in gate_rows):
            findings.append("every VM gate requires nonempty evidence")

    tau = _mapping(status.get("tau_upstream"), "Tau upstream", findings)
    if tau.get("common_ancestor") is not False or tau.get("requalification_required") is not True:
        findings.append("Tau rewritten-history requalification status drift")
    if tau.get("full_side_by_side_build_run") is not False:
        findings.append("Tau full-build status exceeds recorded evidence")

    observations = _mapping(
        status.get("live_gate_observations"),
        "live gate observations",
        findings,
    )
    production_boundary = _mapping(
        observations.get("production_boundary"),
        "production boundary observation",
        findings,
    )
    if production_boundary.get("ok") is not False:
        findings.append("production boundary observation must remain failed")

    return {
        "schema": "zenodex/value-movement-closure-status-check/v1",
        "ok": not findings,
        "subject_commit": commit,
        "gate_count": len(gate_rows) if type(gate_rows) is list else 0,
        "production_authority": authority.get("production_authority"),
        "findings": findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--status", type=Path)
    args = parser.parse_args(argv)
    report = check_value_movement_closure_status_v1(args.root, args.status)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
