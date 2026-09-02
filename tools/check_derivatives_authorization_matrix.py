#!/usr/bin/env python3
"""Fail-closed checker for derivative authorization coverage claims."""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml


REPO_ROOT = Path(__file__).resolve().parents[1]
MATRIX_PATH = REPO_ROOT / "docs" / "derivatives" / "DERIVATIVES_AUTHORIZATION_COVERAGE_MATRIX.json"
CLAIMS_REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"

EXPECTED_SCHEMA = "zenodex/derivatives_authorization_coverage_matrix/v1"
REQUIRED_AREA_IDS = {
    "perps_clearinghouse",
    "funding_rate_market",
    "il_futures",
    "curve_selection",
    "general_cfmo_fire",
}
REQUIRED_OPEN_REQUIREMENTS = {
    "perps_clearinghouse": set(),
    "funding_rate_market": set(),
    "il_futures": set(),
    "curve_selection": set(),
    "general_cfmo_fire": set(),
}
EXPECTED_DISPUTED_CLAIMS = {
    "funding_rate_market": {
        "smt:funding_rate_market_v1:inductive_z3_cvc5",
    },
    "curve_selection": {
        "smt:curve_selection_market_v1:inductive_z3_cvc5",
    },
}
AUTHORIZATION_INCOMPLETE_AREAS: set[str] = set()
NON_DISPUTED_ALLOWED_STATUSES = {"supported", "proved"}


@dataclass(frozen=True)
class MatrixError(Exception):
    message: str

    def __str__(self) -> str:  # pragma: no cover
        return self.message


def _require_mapping(obj: Any, *, name: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise MatrixError(f"{name} must be an object")
    return obj


def _require_list(obj: Any, *, name: str) -> list[Any]:
    if not isinstance(obj, list):
        raise MatrixError(f"{name} must be a list")
    return obj


def _require_str(obj: Any, *, name: str) -> str:
    if not isinstance(obj, str) or not obj.strip():
        raise MatrixError(f"{name} must be a non-empty string")
    return obj.strip()


def _require_bool(obj: Any, *, name: str) -> bool:
    if not isinstance(obj, bool):
        raise MatrixError(f"{name} must be a boolean")
    return obj


def _string_list(obj: Any, *, name: str) -> list[str]:
    items = _require_list(obj, name=name)
    out: list[str] = []
    for idx, item in enumerate(items):
        out.append(_require_str(item, name=f"{name}[{idx}]"))
    return out


def load_matrix(path: Path = MATRIX_PATH) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise MatrixError(f"missing matrix: {path.relative_to(REPO_ROOT)}") from exc
    except json.JSONDecodeError as exc:
        raise MatrixError(f"invalid matrix JSON: {exc}") from exc
    return _require_mapping(data, name="matrix")


def load_claim_statuses(path: Path = CLAIMS_REGISTRY_PATH) -> dict[str, str]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise MatrixError(f"missing claims registry: {path.relative_to(REPO_ROOT)}") from exc
    except yaml.YAMLError as exc:
        raise MatrixError(f"invalid claims registry YAML: {exc}") from exc

    root = _require_mapping(data, name="claims registry")
    claims = _require_list(root.get("claims"), name="claims registry.claims")
    statuses: dict[str, str] = {}
    for idx, claim_obj in enumerate(claims):
        claim = _require_mapping(claim_obj, name=f"claims[{idx}]")
        claim_id = _require_str(claim.get("id"), name=f"claims[{idx}].id")
        status = _require_str(claim.get("status"), name=f"claims[{idx}].status")
        statuses[claim_id] = status
    return statuses


def _validate_requirement(
    *,
    area_id: str,
    requirement: dict[str, Any],
    claim_statuses: dict[str, str],
    disputed_claim_refs: set[str],
) -> tuple[str, bool]:
    requirement_id = _require_str(requirement.get("requirement_id"), name=f"{area_id}.requirement_id")
    covered = _require_bool(requirement.get("covered_required"), name=f"{area_id}.{requirement_id}.covered_required")
    evidence_refs = _string_list(
        requirement.get("evidence_claim_refs", []),
        name=f"{area_id}.{requirement_id}.evidence_claim_refs",
    )
    open_gap = requirement.get("open_gap")

    if covered:
        if not evidence_refs:
            raise MatrixError(f"{area_id}.{requirement_id} is covered but has no evidence claims")
        if open_gap is not None:
            raise MatrixError(f"{area_id}.{requirement_id} is covered but still has open_gap")
    else:
        if not isinstance(open_gap, str) or not open_gap.strip():
            raise MatrixError(f"{area_id}.{requirement_id} is open and must explain open_gap")

    for claim_ref in evidence_refs:
        status = claim_statuses.get(claim_ref)
        if status is None:
            raise MatrixError(f"{area_id}.{requirement_id} references missing claim {claim_ref}")
        if claim_ref in disputed_claim_refs:
            if not requirement.get("coverage_limit"):
                raise MatrixError(
                    f"{area_id}.{requirement_id} uses disputed claim {claim_ref} without coverage_limit"
                )
            if status != "disputed":
                raise MatrixError(f"expected disputed claim {claim_ref} to have status disputed, got {status}")
        elif status not in NON_DISPUTED_ALLOWED_STATUSES:
            raise MatrixError(f"claim {claim_ref} has unsupported status for matrix evidence: {status}")

    return requirement_id, covered


def validate_matrix(
    matrix_path: Path = MATRIX_PATH,
    claims_registry_path: Path = CLAIMS_REGISTRY_PATH,
) -> dict[str, Any]:
    matrix = load_matrix(matrix_path)
    claim_statuses = load_claim_statuses(claims_registry_path)

    schema = _require_str(matrix.get("schema"), name="matrix.schema")
    if schema != EXPECTED_SCHEMA:
        raise MatrixError(f"unsupported matrix schema: {schema}")

    summary = _require_mapping(matrix.get("summary"), name="matrix.summary")
    if summary.get("primary_gap") != "authorization_complete_settlement":
        raise MatrixError("matrix.summary.primary_gap must be authorization_complete_settlement")
    if summary.get("spot_ahead_of_derivatives") is not True:
        raise MatrixError("matrix.summary.spot_ahead_of_derivatives must be true")

    areas = _require_list(matrix.get("areas"), name="matrix.areas")
    seen_area_ids: set[str] = set()
    checked_requirements = 0
    open_requirements = 0

    for idx, area_obj in enumerate(areas):
        area = _require_mapping(area_obj, name=f"areas[{idx}]")
        area_id = _require_str(area.get("area_id"), name=f"areas[{idx}].area_id")
        if area_id in seen_area_ids:
            raise MatrixError(f"duplicate area_id: {area_id}")
        seen_area_ids.add(area_id)

        if area_id not in REQUIRED_AREA_IDS:
            raise MatrixError(f"unexpected area_id: {area_id}")

        authorization_complete = _require_bool(
            area.get("authorization_complete"),
            name=f"{area_id}.authorization_complete",
        )
        production_ready = _require_bool(area.get("production_ready"), name=f"{area_id}.production_ready")
        if area_id in AUTHORIZATION_INCOMPLETE_AREAS and authorization_complete:
            raise MatrixError(f"{area_id} must remain authorization_complete=false until gaps close")
        if production_ready and not authorization_complete:
            raise MatrixError(f"{area_id} cannot be production_ready while authorization_complete=false")

        claim_refs = set(_string_list(area.get("claim_refs", []), name=f"{area_id}.claim_refs"))
        disputed_claim_refs = set(
            _string_list(area.get("disputed_claim_refs", []), name=f"{area_id}.disputed_claim_refs")
        )
        expected_disputed = EXPECTED_DISPUTED_CLAIMS.get(area_id, set())
        if disputed_claim_refs != expected_disputed:
            raise MatrixError(
                f"{area_id}.disputed_claim_refs expected {sorted(expected_disputed)}, got {sorted(disputed_claim_refs)}"
            )
        if not disputed_claim_refs.issubset(claim_refs):
            raise MatrixError(f"{area_id}.disputed_claim_refs must be included in claim_refs")

        for claim_ref in claim_refs:
            status = claim_statuses.get(claim_ref)
            if status is None:
                raise MatrixError(f"{area_id} references missing claim {claim_ref}")
            if claim_ref in disputed_claim_refs:
                if status != "disputed":
                    raise MatrixError(f"{claim_ref} must remain disputed for {area_id}, got {status}")
            elif status not in NON_DISPUTED_ALLOWED_STATUSES:
                raise MatrixError(f"{claim_ref} has unsupported status for {area_id}: {status}")

        for source_doc in _string_list(area.get("source_docs", []), name=f"{area_id}.source_docs"):
            path = (REPO_ROOT / source_doc).resolve()
            if REPO_ROOT not in path.parents and path != REPO_ROOT:
                raise MatrixError(f"{area_id}.source_docs contains path outside repo: {source_doc}")
            if not path.exists():
                raise MatrixError(f"{area_id}.source_docs missing: {source_doc}")

        requirements = _require_list(area.get("requirements"), name=f"{area_id}.requirements")
        requirement_ids: set[str] = set()
        covered_count = 0
        open_count = 0
        for req_idx, requirement_obj in enumerate(requirements):
            requirement = _require_mapping(requirement_obj, name=f"{area_id}.requirements[{req_idx}]")
            requirement_id, covered = _validate_requirement(
                area_id=area_id,
                requirement=requirement,
                claim_statuses=claim_statuses,
                disputed_claim_refs=disputed_claim_refs,
            )
            if requirement_id in requirement_ids:
                raise MatrixError(f"duplicate requirement in {area_id}: {requirement_id}")
            requirement_ids.add(requirement_id)
            checked_requirements += 1
            if covered:
                covered_count += 1
            else:
                open_count += 1
                open_requirements += 1

        if covered_count == 0:
            raise MatrixError(f"{area_id} must record at least one covered requirement")
        if open_count == 0 and not authorization_complete:
            raise MatrixError(f"{area_id} must record at least one open gap")
        if open_count > 0 and authorization_complete:
            raise MatrixError(f"{area_id} cannot be authorization_complete while requirements remain open")

        required_open = REQUIRED_OPEN_REQUIREMENTS[area_id]
        missing_open = required_open - requirement_ids
        if missing_open:
            raise MatrixError(f"{area_id} missing required open requirements: {sorted(missing_open)}")
        for required_id in required_open:
            req = next(r for r in requirements if isinstance(r, dict) and r.get("requirement_id") == required_id)
            if req.get("covered_required") is not False:
                raise MatrixError(f"{area_id}.{required_id} must be open, not covered")

    if seen_area_ids != REQUIRED_AREA_IDS:
        missing = REQUIRED_AREA_IDS - seen_area_ids
        extra = seen_area_ids - REQUIRED_AREA_IDS
        raise MatrixError(f"area set mismatch, missing={sorted(missing)} extra={sorted(extra)}")

    return {
        "area_count": len(seen_area_ids),
        "checked_requirements": checked_requirements,
        "open_requirements": open_requirements,
        "disputed_claims": sorted({claim for claims in EXPECTED_DISPUTED_CLAIMS.values() for claim in claims}),
    }


def main(argv: list[str] | None = None) -> int:
    _ = argv
    try:
        report = validate_matrix()
    except MatrixError as exc:
        print(f"derivatives authorization matrix invalid: {exc}", file=sys.stderr)
        return 1
    print(
        "ok "
        f"areas={report['area_count']} "
        f"requirements={report['checked_requirements']} "
        f"open_requirements={report['open_requirements']} "
        f"disputed_claims={len(report['disputed_claims'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
