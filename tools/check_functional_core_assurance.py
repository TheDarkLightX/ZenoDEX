#!/usr/bin/env python3
"""Validate the versioned ZenoDEX functional-core assurance profile.

Schema validation and release authorization are intentionally separate:

* ordinary CI accepts a structurally valid blocked profile so open work remains
  visible and machine-readable;
* ``--release`` fails closed unless every required obligation is closed with
  verified evidence, every declared TCB component is accepted, and the profile
  explicitly carries ``claim_status: released``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE = (
    ROOT / "docs" / "assurance" / "functional_core_assurance_profile_v1.json"
)
PROFILE_SCHEMA = "zenodex.functional_core.assurance_profile.v1"
REPORT_SCHEMA = "zenodex.functional_core.assurance_report.v1"

_TOP_LEVEL_KEYS = frozenset(
    {
        "schema",
        "profile_id",
        "version",
        "claim_status",
        "scope",
        "normative_transition",
        "trusted_computing_base",
        "obligations",
    }
)
_SCOPE_KEYS = frozenset({"included", "excluded"})
_TRANSITION_KEYS = frozenset({"signature", "accepted", "rejected", "determinism"})
_TCB_KEYS = frozenset(
    {"id", "component", "role", "status", "evidence", "blockers"}
)
_OBLIGATION_KEYS = frozenset(
    {
        "id",
        "title",
        "category",
        "statement",
        "status",
        "required_for_release",
        "evidence",
        "blockers",
    }
)
_EVIDENCE_KEYS = frozenset({"kind", "locator", "status", "sha256"})

_CLAIM_STATUSES = frozenset({"blocked", "candidate", "released"})
_TCB_STATUSES = frozenset({"provisional", "accepted"})
_OBLIGATION_STATUSES = frozenset({"open", "partial", "closed"})
_EVIDENCE_STATUSES = frozenset({"pending", "verified"})
_EVIDENCE_KINDS = frozenset(
    {
        "audit",
        "differential",
        "file",
        "formal_proof",
        "pull_request",
        "release_gate",
        "source",
        "test",
    }
)


class DuplicateJsonKeyError(ValueError):
    """Raised when a JSON object contains duplicate keys."""


def _strict_object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise DuplicateJsonKeyError(f"duplicate JSON key: {key!r}")
        out[key] = value
    return out


def load_profile(path: Path) -> dict[str, Any]:
    """Load one profile without silently collapsing duplicate object keys."""

    raw = path.read_text(encoding="utf-8")
    value = json.loads(raw, object_pairs_hook=_strict_object_pairs)
    if type(value) is not dict:
        raise TypeError("functional-core assurance profile must be a JSON object")
    return value


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _exact_keys(
    value: Mapping[str, Any],
    expected: frozenset[str],
    name: str,
    errors: list[str],
) -> None:
    actual = set(value)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing:
        errors.append(f"{name} missing fields: {','.join(missing)}")
    if extra:
        errors.append(f"{name} unknown fields: {','.join(extra)}")


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if type(value) is not dict:
        errors.append(f"{name} must be an exact object")
        return {}
    return value


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if type(value) is not list:
        errors.append(f"{name} must be an exact list")
        return []
    return value


def _string(value: Any, name: str, errors: list[str]) -> str | None:
    if type(value) is not str or not value:
        errors.append(f"{name} must be a non-empty exact string")
        return None
    return value


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if type(value) is not bool:
        errors.append(f"{name} must be an exact bool")
        return None
    return value


def _string_list(value: Any, name: str, errors: list[str]) -> list[str]:
    raw = _list(value, name, errors)
    out: list[str] = []
    for index, item in enumerate(raw):
        parsed = _string(item, f"{name}[{index}]", errors)
        if parsed is not None:
            out.append(parsed)
    return out


def _sha256_text(value: Any, name: str, errors: list[str]) -> str | None:
    if value is None:
        return None
    if type(value) is not str:
        errors.append(f"{name} must be null or a lowercase SHA-256 string")
        return None
    if len(value) != 64 or any(ch not in "0123456789abcdef" for ch in value):
        errors.append(f"{name} must be a lowercase 64-character SHA-256 string")
        return None
    return value


def _safe_relative_path(locator: str, root: Path) -> Path | None:
    path = Path(locator)
    if path.is_absolute() or ".." in path.parts:
        return None
    resolved = (root / path).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError:
        return None
    return resolved


def _validate_evidence(
    value: Any,
    *,
    name: str,
    root: Path,
    errors: list[str],
) -> dict[str, Any]:
    item = _mapping(value, name, errors)
    _exact_keys(item, _EVIDENCE_KEYS, name, errors)
    kind = _string(item.get("kind"), f"{name}.kind", errors)
    locator = _string(item.get("locator"), f"{name}.locator", errors)
    status = _string(item.get("status"), f"{name}.status", errors)
    digest = _sha256_text(item.get("sha256"), f"{name}.sha256", errors)

    if kind is not None and kind not in _EVIDENCE_KINDS:
        errors.append(f"{name}.kind unsupported: {kind!r}")
    if status is not None and status not in _EVIDENCE_STATUSES:
        errors.append(f"{name}.status unsupported: {status!r}")

    hash_verified = False
    if kind == "file":
        if digest is None:
            errors.append(f"{name}.sha256 is required for file evidence")
        if locator is not None:
            path = _safe_relative_path(locator, root)
            if path is None:
                errors.append(f"{name}.locator must be a safe repository-relative path")
            elif status == "verified":
                if not path.is_file():
                    errors.append(f"{name}.locator does not exist: {locator}")
                elif digest is not None:
                    observed = hashlib.sha256(path.read_bytes()).hexdigest()
                    if observed != digest:
                        errors.append(
                            f"{name}.sha256 mismatch: expected {digest}, observed {observed}"
                        )
                    else:
                        hash_verified = True
    elif digest is not None:
        hash_verified = True

    return {
        "kind": kind,
        "locator": locator,
        "status": status,
        "sha256": digest,
        "hash_verified": hash_verified,
    }


def validate_profile(
    profile: Any,
    *,
    root: Path = ROOT,
    release: bool = False,
) -> dict[str, Any]:
    """Validate profile structure and optionally authorize a release claim."""

    errors: list[str] = []
    obj = _mapping(profile, "profile", errors)
    _exact_keys(obj, _TOP_LEVEL_KEYS, "profile", errors)

    if obj.get("schema") != PROFILE_SCHEMA:
        errors.append("profile.schema mismatch")
    profile_id = _string(obj.get("profile_id"), "profile.profile_id", errors)
    version = obj.get("version")
    if type(version) is not int or version != 1:
        errors.append("profile.version must be exact int 1")
    claim_status = _string(obj.get("claim_status"), "profile.claim_status", errors)
    if claim_status is not None and claim_status not in _CLAIM_STATUSES:
        errors.append(f"profile.claim_status unsupported: {claim_status!r}")

    scope = _mapping(obj.get("scope"), "profile.scope", errors)
    _exact_keys(scope, _SCOPE_KEYS, "profile.scope", errors)
    included = _string_list(scope.get("included"), "profile.scope.included", errors)
    excluded = _string_list(scope.get("excluded"), "profile.scope.excluded", errors)
    if not included:
        errors.append("profile.scope.included must not be empty")
    if not excluded:
        errors.append("profile.scope.excluded must not be empty")

    transition = _mapping(
        obj.get("normative_transition"),
        "profile.normative_transition",
        errors,
    )
    _exact_keys(
        transition,
        _TRANSITION_KEYS,
        "profile.normative_transition",
        errors,
    )
    for key in sorted(_TRANSITION_KEYS):
        _string(
            transition.get(key),
            f"profile.normative_transition.{key}",
            errors,
        )

    tcb_items = _list(
        obj.get("trusted_computing_base"),
        "profile.trusted_computing_base",
        errors,
    )
    tcb_ids: set[str] = set()
    tcb_reports: list[dict[str, Any]] = []
    for index, raw in enumerate(tcb_items):
        name = f"profile.trusted_computing_base[{index}]"
        item_errors: list[str] = []
        item = _mapping(raw, name, item_errors)
        _exact_keys(item, _TCB_KEYS, name, item_errors)
        item_id = _string(item.get("id"), f"{name}.id", item_errors)
        _string(item.get("component"), f"{name}.component", item_errors)
        _string(item.get("role"), f"{name}.role", item_errors)
        status = _string(item.get("status"), f"{name}.status", item_errors)
        if item_id is not None:
            if item_id in tcb_ids:
                item_errors.append(f"{name}.id must be unique")
            tcb_ids.add(item_id)
        if status is not None and status not in _TCB_STATUSES:
            item_errors.append(f"{name}.status unsupported: {status!r}")

        evidence_raw = _list(item.get("evidence"), f"{name}.evidence", item_errors)
        evidence = [
            _validate_evidence(
                value,
                name=f"{name}.evidence[{evidence_index}]",
                root=root,
                errors=item_errors,
            )
            for evidence_index, value in enumerate(evidence_raw)
        ]
        blockers = _string_list(item.get("blockers"), f"{name}.blockers", item_errors)
        if status == "accepted":
            if blockers:
                item_errors.append(f"{name}.blockers must be empty when accepted")
            if not evidence:
                item_errors.append(f"{name}.evidence must not be empty when accepted")
            if any(entry.get("status") != "verified" for entry in evidence):
                item_errors.append(f"{name}.evidence must all be verified when accepted")
        elif status == "provisional" and not blockers:
            item_errors.append(f"{name}.blockers must not be empty when provisional")

        errors.extend(item_errors)
        tcb_reports.append(
            {
                "id": item_id,
                "status": status,
                "accepted": status == "accepted" and not item_errors,
                "errors": item_errors,
            }
        )

    obligation_items = _list(obj.get("obligations"), "profile.obligations", errors)
    obligation_ids: set[str] = set()
    obligation_reports: list[dict[str, Any]] = []
    for index, raw in enumerate(obligation_items):
        name = f"profile.obligations[{index}]"
        item_errors = []
        item = _mapping(raw, name, item_errors)
        _exact_keys(item, _OBLIGATION_KEYS, name, item_errors)
        item_id = _string(item.get("id"), f"{name}.id", item_errors)
        _string(item.get("title"), f"{name}.title", item_errors)
        _string(item.get("category"), f"{name}.category", item_errors)
        _string(item.get("statement"), f"{name}.statement", item_errors)
        status = _string(item.get("status"), f"{name}.status", item_errors)
        required = _bool(
            item.get("required_for_release"),
            f"{name}.required_for_release",
            item_errors,
        )
        if item_id is not None:
            if item_id in obligation_ids:
                item_errors.append(f"{name}.id must be unique")
            obligation_ids.add(item_id)
        if status is not None and status not in _OBLIGATION_STATUSES:
            item_errors.append(f"{name}.status unsupported: {status!r}")

        evidence_raw = _list(item.get("evidence"), f"{name}.evidence", item_errors)
        evidence = [
            _validate_evidence(
                value,
                name=f"{name}.evidence[{evidence_index}]",
                root=root,
                errors=item_errors,
            )
            for evidence_index, value in enumerate(evidence_raw)
        ]
        blockers = _string_list(item.get("blockers"), f"{name}.blockers", item_errors)

        if status == "closed":
            if blockers:
                item_errors.append(f"{name}.blockers must be empty when closed")
            if not evidence:
                item_errors.append(f"{name}.evidence must not be empty when closed")
            if any(entry.get("status") != "verified" for entry in evidence):
                item_errors.append(f"{name}.evidence must all be verified when closed")
        elif required is True and not blockers:
            item_errors.append(
                f"{name}.blockers must not be empty while a required obligation is not closed"
            )

        errors.extend(item_errors)
        obligation_reports.append(
            {
                "id": item_id,
                "status": status,
                "required_for_release": required,
                "closed": status == "closed" and not item_errors,
                "errors": item_errors,
            }
        )

    all_tcb_accepted = bool(tcb_reports) and all(
        item["accepted"] for item in tcb_reports
    )
    required_reports = [
        item for item in obligation_reports if item["required_for_release"] is True
    ]
    all_required_closed = bool(required_reports) and all(
        item["closed"] for item in required_reports
    )
    release_ready = not errors and all_tcb_accepted and all_required_closed

    if claim_status == "blocked" and release_ready:
        errors.append("claim_status blocked is stale because the profile is release-ready")
    if claim_status in {"candidate", "released"} and not release_ready:
        errors.append(f"claim_status {claim_status!r} requires a release-ready profile")

    release_errors: list[str] = []
    if release:
        if claim_status != "released":
            release_errors.append("release requires claim_status 'released'")
        if not all_tcb_accepted:
            release_errors.append("release requires every TCB component to be accepted")
        open_required = sorted(
            str(item["id"])
            for item in required_reports
            if not item["closed"]
        )
        if open_required:
            release_errors.append(
                "release requires every required obligation to be closed: "
                + ",".join(open_required)
            )
        if errors:
            release_errors.append("release requires a structurally valid profile")

    profile_hash = hashlib.sha256(_canonical_json_bytes(profile)).hexdigest()
    all_errors = [*errors, *release_errors]
    return {
        "schema": REPORT_SCHEMA,
        "ok": not all_errors,
        "profile_valid": not errors,
        "release_requested": release,
        "release_ready": release_ready,
        "claim_status": claim_status,
        "profile_id": profile_id,
        "profile_sha256": profile_hash,
        "tcb_count": len(tcb_reports),
        "accepted_tcb_count": sum(item["accepted"] for item in tcb_reports),
        "obligation_count": len(obligation_reports),
        "required_obligation_count": len(required_reports),
        "closed_required_obligation_count": sum(
            item["closed"] for item in required_reports
        ),
        "errors": all_errors,
        "trusted_computing_base": tcb_reports,
        "obligations": obligation_reports,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--release", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        profile = load_profile(args.profile)
        report = validate_profile(
            profile,
            root=args.root.resolve(),
            release=args.release,
        )
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "profile_valid": False,
            "release_requested": args.release,
            "release_ready": False,
            "errors": [f"profile load failed: {type(exc).__name__}: {exc}"],
        }

    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
