"""Fail-closed checker for the FCIS M6 I08 honest delivery contract."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any, cast

_CLAIM_IDS = (
    "ATOMIC_ENQUEUE",
    "AT_LEAST_ONCE_ATTEMPTS",
    "STABLE_IDEMPOTENT_SEMANTIC_IDENTITY",
    "PROVENANCE_BOUND_ACKNOWLEDGMENT",
)
_CLAIM_FIELDS = frozenset({"id", "phrase", "meaning", "status"})
_EXPECTED_PHRASES = {
    "ATOMIC_ENQUEUE": "atomic enqueue",
    "AT_LEAST_ONCE_ATTEMPTS": "at-least-once attempts",
    "STABLE_IDEMPOTENT_SEMANTIC_IDENTITY": "stable idempotent semantic identity",
    "PROVENANCE_BOUND_ACKNOWLEDGMENT": "provenance-bound acknowledgment",
}
_EXPECTED_API_NAMES = {
    "enqueue": "atomic_enqueue",
    "attempt": "at_least_once_attempt",
    "identity": "stable_effect_identity",
    "acknowledgment": "provenance_bound_ack",
}
_FORBIDDEN_TOKENS = ("exactly-once", "exactly_once", "network_exactly_once")
_REQUIRED_NONCLAIMS = (
    "network-level exactly-once delivery",
    "production destination semantics without a verified dedup contract",
    "runtime mounting or value movement",
)


def _require_nonempty_string(value: object, label: str) -> None:
    if type(value) is not str or not value:
        raise ValueError(f"{label} must be a nonempty string")


def _require_string_list(value: object, label: str, *, nonempty: bool = True) -> list[str]:
    if type(value) is not list or (nonempty and not value):
        raise ValueError(f"{label} must be a {'nonempty ' if nonempty else ''}list")
    result = cast(list[str], value)
    if any(type(item) is not str or not item for item in result):
        raise ValueError(f"{label} must contain nonempty strings")
    if len(set(result)) != len(result):
        raise ValueError(f"{label} must not contain duplicates")
    return result


def _check_forbidden_claim_tokens(value: str, label: str) -> None:
    lowered = value.lower()
    if any(token in lowered for token in _FORBIDDEN_TOKENS):
        raise ValueError(f"unsupported exactly-once wording in {label}")


def _check_docs(
    docs_path: Path,
    claims: list[dict[str, Any]],
    nonclaims: list[str],
) -> None:
    try:
        lines = docs_path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        raise ValueError(f"contract documentation is unreadable: {exc}") from exc
    text = "\n".join(lines).lower()
    for claim in claims:
        phrase = cast(str, claim["phrase"])
        if phrase.lower() not in text:
            raise ValueError(f"contract documentation omits claim phrase: {phrase}")
    for nonclaim in nonclaims:
        if nonclaim.lower() not in text:
            raise ValueError(f"contract documentation omits nonclaim: {nonclaim}")
    claim_lines = [line for line in lines if re.match(r"^\s*-\s*Claim:", line)]
    if len(claim_lines) != len(_CLAIM_IDS):
        raise ValueError("contract documentation must contain exactly four Claim lines")
    for line in claim_lines:
        _check_forbidden_claim_tokens(line, "documentation Claim line")


def check_contract(path: Path) -> None:
    payload = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
    if payload.get("schema_version") != "zenodex.fcis.m6.i08.honest-delivery-contract.v1":
        raise ValueError("wrong I08 contract schema")
    if payload.get("task_id") != "I08":
        raise ValueError("wrong I08 task ID")
    if payload.get("status") != "RESEARCH_ONLY_UNMOUNTED":
        raise ValueError("I08 status must remain research-only and unmounted")
    required_ids = payload.get("required_claim_ids")
    if type(required_ids) is not list or tuple(required_ids) != _CLAIM_IDS:
        raise ValueError("I08 claim registry is incomplete or reordered")
    raw_claims = payload.get("claims")
    if type(raw_claims) is not list or len(raw_claims) != len(_CLAIM_IDS):
        raise ValueError("I08 must contain exactly four claims")
    claims = cast(list[dict[str, Any]], raw_claims)
    seen: set[str] = set()
    for claim in claims:
        if type(claim) is not dict or set(claim) != _CLAIM_FIELDS:
            raise ValueError("I08 claim fields are not exact")
        claim_id = claim["id"]
        phrase = claim["phrase"]
        meaning = claim["meaning"]
        status = claim["status"]
        _require_nonempty_string(claim_id, "claim.id")
        _require_nonempty_string(phrase, f"{claim_id}.phrase")
        _require_nonempty_string(meaning, f"{claim_id}.meaning")
        _require_nonempty_string(status, f"{claim_id}.status")
        if claim_id not in _CLAIM_IDS or claim_id in seen:
            raise ValueError(f"unknown or duplicate I08 claim: {claim_id}")
        if phrase != _EXPECTED_PHRASES[claim_id]:
            raise ValueError(f"unsupported wording for {claim_id}")
        if status != "RESEARCH_ONLY_UNMOUNTED":
            raise ValueError(f"{claim_id} has an invalid promotion status")
        _check_forbidden_claim_tokens(phrase, f"{claim_id}.phrase")
        _check_forbidden_claim_tokens(meaning, f"{claim_id}.meaning")
        seen.add(claim_id)
    if tuple(claim["id"] for claim in claims) != _CLAIM_IDS:
        raise ValueError("I08 claims are not in the required order")

    api_names_value = payload.get("api_names")
    if type(api_names_value) is not dict:
        raise ValueError("api_names must be an object")
    api_names = cast(dict[str, Any], api_names_value)
    if set(api_names) != set(_EXPECTED_API_NAMES):
        raise ValueError("I08 API name registry is not exact")
    for key, expected in _EXPECTED_API_NAMES.items():
        value = api_names[key]
        if value != expected:
            raise ValueError(f"unsupported API name for {key}")
        _check_forbidden_claim_tokens(cast(str, value), f"api_names.{key}")

    nonclaims = _require_string_list(payload.get("nonclaims"), "nonclaims")
    for required_nonclaim in _REQUIRED_NONCLAIMS:
        if required_nonclaim not in nonclaims:
            raise ValueError(f"I08 omits required nonclaim: {required_nonclaim}")
    docs_name_value = payload.get("documentation_file")
    _require_nonempty_string(docs_name_value, "documentation_file")
    docs_name = cast(str, docs_name_value)
    docs_path = (path.parent / docs_name).resolve()
    if docs_path.parent != path.parent.resolve():
        raise ValueError("documentation_file must stay beside the I08 contract")
    _check_docs(docs_path, claims, nonclaims)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_fcis_m6_i08_honest_contract.py <contract.json>", file=sys.stderr)
        return 2
    try:
        check_contract(Path(argv[1]))
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"I08_HONEST_CONTRACT_REJECT: {exc}", file=sys.stderr)
        return 1
    print("I08_HONEST_CONTRACT_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
