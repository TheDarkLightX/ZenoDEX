"""Stable rejection reports for ZenoLedger node/operator surfaces."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import hash_v0

REJECTION_REPORT_SCHEMA_V0 = "zenodex.zeno_ledger.rejection_report.v0"

BAD_JSON = "BAD_JSON"
BAD_AUTH = "BAD_AUTH"
HTTP_POST_TOO_LARGE = "HTTP_POST_TOO_LARGE"
REMOTE_ARTIFACT_TOO_LARGE = "REMOTE_ARTIFACT_TOO_LARGE"
GOSSIP_ALREADY_SEEN = "GOSSIP_ALREADY_SEEN"
GOSSIP_TX_CAP_EXCEEDED = "GOSSIP_TX_CAP_EXCEEDED"
GOSSIP_PREV_HASH_MISMATCH = "GOSSIP_PREV_HASH_MISMATCH"
GOSSIP_REPLAY_HEADER_MISMATCH = "GOSSIP_REPLAY_HEADER_MISMATCH"
PEER_NETWORK_MISMATCH = "PEER_NETWORK_MISMATCH"
PEER_CHAIN_MISMATCH = "PEER_CHAIN_MISMATCH"
PEER_FORK_CHOICE_REJECTED = "PEER_FORK_CHOICE_REJECTED"
DYNAMIC_PEER_CAP_EXCEEDED = "DYNAMIC_PEER_CAP_EXCEEDED"
PUBLIC_CONFIG_QUORUM_MISSING = "PUBLIC_CONFIG_QUORUM_MISSING"
LIVE_CHECKPOINT_QUORUM_MISSING = "LIVE_CHECKPOINT_QUORUM_MISSING"

KNOWN_REJECTION_CODES = frozenset(
    {
        BAD_JSON,
        BAD_AUTH,
        HTTP_POST_TOO_LARGE,
        REMOTE_ARTIFACT_TOO_LARGE,
        GOSSIP_ALREADY_SEEN,
        GOSSIP_TX_CAP_EXCEEDED,
        GOSSIP_PREV_HASH_MISMATCH,
        GOSSIP_REPLAY_HEADER_MISMATCH,
        PEER_NETWORK_MISMATCH,
        PEER_CHAIN_MISMATCH,
        PEER_FORK_CHOICE_REJECTED,
        DYNAMIC_PEER_CAP_EXCEEDED,
        PUBLIC_CONFIG_QUORUM_MISSING,
        LIVE_CHECKPOINT_QUORUM_MISSING,
    }
)

_HASH_FIELD = "rejection_report_hash"
_RESERVED_FIELDS = frozenset(
    {
        "schema",
        "ok",
        "status",
        "error_code",
        "detail",
        _HASH_FIELD,
    }
)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_code(code: object) -> str:
    if not isinstance(code, str) or code == "":
        raise ValueError("error_code must be a non-empty string")
    if code not in KNOWN_REJECTION_CODES:
        raise ValueError(f"unknown rejection code: {code}")
    return code


def _require_detail(detail: object) -> str:
    if not isinstance(detail, str):
        raise TypeError("detail must be a string")
    return detail


def _report_body(report: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(report).items() if key != _HASH_FIELD}


def _report_hash(body: Mapping[str, Any]) -> str:
    return hash_v0("zeno_ledger_rejection_report_v0", dict(body))


def build_rejection_report_v0(code: object, detail: str = "", **fields: object) -> dict[str, Any]:
    error_code = _require_code(code)
    message = _require_detail(detail)
    body: dict[str, Any] = {
        "schema": REJECTION_REPORT_SCHEMA_V0,
        "ok": False,
        "status": "rejected",
        "error_code": error_code,
        "detail": message,
    }
    for key, value in sorted(fields.items()):
        if key in _RESERVED_FIELDS:
            raise ValueError(f"reserved rejection report field: {key}")
        body[key] = value
    return {**body, _HASH_FIELD: _report_hash(body)}


def validate_rejection_report_v0(report: object) -> None:
    obj = dict(_require_mapping(report, name="report"))
    if obj.get("schema") != REJECTION_REPORT_SCHEMA_V0:
        raise ValueError("rejection report schema mismatch")
    if obj.get("ok") is not False:
        raise ValueError("rejection report ok must be false")
    if obj.get("status") != "rejected":
        raise ValueError("rejection report status must be rejected")
    _require_code(obj.get("error_code"))
    _require_detail(obj.get("detail"))
    report_hash = obj.get(_HASH_FIELD)
    if not isinstance(report_hash, str) or report_hash == "":
        raise ValueError("rejection report hash must be a non-empty string")
    expected_hash = _report_hash(_report_body(obj))
    if report_hash != expected_hash:
        raise ValueError("rejection report hash mismatch")
