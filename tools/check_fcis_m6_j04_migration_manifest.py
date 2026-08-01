"""Fail-closed checker for the FCIS M6 J04 migration manifest."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, cast

_HEX_RE = re.compile(r"\A[0-9a-f]{64}\Z")
_ROOT_FIELDS = (
    "source_profile_root",
    "source_deployment_root",
    "source_configuration_root",
    "target_profile_root",
    "target_deployment_root",
    "target_configuration_root",
    "source_state_root",
    "target_state_root",
    "source_history_root",
    "target_history_root",
    "complete_replay_evidence_root",
)
_TRANSPORT_FIELDS = frozenset({"artifact_id", "checker_id", "transport_root"})
_TRANSPORT_IDS = ("state", "residual_fee_history", "outbox_effects")
_QUIESCENCE_MARKERS = frozenset(
    {
        "API_WRITER_QUIESCED",
        "CLI_WRITER_QUIESCED",
        "WORKER_WRITER_QUIESCED",
        "ADMIN_WRITER_QUIESCED",
        "DIRECT_ADAPTER_WRITER_QUIESCED",
        "HEAD_REPLAY_EQUAL",
    }
)
_MANIFEST_FIELDS = frozenset(
    {
        "schema_version",
        "task_id",
        "status",
        "source_profile_root",
        "source_deployment_root",
        "source_configuration_root",
        "target_profile_root",
        "target_deployment_root",
        "target_configuration_root",
        "source_state_root",
        "target_state_root",
        "source_history_root",
        "target_history_root",
        "transport_maps",
        "activation_sequence",
        "rollback_window",
        "quiescence_evidence",
        "complete_replay_evidence_root",
        "manifest_root",
        "nonclaims",
    }
)
_ROLLBACK_FIELDS = frozenset({"enabled", "max_sequence_exclusive", "history_preserved", "rules"})


def _text(value: object, label: str) -> str:
    if type(value) is not str or not value:
        raise ValueError(f"{label} must be a nonempty string")
    return value


def _root(value: object, label: str) -> str:
    checked = _text(value, label)
    if _HEX_RE.fullmatch(checked) is None:
        raise ValueError(f"{label} must be 64 lowercase hexadecimal characters")
    return checked


def _strings(value: object, label: str) -> list[str]:
    if type(value) is not list or not value:
        raise ValueError(f"{label} must be a nonempty list")
    items = cast(list[str], value)
    if any(type(item) is not str or not item for item in items):
        raise ValueError(f"{label} must contain nonempty strings")
    if len(set(items)) != len(items):
        raise ValueError(f"{label} must not contain duplicates")
    return items


def derive_manifest_root(payload: dict[str, Any]) -> str:
    """Hash the canonical manifest body without its self-reference."""

    body = dict(payload)
    body.pop("manifest_root", None)
    encoded = json.dumps(
        body,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _check_transport_maps(value: object) -> None:
    if type(value) is not list or len(value) != len(_TRANSPORT_IDS):
        raise ValueError("transport_maps must contain exactly three rows")
    rows = cast(list[dict[str, Any]], value)
    seen: set[str] = set()
    for row in rows:
        if type(row) is not dict or set(row) != _TRANSPORT_FIELDS:
            raise ValueError("transport map fields are not exact")
        artifact_id = _text(row["artifact_id"], "transport artifact_id")
        if artifact_id not in _TRANSPORT_IDS or artifact_id in seen:
            raise ValueError(f"unknown or duplicate transport artifact: {artifact_id}")
        _text(row["checker_id"], f"{artifact_id}.checker_id")
        _root(row["transport_root"], f"{artifact_id}.transport_root")
        if row["checker_id"] == "NONE":
            raise ValueError(f"{artifact_id} transport checker is missing")
        seen.add(artifact_id)
    if tuple(cast(str, row["artifact_id"]) for row in rows) != _TRANSPORT_IDS:
        raise ValueError("transport maps are not in the required order")


def _check_rollback_window(value: object, activation_sequence: int) -> None:
    if type(value) is not dict or set(value) != _ROLLBACK_FIELDS:
        raise ValueError("rollback_window fields are not exact")
    rollback = cast(dict[str, Any], value)
    if rollback["enabled"] is not True:
        raise ValueError("rollback window must be explicitly enabled")
    if rollback["history_preserved"] is not True:
        raise ValueError("rollback must preserve complete history")
    maximum = rollback["max_sequence_exclusive"]
    if type(maximum) is not int or maximum <= activation_sequence or maximum > (1 << 32) - 1:
        raise ValueError("rollback sequence window is invalid")
    rules = _strings(rollback["rules"], "rollback_window.rules")
    required_rules = {
        "restore complete authorized history",
        "do not restore balances alone",
        "preserve nullifiers and outbox identity",
    }
    if not required_rules.issubset(rules):
        raise ValueError("rollback rules omit complete-history protections")


def check_manifest(path: Path) -> None:
    payload = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
    if set(payload) != _MANIFEST_FIELDS:
        raise ValueError("J04 manifest fields are not exact")
    if payload["schema_version"] != "zenodex.fcis.m6.j04.migration-manifest.v1":
        raise ValueError("wrong J04 migration-manifest schema")
    if payload["task_id"] != "J04":
        raise ValueError("wrong J04 task ID")
    if payload["status"] != "RESEARCH_ONLY_UNMOUNTED":
        raise ValueError("J04 status must remain research-only and unmounted")
    roots = {name: _root(payload[name], name) for name in _ROOT_FIELDS}
    for source, target in (
        ("source_profile_root", "target_profile_root"),
        ("source_deployment_root", "target_deployment_root"),
        ("source_configuration_root", "target_configuration_root"),
    ):
        if roots[source] == roots[target]:
            raise ValueError(f"{source} and {target} must differ")
    activation_sequence = payload["activation_sequence"]
    if type(activation_sequence) is not int or not 0 < activation_sequence <= (1 << 32) - 1:
        raise ValueError("activation_sequence must be a positive u32")
    _check_transport_maps(payload["transport_maps"])
    _check_rollback_window(payload["rollback_window"], activation_sequence)
    quiescence = _strings(payload["quiescence_evidence"], "quiescence_evidence")
    if not _QUIESCENCE_MARKERS.issubset(quiescence):
        raise ValueError("quiescence evidence is incomplete")
    nonclaims = _strings(payload["nonclaims"], "nonclaims")
    if "M6 remains unmounted and non-promotable" not in nonclaims:
        raise ValueError("J04 nonclaims omit the unmounted boundary")
    expected_root = derive_manifest_root(payload)
    if roots["complete_replay_evidence_root"] == roots["source_history_root"]:
        raise ValueError("complete replay evidence must be independently bound")
    if payload["manifest_root"] != expected_root:
        raise ValueError("manifest_root does not match canonical manifest body")
    _root(payload["manifest_root"], "manifest_root")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_fcis_m6_j04_migration_manifest.py <manifest.json>", file=sys.stderr)
        return 2
    try:
        check_manifest(Path(argv[1]))
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"J04_MIGRATION_MANIFEST_REJECT: {exc}", file=sys.stderr)
        return 1
    print("J04_MIGRATION_MANIFEST_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
