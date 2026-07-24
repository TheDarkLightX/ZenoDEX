"""Canonical authority-false completion markers for remote reproof stages."""

from __future__ import annotations

import copy
import hashlib
import json
import re
from pathlib import PurePosixPath
from typing import Mapping, Sequence, cast

SCHEMA = "zenodex/zrpf_remote_reproof_stage_publication_marker/v1"
STATUS = "complete_stage_outputs_published_without_proof_or_release_authority"
CONTENT_ID_DOMAIN = b"zenodex/zrpf_remote_reproof_stage_publication_marker_id/v1\0"
ZERO_SHA256 = "0" * 64
MAX_MARKER_BYTES = 4 * 1024 * 1024
MAX_OUTPUTS = 128
MAX_STAGE_ID_CHARS = 128
MAX_ORDINAL = 9_999

AUTHORITY_FIELDS = (
    "data_availability_authority",
    "ledger_authority",
    "production_authority",
    "proof_authority",
    "release_authority",
    "settlement_authority",
)
FIELDS = {
    "schema",
    "status",
    "content_id",
    "handoff_id",
    "execution_packet_id",
    "task_id",
    "stage_id",
    "ordinal",
    "capture_id",
    "outputs",
    "authority",
}
_HEX_RE = re.compile(r"[0-9a-f]{64}\Z")
_STAGE_RE = re.compile(r"[a-z0-9_]+\Z")


class StagePublicationMarkerError(ValueError):
    """Stable fail-closed marker rejection."""


def canonical_json_bytes_v1(value: object) -> bytes:
    try:
        raw = (
            json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n"
        ).encode("ascii")
    except (TypeError, ValueError, OverflowError) as exc:
        raise StagePublicationMarkerError("marker is not canonical JSON data") from exc
    if len(raw) > MAX_MARKER_BYTES:
        raise StagePublicationMarkerError("marker exceeds its byte bound")
    return raw


def false_authority_v1() -> dict[str, bool]:
    return {field: False for field in AUTHORITY_FIELDS}


def derive_stage_publication_content_id_v1(document: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(document))
    candidate["content_id"] = ZERO_SHA256
    return hashlib.sha256(CONTENT_ID_DOMAIN + canonical_json_bytes_v1(candidate)).hexdigest()


def stage_publication_marker_relative_path_v1(ordinal: int, stage_id: str) -> str:
    checked_ordinal = _ordinal(ordinal, "marker ordinal")
    checked_stage = _stage_id(stage_id, "marker stage ID")
    return str(
        PurePosixPath(".zrpf-stage-publications")
        / "v1"
        / f"{checked_ordinal:02d}-{checked_stage}.json"
    )


def build_stage_publication_marker_v1(
    *,
    handoff_id: str,
    execution_packet_id: str,
    task_id: str,
    stage_id: str,
    ordinal: int,
    capture_id: str,
    outputs: Sequence[Mapping[str, object]],
) -> dict[str, object]:
    checked_outputs = _outputs(outputs, "marker outputs")
    document: dict[str, object] = {
        "schema": SCHEMA,
        "status": STATUS,
        "content_id": ZERO_SHA256,
        "handoff_id": _hex(handoff_id, "marker handoff ID"),
        "execution_packet_id": _hex(execution_packet_id, "marker execution packet ID"),
        "task_id": _hex(task_id, "marker task ID"),
        "stage_id": _stage_id(stage_id, "marker stage ID"),
        "ordinal": _ordinal(ordinal, "marker ordinal"),
        "capture_id": _hex(capture_id, "marker capture ID"),
        "outputs": checked_outputs,
        "authority": false_authority_v1(),
    }
    document["content_id"] = derive_stage_publication_content_id_v1(document)
    canonical_json_bytes_v1(document)
    return document


def validate_stage_publication_marker_v1(
    document: Mapping[str, object],
    *,
    expected_handoff_id: str,
    expected_execution_packet_id: str,
    expected_task_id: str,
    expected_stage_id: str,
    expected_ordinal: int,
    expected_outputs: Sequence[Mapping[str, object]],
) -> None:
    if type(document) is not dict or set(document) != FIELDS:
        raise StagePublicationMarkerError("marker fields are not exact")
    if document.get("schema") != SCHEMA or document.get("status") != STATUS:
        raise StagePublicationMarkerError("marker schema or status mismatch")
    content_id = _hex(document.get("content_id"), "marker content ID")
    if content_id != derive_stage_publication_content_id_v1(document):
        raise StagePublicationMarkerError("marker content ID mismatch")
    expected = (
        ("handoff_id", _hex(expected_handoff_id, "expected handoff ID")),
        (
            "execution_packet_id",
            _hex(expected_execution_packet_id, "expected execution packet ID"),
        ),
        ("task_id", _hex(expected_task_id, "expected task ID")),
        ("stage_id", _stage_id(expected_stage_id, "expected stage ID")),
        ("ordinal", _ordinal(expected_ordinal, "expected ordinal")),
    )
    for field, value in expected:
        if type(document.get(field)) is not type(value) or document.get(field) != value:
            raise StagePublicationMarkerError(f"marker {field} mismatch")
    _hex(document.get("capture_id"), "marker capture ID")
    actual_outputs = _outputs_value(document.get("outputs"), "marker outputs")
    checked_expected_outputs = _outputs(expected_outputs, "expected marker outputs")
    if canonical_json_bytes_v1(actual_outputs) != canonical_json_bytes_v1(checked_expected_outputs):
        raise StagePublicationMarkerError("marker outputs mismatch")
    authority = document.get("authority")
    if type(authority) is not dict or set(authority) != set(AUTHORITY_FIELDS):
        raise StagePublicationMarkerError("marker authority fields are not exact")
    if any(authority[field] is not False for field in AUTHORITY_FIELDS):
        raise StagePublicationMarkerError("marker authority must use exact Boolean false")
    canonical_json_bytes_v1(document)


def _outputs(value: object, label: str) -> list[dict[str, object]]:
    if isinstance(value, (str, bytes, bytearray)) or not isinstance(value, Sequence):
        raise StagePublicationMarkerError(f"{label} must be a sequence")
    source_rows = list(value)
    if not source_rows or len(source_rows) > MAX_OUTPUTS:
        raise StagePublicationMarkerError(f"{label} count is outside its bound")
    if any(type(row) is not dict for row in source_rows):
        raise StagePublicationMarkerError(f"{label} must contain objects")
    rows = [copy.deepcopy(cast(dict[str, object], row)) for row in source_rows]
    canonical_json_bytes_v1(rows)
    return rows


def _outputs_value(value: object, label: str) -> list[dict[str, object]]:
    if type(value) is not list:
        raise StagePublicationMarkerError(f"{label} must be a list")
    return _outputs(value, label)


def _hex(value: object, label: str) -> str:
    if type(value) is not str or _HEX_RE.fullmatch(value) is None:
        raise StagePublicationMarkerError(f"{label} must be 64 lowercase hex characters")
    return value


def _stage_id(value: object, label: str) -> str:
    if (
        type(value) is not str
        or not value
        or len(value) > MAX_STAGE_ID_CHARS
        or _STAGE_RE.fullmatch(value) is None
    ):
        raise StagePublicationMarkerError(f"{label} is invalid")
    return value


def _ordinal(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_ORDINAL:
        raise StagePublicationMarkerError(f"{label} is outside its bound")
    return value
