"""Typed decoding for the M6 value-sink manifest.

Every entry binds a source-derived operation fingerprint, so a reviewed
classification cannot survive a relocated operation.  Entries that write
authority-control or generated artifacts must name their consumers, because an
artifact nobody reads carries different risk from one that selects authority.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from tools.m6_value_sinks.launchers import canonical_relative_path, read_bounded_text
from tools.m6_value_sinks.operations import SINK_KINDS

SCHEMA_V2 = "zenodex/m6-value-sink-inventory/v2"
MAX_MANIFEST_ENTRIES = 4096
MAX_MANIFEST_BYTES = 4 * 1024 * 1024
MAX_JSON_DEPTH = 64
MAX_JSON_NODES = 200_000
MAX_INT_DIGITS = 20
MAX_CLOSURE_GAPS = 4096
UNADJUDICATED = "UNADJUDICATED"

# UNADJUDICATED is an explicit research state, never a default. The economic
# meaning of a writer is a semantic input; guessing it would manufacture drift.
CLASSIFICATIONS = frozenset(
    {
        "ADVISORY_CONTROL_STATE",
        "AUTHORITY_CONTROL_STATE",
        "DURABLE_EXTERNAL_EFFECT_STATE",
        "DURABLE_VALUE_STATE",
        "GENERATED_ARTIFACT_STATE",
        "INITIALIZATION_STATE",
        "PUBLICATION_STATE",
        UNADJUDICATED,
    }
)
MEDIATION_STATUSES = frozenset(
    {
        "MEDIATED_BY_VERIFIED_PUBLISHER",
        "NON_VALUE_EFFECT",
        "RESEARCH_UNMOUNTED",
        "UNMEDIATED_DEPLOYED_WRITER",
        UNADJUDICATED,
    }
)
# A write that can steer authority or feed another decision may never be excused
# as a non-value effect, and must name who consumes what it writes.
CONSUMER_TRACED_CLASSIFICATIONS = frozenset(
    {"AUTHORITY_CONTROL_STATE", "GENERATED_ARTIFACT_STATE"}
)
VALUE_BEARING_CLASSIFICATIONS = frozenset(
    {
        "AUTHORITY_CONTROL_STATE",
        "DURABLE_EXTERNAL_EFFECT_STATE",
        "DURABLE_VALUE_STATE",
        "GENERATED_ARTIFACT_STATE",
        "INITIALIZATION_STATE",
        "PUBLICATION_STATE",
    }
)

_SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")

_ENTRY_KEYS = {
    "classification",
    "consumers",
    "deployed_reachable",
    "identity_fingerprint",
    "mediation_status",
    "occurrence_count",
    "path",
    "rationale",
    "release_binding",
    "sink_id",
    "sink_kind",
    "symbol",
}
_STRING_FIELDS = ("sink_id", "path", "symbol", "sink_kind", "classification", "mediation_status", "rationale")


CONSUMER_KINDS = frozenset({"LAUNCHER_ID", "REPO_PATH"})


@dataclass(frozen=True, slots=True, order=True)
class ConsumerRecordV2:
    """One source-bound reader of an artifact.

    A free-form sentence is not evidence. A consumer names either a repository
    path that must exist in the scanned tree or a decoded launcher identifier.
    """

    artifact: str
    kind: str
    reader_fingerprint: str
    reference: str
    source_path: str
    source_sha256: str

    def to_dict(self) -> dict[str, str]:
        return {
            "artifact": self.artifact,
            "kind": self.kind,
            "reader_fingerprint": self.reader_fingerprint,
            "reference": self.reference,
            "source_path": self.source_path,
            "source_sha256": self.source_sha256,
        }


@dataclass(frozen=True, slots=True)
class ValueSinkSpecV2:
    sink_id: str
    path: str
    symbol: str
    sink_kind: str
    occurrence_count: int
    identity_fingerprint: str
    classification: str
    mediation_status: str
    consumers: tuple[ConsumerRecordV2, ...]
    deployed_reachable: bool
    release_binding: None
    rationale: str

    def identity(self) -> tuple[str, str, str]:
        return (self.path, self.symbol, self.sink_kind)

    def to_dict(self) -> dict[str, object]:
        return {
            "classification": self.classification,
            "consumers": [consumer.to_dict() for consumer in self.consumers],
            "deployed_reachable": self.deployed_reachable,
            "identity_fingerprint": self.identity_fingerprint,
            "mediation_status": self.mediation_status,
            "occurrence_count": self.occurrence_count,
            "path": self.path,
            "rationale": self.rationale,
            "release_binding": self.release_binding,
            "sink_id": self.sink_id,
            "sink_kind": self.sink_kind,
            "symbol": self.symbol,
        }


@dataclass(frozen=True, slots=True, order=True)
class ClosureGapV2:
    path: str
    mechanism: str
    rationale: str

    def identity(self) -> tuple[str, str]:
        return (self.path, self.mechanism)

    def to_dict(self) -> dict[str, str]:
        return {"mechanism": self.mechanism, "path": self.path, "rationale": self.rationale}


def identity_sink_id_v2(identity: tuple[str, str, str]) -> str:
    """Derive the only accepted sink ID from the complete source identity."""

    path, symbol, kind = identity
    payload = "\0".join(identity).encode("utf-8")
    digest = hashlib.sha256(b"zenodex-m6-sink-id-v2\0" + payload).hexdigest()
    return f"{Path(path).stem}__{symbol.replace('.', '_')}__{kind.lower()}__{digest}"


def _scan_json_shape(text: str) -> tuple[int, int]:
    """Measure container depth and a structural node count lexically.

    The scan runs before parsing so a hostile nesting depth is rejected by a
    typed error instead of exhausting the interpreter stack.  String contents
    and escapes are skipped so a brace inside a string cannot inflate depth.
    """

    depth = 0
    maximum = 0
    nodes = 0
    in_string = False
    escaped = False
    for character in text:
        if in_string:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            continue
        if character == '"':
            in_string = True
            nodes += 1
        elif character in "[{":
            depth += 1
            maximum = max(maximum, depth)
            nodes += 1
        elif character in "]}":
            depth -= 1
        elif character in ",:":
            nodes += 1
    return maximum, nodes


def _reject_json_float(value: str) -> float:
    raise ValueError(f"manifest rejects non-integer number: {value}")


def _reject_json_constant(value: str) -> object:
    raise ValueError(f"manifest rejects nonfinite constant: {value}")


def _parse_json_int(value: str) -> int:
    if len(value.lstrip("-")) > MAX_INT_DIGITS:
        raise ValueError(f"manifest integer exceeds {MAX_INT_DIGITS} digits")
    return int(value)


def _decode_bounded_json_text(text: str) -> Any:
    """Decode one manifest text under explicit resource bounds.

    Every failure, including recursion exhaustion, is normalized to ValueError
    so a hostile document produces a typed rejection rather than a crash.
    """

    if len(text.encode("utf-8")) > MAX_MANIFEST_BYTES:
        raise ValueError(f"value sink manifest exceeds {MAX_MANIFEST_BYTES} bytes")
    depth, nodes = _scan_json_shape(text)
    if depth > MAX_JSON_DEPTH:
        raise ValueError(f"value sink manifest exceeds depth {MAX_JSON_DEPTH}")
    if nodes > MAX_JSON_NODES:
        raise ValueError(f"value sink manifest exceeds {MAX_JSON_NODES} nodes")
    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicate_keys,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
            parse_int=_parse_json_int,
        )
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ValueError(f"cannot read value sink manifest: {exc}") from exc


def _decode_bounded_json(path: Path) -> Any:
    """Read and decode one manifest under explicit resource bounds."""

    text, error = read_bounded_text(path, MAX_MANIFEST_BYTES)
    if text is None:
        raise ValueError(f"cannot read value sink manifest: {error}")
    return _decode_bounded_json_text(text)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def require_exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    if set(value) != expected:
        missing = sorted(expected - set(value))
        surplus = sorted(set(value) - expected)
        raise ValueError(f"{label} keys mismatch: missing={missing}, surplus={surplus}")


def _parse_consumers(value: Any, *, label: str) -> tuple[ConsumerRecordV2, ...]:
    if not isinstance(value, list):
        raise ValueError(f"{label} must be a list")
    records: list[ConsumerRecordV2] = []
    for index, item in enumerate(value):
        item_label = f"{label}[{index}]"
        if not isinstance(item, Mapping):
            raise ValueError(f"{item_label} must be an object")
        require_exact_keys(
            item,
            {
                "artifact",
                "kind",
                "reader_fingerprint",
                "reference",
                "source_path",
                "source_sha256",
            },
            label=item_label,
        )
        artifact = item["artifact"]
        kind = item["kind"]
        reader_fingerprint = item["reader_fingerprint"]
        reference = item["reference"]
        source_path = item["source_path"]
        source_sha256 = item["source_sha256"]
        if type(artifact) is not str or not artifact or any(ord(character) < 32 for character in artifact):
            raise ValueError(f"{item_label}.artifact must be a non-empty exact string")
        if type(kind) is not str or kind not in CONSUMER_KINDS:
            raise ValueError(f"{item_label}.kind is unknown")
        if type(reader_fingerprint) is not str or _SHA256_RE.fullmatch(reader_fingerprint) is None:
            raise ValueError(f"{item_label}.reader_fingerprint must be lowercase SHA-256")
        if type(reference) is not str or not reference.strip():
            raise ValueError(f"{item_label}.reference must be a non-empty exact string")
        if kind == "REPO_PATH" and canonical_relative_path(reference) != reference:
            raise ValueError(f"{item_label}.reference must be a canonical repository-relative path")
        if type(source_path) is not str or canonical_relative_path(source_path) != source_path:
            raise ValueError(f"{item_label}.source_path must be a canonical repository-relative path")
        if kind == "REPO_PATH" and reference != source_path:
            raise ValueError(f"{item_label}.reference must equal source_path for REPO_PATH consumers")
        if type(source_sha256) is not str or _SHA256_RE.fullmatch(source_sha256) is None:
            raise ValueError(f"{item_label}.source_sha256 must be lowercase SHA-256")
        records.append(
            ConsumerRecordV2(
                artifact=artifact,
                kind=kind,
                reader_fingerprint=reader_fingerprint,
                reference=reference,
                source_path=source_path,
                source_sha256=source_sha256,
            )
        )
    identities = [
        (
            record.artifact,
            record.kind,
            record.reader_fingerprint,
            record.reference,
            record.source_path,
            record.source_sha256,
        )
        for record in records
    ]
    if len(identities) != len(set(identities)):
        raise ValueError(f"{label} must be unique")
    if list(records) != sorted(records):
        raise ValueError(f"{label} must be canonically sorted")
    return tuple(records)


def _check_entry_types(value: Mapping[str, Any], *, label: str) -> None:
    if any(not isinstance(value[name], str) or not value[name] for name in _STRING_FIELDS):
        raise ValueError(f"{label} has an invalid string field")
    if canonical_relative_path(value["path"]) != value["path"] or not value["path"].endswith(".py"):
        raise ValueError(f"{label}.path must be a canonical repository-relative Python path")
    if value["sink_kind"] not in SINK_KINDS:
        raise ValueError(f"{label}.sink_kind is unknown")
    if value["classification"] not in CLASSIFICATIONS:
        raise ValueError(f"{label}.classification is unknown")
    if value["mediation_status"] not in MEDIATION_STATUSES:
        raise ValueError(f"{label}.mediation_status is unknown")
    if _SHA256_RE.fullmatch(value["identity_fingerprint"]) is None:
        raise ValueError(f"{label}.identity_fingerprint must be lowercase SHA-256")
    if type(value["deployed_reachable"]) is not bool:
        raise ValueError(f"{label}.deployed_reachable must be an exact boolean")
    if type(value["occurrence_count"]) is not int or value["occurrence_count"] <= 0:
        raise ValueError(f"{label}.occurrence_count must be a positive exact integer")
    if value["release_binding"] is not None:
        raise ValueError(f"{label}.release_binding must remain null in research schema v2")


def _check_entry_consistency(value: Mapping[str, Any], *, label: str) -> None:
    classification = value["classification"]
    mediation = value["mediation_status"]
    if UNADJUDICATED in (classification, mediation):
        # An unreviewed row carries no judgement at all: no partial
        # classification, no consumer evidence, no release binding.
        if classification != mediation:
            raise ValueError(f"{label} must leave classification and mediation both unadjudicated")
        if value["consumers"]:
            raise ValueError(f"{label} names consumers for an unadjudicated sink")
        return
    if value["deployed_reachable"] and mediation == "RESEARCH_UNMOUNTED":
        raise ValueError(f"{label} marks a deployed sink as research-only")
    if not value["deployed_reachable"] and mediation == "UNMEDIATED_DEPLOYED_WRITER":
        raise ValueError(f"{label} marks an undeployed sink as a deployed writer")
    if classification in VALUE_BEARING_CLASSIFICATIONS and mediation == "NON_VALUE_EFFECT":
        raise ValueError(f"{label} excuses a value-bearing classification as a non-value effect")
    if classification in CONSUMER_TRACED_CLASSIFICATIONS and not value["consumers"]:
        raise ValueError(f"{label} must name the consumers of its artifact")
    if classification not in CONSUMER_TRACED_CLASSIFICATIONS and value["consumers"]:
        raise ValueError(f"{label} names consumers for a classification that does not trace them")


def _parse_spec(value: Any, *, index: int) -> ValueSinkSpecV2:
    label = f"sink entries[{index}]"
    if not isinstance(value, Mapping):
        raise ValueError(f"{label} must be an object")
    require_exact_keys(value, _ENTRY_KEYS, label=label)
    consumers = _parse_consumers(value["consumers"], label=f"{label}.consumers")
    _check_entry_types(value, label=label)
    _check_entry_consistency(value, label=label)
    identity = (value["path"], value["symbol"], value["sink_kind"])
    if value["sink_id"] != identity_sink_id_v2(identity):
        raise ValueError(f"{label}.sink_id must equal its full-identity ID")
    return ValueSinkSpecV2(
        sink_id=value["sink_id"],
        path=value["path"],
        symbol=value["symbol"],
        sink_kind=value["sink_kind"],
        occurrence_count=value["occurrence_count"],
        identity_fingerprint=value["identity_fingerprint"],
        classification=value["classification"],
        mediation_status=value["mediation_status"],
        consumers=consumers,
        deployed_reachable=value["deployed_reachable"],
        release_binding=None,
        rationale=value["rationale"],
    )


@dataclass(frozen=True, slots=True)
class ValueSinkDocumentV2:
    """Entries and closure gaps decoded from one manifest read.

    Both halves come from a single set of bytes, so a concurrent edit cannot
    give the comparison step entries from one document and gaps from another.
    """

    entries: tuple[ValueSinkSpecV2, ...]
    closure_gaps: tuple[ClosureGapV2, ...]


def _document_mapping(raw: Any) -> Mapping[str, Any]:
    if not isinstance(raw, Mapping):
        raise ValueError("value sink manifest root must be an object")
    require_exact_keys(raw, {"closure_gaps", "entries", "schema", "scope"}, label="value sink manifest")
    if raw["schema"] != SCHEMA_V2:
        raise ValueError("value sink manifest schema mismatch")
    if not isinstance(raw["scope"], str) or not raw["scope"].strip():
        raise ValueError("value sink manifest scope must be nonempty")
    return raw


def _load_document(path: Path) -> Mapping[str, Any]:
    return _document_mapping(_decode_bounded_json(path))


def _decode_document(raw: Mapping[str, Any]) -> ValueSinkDocumentV2:
    return ValueSinkDocumentV2(
        entries=_parse_entries(raw["entries"]),
        closure_gaps=_parse_closure_gaps(raw["closure_gaps"]),
    )


def load_value_sink_document(path: Path) -> ValueSinkDocumentV2:
    """Decode entries and closure gaps from one bounded read."""

    return _decode_document(_load_document(path))


def decode_value_sink_document_text_v2(text: str) -> ValueSinkDocumentV2:
    """Apply the production manifest decoder to already rendered exact bytes."""

    return _decode_document(_document_mapping(_decode_bounded_json_text(text)))


def _parse_entries(entries: Any) -> tuple[ValueSinkSpecV2, ...]:
    if not isinstance(entries, list) or not entries:
        raise ValueError("value sink manifest entries must be nonempty")
    if len(entries) > MAX_MANIFEST_ENTRIES:
        raise ValueError(f"value sink manifest exceeds {MAX_MANIFEST_ENTRIES} entries")
    specs = tuple(_parse_spec(entry, index=index) for index, entry in enumerate(entries))
    ids = [spec.sink_id for spec in specs]
    identities = [spec.identity() for spec in specs]
    if len(ids) != len(set(ids)):
        raise ValueError("value sink IDs must be unique")
    if len(identities) != len(set(identities)):
        raise ValueError("value sink identities must be unique")
    if identities != sorted(identities):
        raise ValueError("value sink entries must use canonical identity order")
    return specs


def _parse_closure_gap(value: Any, *, index: int) -> ClosureGapV2:
    label = f"closure_gaps[{index}]"
    if not isinstance(value, Mapping):
        raise ValueError(f"{label} must be an object")
    require_exact_keys(value, {"mechanism", "path", "rationale"}, label=label)
    if any(not isinstance(value[name], str) or not value[name] for name in ("mechanism", "path", "rationale")):
        raise ValueError(f"{label} has an invalid string field")
    if canonical_relative_path(value["path"]) != value["path"]:
        raise ValueError(f"{label}.path must be a canonical repository-relative path")
    return ClosureGapV2(path=value["path"], mechanism=value["mechanism"], rationale=value["rationale"])


def _parse_closure_gaps(gaps: Any) -> tuple[ClosureGapV2, ...]:
    if not isinstance(gaps, list):
        raise ValueError("closure_gaps must be a list")
    if len(gaps) > MAX_CLOSURE_GAPS:
        raise ValueError(f"closure_gaps exceeds {MAX_CLOSURE_GAPS} entries")
    parsed = tuple(_parse_closure_gap(gap, index=index) for index, gap in enumerate(gaps))
    identities = [gap.identity() for gap in parsed]
    # Reconciliation compares identities, so two rows sharing an identity with
    # different rationales would collapse silently during the set difference.
    if len(identities) != len(set(identities)):
        raise ValueError("closure_gaps identities must be unique")
    if list(parsed) != sorted(parsed):
        raise ValueError("closure_gaps must use canonical order")
    return parsed


def load_value_sink_manifest(path: Path) -> tuple[ValueSinkSpecV2, ...]:
    return load_value_sink_document(path).entries


def load_closure_gaps(path: Path) -> tuple[ClosureGapV2, ...]:
    return load_value_sink_document(path).closure_gaps
