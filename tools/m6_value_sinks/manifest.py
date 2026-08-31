"""Typed decoding for the M6 value-sink manifest.

Every entry binds a source-derived operation fingerprint, so a reviewed
classification cannot survive a relocated operation.  Entries that write
authority-control or generated artifacts must name their consumers, because an
artifact nobody reads carries different risk from one that selects authority.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from tools.m6_value_sinks.launchers import canonical_relative_path
from tools.m6_value_sinks.operations import SINK_KINDS

SCHEMA_V2 = "zenodex/m6-value-sink-inventory/v2"
MAX_MANIFEST_ENTRIES = 4096
UNADJUDICATED = "UNADJUDICATED"

CLASSIFICATIONS = frozenset(
    {
        "ADVISORY_CONTROL_STATE",
        "AUTHORITY_CONTROL_STATE",
        "DURABLE_EXTERNAL_EFFECT_STATE",
        "DURABLE_VALUE_STATE",
        "GENERATED_ARTIFACT_STATE",
        "INITIALIZATION_STATE",
        "PUBLICATION_STATE",
    }
)
MEDIATION_STATUSES = frozenset(
    {
        "MEDIATED_BY_VERIFIED_PUBLISHER",
        "NON_VALUE_EFFECT",
        "RESEARCH_UNMOUNTED",
        "UNMEDIATED_DEPLOYED_WRITER",
    }
)
# A write that can steer authority or feed another decision may never be excused
# as a non-value effect, and must name who consumes what it writes.
CONSUMER_TRACED_CLASSIFICATIONS = frozenset({"AUTHORITY_CONTROL_STATE", "GENERATED_ARTIFACT_STATE"})
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
_STRING_FIELDS = (
    "sink_id",
    "path",
    "symbol",
    "sink_kind",
    "classification",
    "mediation_status",
    "rationale",
)


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
    consumers: tuple[str, ...]
    deployed_reachable: bool
    release_binding: None
    rationale: str

    def identity(self) -> tuple[str, str, str]:
        return (self.path, self.symbol, self.sink_kind)

    def to_dict(self) -> dict[str, object]:
        return {
            "classification": self.classification,
            "consumers": list(self.consumers),
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


def _require_string_list(value: Any, *, label: str, allow_empty: bool) -> tuple[str, ...]:
    if not isinstance(value, list) or (not value and not allow_empty):
        raise ValueError(f"{label} must be a {'' if allow_empty else 'non-empty '}string list")
    if any(type(item) is not str or not item.strip() for item in value):
        raise ValueError(f"{label} must contain non-empty exact strings")
    if value != sorted(set(value)):
        raise ValueError(f"{label} must be unique and canonically sorted")
    return tuple(value)


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
    _require_string_list(value["consumers"], label=f"{label}.consumers", allow_empty=True)
    _check_entry_types(value, label=label)
    _check_entry_consistency(value, label=label)
    return ValueSinkSpecV2(
        sink_id=value["sink_id"],
        path=value["path"],
        symbol=value["symbol"],
        sink_kind=value["sink_kind"],
        occurrence_count=value["occurrence_count"],
        identity_fingerprint=value["identity_fingerprint"],
        classification=value["classification"],
        mediation_status=value["mediation_status"],
        consumers=tuple(value["consumers"]),
        deployed_reachable=value["deployed_reachable"],
        release_binding=None,
        rationale=value["rationale"],
    )


def _load_document(path: Path) -> Mapping[str, Any]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError(f"cannot read value sink manifest: {exc}") from exc
    if not isinstance(raw, Mapping):
        raise ValueError("value sink manifest root must be an object")
    require_exact_keys(
        raw, {"closure_gaps", "entries", "schema", "scope"}, label="value sink manifest"
    )
    if raw["schema"] != SCHEMA_V2:
        raise ValueError("value sink manifest schema mismatch")
    if not isinstance(raw["scope"], str) or not raw["scope"].strip():
        raise ValueError("value sink manifest scope must be nonempty")
    return raw


def load_value_sink_manifest(path: Path) -> tuple[ValueSinkSpecV2, ...]:
    raw = _load_document(path)
    entries = raw["entries"]
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
    if any(
        not isinstance(value[name], str) or not value[name]
        for name in ("mechanism", "path", "rationale")
    ):
        raise ValueError(f"{label} has an invalid string field")
    return ClosureGapV2(
        path=value["path"], mechanism=value["mechanism"], rationale=value["rationale"]
    )


def load_closure_gaps(path: Path) -> tuple[ClosureGapV2, ...]:
    raw = _load_document(path)
    gaps = raw["closure_gaps"]
    if not isinstance(gaps, list):
        raise ValueError("closure_gaps must be a list")
    parsed = tuple(_parse_closure_gap(gap, index=index) for index, gap in enumerate(gaps))
    if len(parsed) != len(set(parsed)):
        raise ValueError("closure_gaps entries must be unique")
    if list(parsed) != sorted(parsed):
        raise ValueError("closure_gaps must use canonical order")
    return parsed
