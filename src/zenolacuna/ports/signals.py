"""Bounded projection checks for the fixed AutoTrader signal fixtures.

This port is deliberately source-bound.  It reads the real fixture producer
and invokes the real observation parser, while the compact V2 payload is
assembled from the fixed seven-bit metadata layout.  The result is evidence
about these 128 fixture words and their fixed identifiers/tags; it does not
claim coverage of arbitrary JSON or runtime mounting.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType

import src.integration.autotrader_signal_profile as _profile_module
import src.integration.autotrader_signals as _signals_module
import src.kernels.python.external_signal_profile_decode_v2 as _decode_module
import src.kernels.python.external_signal_profile_encode_v2 as _encode_module
import tools.tau_signal_migration_case as _migration_module
from src.integration.autotrader_signal_profile import SignalProfile, encode_profile
from src.integration.autotrader_signals import (
    EXTERNAL_SIGNAL_COMPACT_SCHEMA,
    external_signal_observation_from_dict,
)
from tools.tau_signal_migration_case import legacy_payload, observe

from ..model import Evidence

_SEMANTIC_WORDS = range(128)
_SOURCE_INDEX = {
    "route_quote_receipt": 0,
    "local_protocol_state": 1,
    "attested_external": 2,
    "advisory_external": 3,
}
_TRUST_INDEX = {
    "advisory": 0,
    "attested": 1,
    "verified": 2,
    "protocol": 3,
}
_SOURCE_MODULES: tuple[ModuleType, ...] = (
    _migration_module,
    _signals_module,
    _profile_module,
    _encode_module,
    _decode_module,
)
_FIXED_CLAIM = "FIXED_AUTOTRADER_SIGNAL_V1_V2_METADATA_FIXTURES"


@dataclass(frozen=True, slots=True)
class SignalProjectionReport:
    """Result fields for the fixed 128-word V1/V2 metadata projection.

    ``runtime_fields`` is derived from ``legacy_payload(0)`` and both
    ``missing_fields`` and ``unknown_fields`` are sorted.  ``checked_inputs128``
    is zero when the declaration is incomplete or contains unknown fields and
    is 128 after every fixture word has been compared.  ``source_sha256`` is
    ordered according to the fixed module list above.  ``authority`` remains
    ``NONE`` because this report is a bounded replay receipt, not a release
    authorization.
    """

    declared_fields: tuple[str, ...]
    runtime_fields: tuple[str, ...]
    missing_fields: tuple[str, ...]
    unknown_fields: tuple[str, ...]
    code: str
    evidence: Evidence
    checked_inputs128: int
    source_sha256: tuple[str, ...]
    authority: str = "NONE"
    claim: str = _FIXED_CLAIM
    mismatches: tuple[int, ...] = ()


def _source_hashes() -> tuple[str, ...]:
    """Hash the bytes at the already imported, fixed module paths."""

    def source_path(module: ModuleType) -> Path:
        filename = module.__file__
        if filename is None:
            raise RuntimeError("fixed source module has no file")
        return Path(filename).resolve(strict=True)

    return tuple(
        hashlib.sha256(source_path(module).read_bytes()).hexdigest()
        for module in _SOURCE_MODULES
    )


def _runtime_fields() -> tuple[str, ...]:
    payload = legacy_payload(0)
    return tuple(sorted(payload))


def _report_for_omission(
    declared_fields: tuple[str, ...],
    runtime_fields: tuple[str, ...],
    source_sha256: tuple[str, ...],
) -> SignalProjectionReport:
    missing = tuple(field for field in runtime_fields if field not in declared_fields)
    unknown = tuple(field for field in declared_fields if field not in runtime_fields)
    return SignalProjectionReport(
        declared_fields=declared_fields,
        runtime_fields=runtime_fields,
        missing_fields=missing,
        unknown_fields=unknown,
        code="MODEL_OMISSION",
        evidence=Evidence.UNKNOWN,
        checked_inputs128=0,
        source_sha256=source_sha256,
    )


def _v2_payload(word: int) -> dict[str, object]:
    v1 = legacy_payload(word)
    source_kind = v1["source_kind"]
    trust_tier = v1["trust_tier"]
    if type(source_kind) is not str or type(trust_tier) is not str:
        raise TypeError("fixture metadata field type")
    profile = SignalProfile(
        source_index=_SOURCE_INDEX[source_kind],
        trust_index=_TRUST_INDEX[trust_tier],
        freshness_ok=v1["freshness_ok"],
        auth_ok=v1["auth_ok"],
        advisory_only=v1["advisory_only"],
    )
    tags = v1["tags"]
    if not isinstance(tags, list):
        raise TypeError("fixture tags must be a list")
    return {
        "schema": EXTERNAL_SIGNAL_COMPACT_SCHEMA,
        "signal_id": v1["signal_id"],
        "source_id": v1["source_id"],
        "profile_code": encode_profile(profile),
        "tags": list(tags),
    }


def _observe_v2(payload: dict[str, object]) -> dict[str, object]:
    """Use the same parser/result shape as the fixed legacy observation."""

    try:
        signal = external_signal_observation_from_dict(payload)
    except (TypeError, ValueError) as exc:
        return {"status": "REJECT", "error_type": type(exc).__name__, "error": str(exc)}
    normalized = signal.to_dict()
    encoded = _canonical(normalized)
    return {
        "status": "ACCEPT",
        "normalized": normalized,
        "normalized_sha256": hashlib.sha256(encoded).hexdigest(),
    }


def _canonical(value: object) -> bytes:
    """Match the fixed migration fixture's canonical normalized bytes."""

    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def replay_signal_projection(declared_fields: tuple[str, ...]) -> SignalProjectionReport:
    """Replay all fixed V1/V2 metadata words under the existing signal guard.

    The declaration must be a canonical sorted tuple with exactly the fields
    emitted by ``legacy_payload``.  A missing field, duplicate, noncanonical
    order, or unknown field prevents replay and is classified as a model
    omission.  With a complete declaration, V1 and compact V2 outcomes are
    compared for every word in ``range(128)``.
    """

    runtime_fields = _runtime_fields()
    source_sha256 = _source_hashes()
    if type(declared_fields) is not tuple or any(type(field) is not str for field in declared_fields):
        return _report_for_omission((), runtime_fields, source_sha256)
    missing = tuple(field for field in runtime_fields if field not in declared_fields)
    unknown = tuple(field for field in declared_fields if field not in runtime_fields)
    canonical = declared_fields == tuple(sorted(declared_fields))
    unique = len(set(declared_fields)) == len(declared_fields)
    if missing or unknown or not canonical or not unique or declared_fields != runtime_fields:
        return _report_for_omission(declared_fields, runtime_fields, source_sha256)

    mismatches: list[int] = []
    for word in _SEMANTIC_WORDS:
        if observe(legacy_payload(word)) != _observe_v2(_v2_payload(word)):
            mismatches.append(word)
    if mismatches:
        return SignalProjectionReport(
            declared_fields=declared_fields,
            runtime_fields=runtime_fields,
            missing_fields=(),
            unknown_fields=(),
            code="SIGNAL_FIXTURE_MISMATCH",
            evidence=Evidence.UNKNOWN,
            checked_inputs128=128,
            source_sha256=source_sha256,
            mismatches=tuple(mismatches),
        )
    return SignalProjectionReport(
        declared_fields=declared_fields,
        runtime_fields=runtime_fields,
        missing_fields=(),
        unknown_fields=(),
        code="SIGNAL_FIXTURE_PARITY",
        evidence=Evidence.EXHAUSTIVE_FINITE,
        checked_inputs128=128,
        source_sha256=source_sha256,
    )


__all__ = ["SignalProjectionReport", "replay_signal_projection"]
