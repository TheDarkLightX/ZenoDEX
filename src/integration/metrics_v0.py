"""Minimal metrics snapshot helpers for operator-facing ZenoLedger status."""

from __future__ import annotations

import hashlib
import json
import time
from typing import Any, Iterable, Mapping

METRICS_SNAPSHOT_SCHEMA_V0 = "zenodex.metrics_snapshot.v0"
METRIC_SAMPLE_SCHEMA_V0 = "zenodex.metric_sample.v0"


def build_minimal_operator_samples_v0(
    *,
    ledger_height: int,
    peer_count: int,
    gossip_rejection_count: int,
    slashing_evidence_count: int,
    proof_metadata_mismatch_count: int,
    key_admission_rejection_count: int,
) -> list[dict[str, Any]]:
    """Build the small sample set used by the local operator cockpit."""

    return [
        _sample("zeno_ledger_height", ledger_height, unit="blocks"),
        _sample("zeno_peer_count", peer_count, unit="peers"),
        _sample("zeno_gossip_rejections_total", gossip_rejection_count, unit="events"),
        _sample("zeno_slashing_evidence_total", slashing_evidence_count, unit="events"),
        _sample("zeno_proof_metadata_mismatch_total", proof_metadata_mismatch_count, unit="events"),
        _sample("zeno_key_admission_rejections_total", key_admission_rejection_count, unit="events"),
    ]


def build_metrics_snapshot_v0(*, samples: Iterable[Mapping[str, Any]], source: str) -> dict[str, Any]:
    """Wrap metric samples in a deterministic, hash-addressed status snapshot."""

    normalized = [_normalize_sample(sample) for sample in samples]
    alerts = _alerts_for_samples(normalized)
    body: dict[str, Any] = {
        "schema": METRICS_SNAPSHOT_SCHEMA_V0,
        "source": source,
        "generated_at_unix": int(time.time()),
        "samples": normalized,
        "sample_count": len(normalized),
        "alerts": alerts,
        "ok": not alerts,
    }
    body["metrics_hash"] = _stable_hash({key: value for key, value in body.items() if key != "metrics_hash"})
    return body


def _sample(name: str, value: int | float, *, unit: str) -> dict[str, Any]:
    return {
        "schema": METRIC_SAMPLE_SCHEMA_V0,
        "name": name,
        "value": value,
        "unit": unit,
    }


def _normalize_sample(sample: Mapping[str, Any]) -> dict[str, Any]:
    name = str(sample.get("name", ""))
    if not name:
        raise ValueError("metric sample name must be non-empty")
    value = sample.get("value", 0)
    if isinstance(value, bool) or not isinstance(value, int | float):
        raise TypeError(f"metric sample {name} value must be numeric")
    return {
        "schema": str(sample.get("schema", METRIC_SAMPLE_SCHEMA_V0)),
        "name": name,
        "value": value,
        "unit": str(sample.get("unit", "count")),
    }


def _alerts_for_samples(samples: Iterable[Mapping[str, Any]]) -> list[dict[str, Any]]:
    alerts: list[dict[str, Any]] = []
    for sample in samples:
        name = str(sample["name"])
        value = sample["value"]
        if isinstance(value, int | float) and value < 0:
            alerts.append({"level": "error", "code": "negative_metric", "metric": name})
    return alerts


def _stable_hash(value: Mapping[str, Any]) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "0x" + hashlib.sha256(payload).hexdigest()
