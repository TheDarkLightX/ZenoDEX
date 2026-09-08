"""Finite, real AutoTrader metadata inputs and pre-migration observations.

The order here is the normative semantic-word order, independent of the wire
codec. Amounts, epochs, identifiers and tags are outside the finite theorem.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from src.integration.autotrader_signals import external_signal_observation_from_dict

ROOT = Path(__file__).resolve().parents[1]
BASELINE_SOURCES = (
    "src/integration/autotrader_signals.py",
    "src/integration/autotrader_signal_registry.py",
    "src/kernels/python/strategy_external_signal_contract_v1_adapter.py",
    "src/kernels/python/strategy_external_signal_source_registry_guard_v1_adapter.py",
    "src/kernels/python/strategy_signal_provenance_guard_v1_adapter.py",
    "src/integration/tau_witness.py",
)
BASELINE = "docs/research/tau_signal_migration_20260908/baseline.json"
SOURCE_KINDS = ("route_quote_receipt", "local_protocol_state", "attested_external", "advisory_external")
TRUST_TIERS = ("advisory", "attested", "verified", "protocol")


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def legacy_payload(word: int) -> dict[str, Any]:
    if type(word) is not int or not 0 <= word < 128:
        raise ValueError("semantic_word_range")
    return {
        "schema": "zenodex/autotrader-external-signal/v1",
        "signal_id": "signal.alpha", "source_id": "provider.alpha",
        "source_kind": SOURCE_KINDS[word // 32],
        "trust_tier": TRUST_TIERS[(word // 8) % 4],
        "freshness_ok": bool((word // 4) % 2),
        "auth_ok": bool((word // 2) % 2), "advisory_only": bool(word % 2),
        "tags": ["market"],
    }


def observe(payload: dict[str, Any]) -> dict[str, object]:
    try:
        signal = external_signal_observation_from_dict(payload)
    except (TypeError, ValueError) as exc:
        return {"status": "REJECT", "error_type": type(exc).__name__, "error": str(exc)}
    normalized = signal.to_dict()
    return {"status": "ACCEPT", "normalized": normalized,
            "normalized_sha256": hashlib.sha256(canonical(normalized)).hexdigest()}


def capture_baseline(output: Path) -> None:
    """Run before the migration; refuse to overwrite captured observations."""
    rows = [{"semantic_word": word, "input": legacy_payload(word),
             "outcome": observe(legacy_payload(word))} for word in range(128)]
    packet = {
        "schema": "zenodex/tau-signal-migration-baseline/v1", "authority": "NONE",
        "sources": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                    for name in BASELINE_SOURCES},
        "rows": rows,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as stream:
        json.dump(packet, stream, sort_keys=True, indent=2)
        stream.write("\n")
