from __future__ import annotations

import json
from pathlib import Path

from tools.check_disaster_class_closure_packets import (
    DEFAULT_PACKETS,
    check_closure_packets,
)


def test_disaster_class_closure_packets_cover_crosswalk_entries() -> None:
    result = check_closure_packets(DEFAULT_PACKETS)

    assert result["ok"] is True
    assert result["packet_count"] == 20
    assert result["crosswalk_entry_count"] == 20
    assert result["covered_crosswalk_entry_count"] == result["crosswalk_entry_count"]
    assert result["missing_packet_count"] == 0
    assert result["extra_packet_count"] == 0
    assert result["crosswalk_known_axis_count"] == 125
    assert result["crosswalk_mapped_axis_count"] == 125


def test_disaster_class_closure_packets_reject_missing_packet(tmp_path: Path) -> None:
    payload = json.loads(DEFAULT_PACKETS.read_text(encoding="utf-8"))
    payload["packets"] = payload["packets"][1:]
    candidate = tmp_path / "missing_packet.json"
    candidate.write_text(json.dumps(payload), encoding="utf-8")

    result = check_closure_packets(candidate)

    assert result["ok"] is False
    assert result["missing_packet_count"] == 1
    assert any("missing closure packets" in error for error in result["errors"])


def test_disaster_class_closure_packets_reject_weak_predicate(tmp_path: Path) -> None:
    payload = json.loads(DEFAULT_PACKETS.read_text(encoding="utf-8"))
    payload["packets"][0]["bad_trace_predicate"]["conditions"] = ["too weak"]
    candidate = tmp_path / "weak_predicate.json"
    candidate.write_text(json.dumps(payload), encoding="utf-8")

    result = check_closure_packets(candidate)

    assert result["ok"] is False
    assert any("conditions must contain at least three clauses" in error for error in result["errors"])
