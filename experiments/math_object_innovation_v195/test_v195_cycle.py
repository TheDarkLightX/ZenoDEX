#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"


def load_report() -> dict:
    subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
    return json.loads(REPORT.read_text(encoding="utf-8"))


def test_override_language_counts_and_audit() -> None:
    report = load_report()

    assert report["packet_count"] == 13
    assert report["valid_packet_count"] == 2
    assert report["invalid_packet_count"] == 11
    assert report["atom_count"] == 8
    assert report["forced_atom_count"] == 8
    assert report["minimal_exact_language_count"] == 1
    assert report["minimal_exact_atom_count"] == 8
    assert report["model_audit"]["total_override_language_invariant_failures"] == 0


def test_every_atom_has_private_negative_witness() -> None:
    report = load_report()

    witnesses = report["private_witnesses"]
    assert set(witnesses) == set(report["discovery_domain"]["atoms"])
    assert all(witnesses[atom] for atom in report["discovery_domain"]["atoms"])


def test_full_guard_is_unique_minimal_exact_language() -> None:
    report = load_report()

    exact = report["minimal_exact_languages"]
    assert len(exact) == 1
    assert set(exact[0]["atoms"]) == set(report["discovery_domain"]["atoms"])
    assert exact[0]["exact"] is True
    assert exact[0]["false_accept_count"] == 0
    assert exact[0]["false_reject_count"] == 0


def test_weaker_languages_have_false_accepts() -> None:
    report = load_report()

    for name in ("text_only", "authority_only", "fresh_authority_only", "cap_and_ack_only"):
        stats = report["named_language_stats"][name]
        assert stats["exact"] is False
        assert stats["false_accept_count"] > 0
        assert stats["false_reject_count"] == 0


def test_full_guard_accepts_only_expected_good_packets() -> None:
    report = load_report()

    full = report["named_language_stats"]["full_override_packet_guard"]
    assert full["exact"] is True
    accepted = [
        row["packet_id"]
        for row in report["packets"]
        if all(row[atom] for atom in full["atoms"])
    ]
    assert accepted == ["valid_route_override", "valid_uncapped_surface_override"]
