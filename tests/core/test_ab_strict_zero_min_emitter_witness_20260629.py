from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from tools.check_ab_strict_zero_min_emitter_witness import (
    REPORT_JSON,
    build_report,
    verify_witness_packet,
)


ROOT = Path(__file__).resolve().parents[2]


def test_ab_strict_zero_min_emitter_witness_report() -> None:
    report = build_report()
    search = report["search"]

    assert report["ok"] is True
    assert search["case_count"] == 8
    assert search["valid_packet_count"] == 8
    assert search["first_invalid_packet"] is None
    assert search["mutation_count"] == 56
    assert search["mutation_accept_count"] == 0
    assert search["first_mutation_accept"] is None
    assert report["deterministic_replay"]["ok"] is True


def test_ab_strict_zero_min_emitter_witness_packet_shape() -> None:
    report = build_report()
    packet = report["search"]["first_packet"]
    verification = verify_witness_packet(packet)

    assert verification["ok"] is True
    assert packet["schema"] == "zenodex.ab_strict_zero_min_emitter_witness_packet.v1"
    assert packet["lean_contract"]["structure"] == "StrictCompressedFullMaskEconomicWitness"
    assert packet["lean_contract"]["valid_predicate"] == "strictCompressedFullMaskEconomicWitnessValid"
    assert packet["lean_contract"]["endpoint"] == "strictCompressedFullMaskEconomicWitness_validates"
    assert packet["winner"]["mask_id"] == packet["full_mask"]
    assert packet["winner"]["selected"]["processed_reserve_in"] == (
        packet["initial_reserve_in"] + packet["executed_input"]
    )
    assert verification["checks"]["winner_covers_full_mask"] is True
    assert verification["checks"]["winner_member_of_children"] is True
    assert verification["checks"]["selected_key_dominates_full_frontier"] is True
    assert verification["checks"]["compressed_key_matches_witness"] is True
    assert verification["checks"]["empty_suffix_executable"] is True
    assert verification["checks"]["no_authority_effect"] is True


def test_ab_strict_zero_min_emitter_witness_mutations_fail_closed() -> None:
    report = build_report()
    mutation_reasons = {
        row["mutation_id"]: set(row["reasons"])
        for row in report["search"]["mutations"]
        if row["case_id"] == "n2_variant0"
    }

    assert "packet_hash_mismatch" in mutation_reasons["bad_packet_hash"]
    assert "authority_effect_present" in mutation_reasons["authority_effect_present"]
    assert "winner_missing_full_mask_bits" in mutation_reasons["winner_missing_full_mask_bit"]
    assert "winner_not_in_child_frontier" in mutation_reasons["winner_removed_from_children"]
    assert (
        "selected_key_does_not_dominate_full_frontier"
        in mutation_reasons["selected_no_longer_dominates"]
    )
    assert "winner_processed_reserve_in_mismatch" in mutation_reasons["executed_input_mismatch"]
    assert "compressed_key_mismatch_with_witness" in mutation_reasons["economic_key_mismatch"]


def test_ab_strict_zero_min_emitter_witness_rejects_manual_authority_tamper() -> None:
    report = build_report()
    packet: dict[str, Any] = copy.deepcopy(report["search"]["first_packet"])
    packet["authority_boundary"] = "settlement_authority"
    packet["packet_hash"] = "0" * 64

    verification = verify_witness_packet(packet)

    assert verification["ok"] is False
    assert "authority_boundary_mismatch" in verification["reasons"]
    assert "packet_hash_mismatch" in verification["reasons"]


def test_ab_strict_zero_min_emitter_witness_non_claims() -> None:
    report = build_report()
    non_claims = "\n".join(report["non_claims"])

    assert "not a proof of full compressed-DP induction" in non_claims
    assert "does not prove Lean-to-Python refinement" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "Nonzero min_amount_out batches are outside" in non_claims
    assert "No settlement authority" in non_claims


def test_ab_strict_zero_min_emitter_witness_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_strict_zero_min_emitter_witness.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["mutation_accept_count"] == 0
