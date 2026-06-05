from __future__ import annotations

import dataclasses
import json
from pathlib import Path

import pytest

import tools.check_settlement_conservation_live_refinement as checker
from src.core.settlement import BalanceDelta


def test_committed_refinement_receipt_checks() -> None:
    result = checker.check_receipt(checker.DEFAULT_RECEIPT)
    assert result["ok"], result


def test_refinement_receipt_covers_all_live_asset_move_constructors() -> None:
    result = checker.check_receipt(checker.DEFAULT_RECEIPT)
    assert result["covered_constructors"] == [
        "addLiquidity",
        "createPool",
        "removeLiquidity",
        "swapInput",
        "swapOutput",
    ]


def test_refinement_receipt_includes_protocol_fee_witness() -> None:
    cases = checker.run_refinement_checks()
    protocol_fee_witnesses = [
        witness
        for case in cases
        for witness in case["witnesses"]
        if witness["constructor"] == "swapInput" and witness["params"].get("protocol_fee", 0) > 0
    ]
    assert protocol_fee_witnesses, "refinement corpus must cover protocol-fee balance+reserve split"


def test_refinement_receipt_includes_mixed_batch_composition() -> None:
    cases = checker.run_refinement_checks()
    mixed = next(case for case in cases if case["case_id"] == "mixed_existing_pool_batch")
    assert mixed["filled_intents"] >= 4
    assert set(mixed["constructors"]) == {"addLiquidity", "removeLiquidity", "swapInput", "swapOutput"}
    assert len(mixed["witnesses"]) >= 8


def test_refinement_receipt_source_hash_tamper_fails(tmp_path: Path) -> None:
    receipt = json.loads(checker.DEFAULT_RECEIPT.read_text(encoding="utf-8"))
    receipt["source_hashes"]["tools/check_settlement_conservation_live_refinement.py"] = "0" * 64
    tampered = tmp_path / "receipt.json"
    tampered.write_text(json.dumps(receipt), encoding="utf-8")

    result = checker.check_receipt(tampered)
    assert not result["ok"]
    assert any("source hash mismatch" in err for err in result["errors"])


def test_refinement_receipt_witness_tamper_fails(tmp_path: Path) -> None:
    receipt = json.loads(checker.DEFAULT_RECEIPT.read_text(encoding="utf-8"))
    receipt["cases"][0]["witnesses"][0]["balance_delta"] += 1
    tampered = tmp_path / "receipt.json"
    tampered.write_text(json.dumps(receipt), encoding="utf-8")

    result = checker.check_receipt(tampered)
    assert not result["ok"]
    assert any("case replay mismatch" in err for err in result["errors"])


def test_refinement_receipt_command_tamper_fails(tmp_path: Path) -> None:
    receipt = json.loads(checker.DEFAULT_RECEIPT.read_text(encoding="utf-8"))
    receipt["commands"][0]["returncode"] = 1
    tampered = tmp_path / "receipt.json"
    tampered.write_text(json.dumps(receipt), encoding="utf-8")

    result = checker.check_receipt(tampered)
    assert not result["ok"]
    assert any("command receipt mismatch" in err for err in result["errors"])


def test_refinement_receipt_claim_overreach_tamper_fails(tmp_path: Path) -> None:
    receipt = json.loads(checker.DEFAULT_RECEIPT.read_text(encoding="utf-8"))
    receipt["claim"] = "Production balances proof_artifact is fully cleared."
    receipt["grade"] = "S"
    tampered = tmp_path / "receipt.json"
    tampered.write_text(json.dumps(receipt), encoding="utf-8")

    result = checker.check_receipt(tampered)
    assert not result["ok"]
    assert any("claim mismatch" in err for err in result["errors"])
    assert any("grade mismatch" in err for err in result["errors"])


def test_refinement_rejects_unmodeled_balance_leak() -> None:
    scenario = checker.build_scenarios()[0]
    leaked = dataclasses.replace(
        scenario.settlement,
        balance_deltas=tuple(scenario.settlement.balance_deltas)
        + (BalanceDelta(pubkey=checker.FEE_RECIP, asset=checker.A0, delta_add=1, delta_sub=0),),
    )
    tampered = dataclasses.replace(scenario, settlement=leaked)

    # REVIEW [A- -> A]: the checker must reject a settlement that still has the
    # right shape but no longer refines to the Lean AssetMove balance/reserve
    # equations. This protects the receipt from becoming a self-reporting green
    # badge over arbitrary emitted deltas.
    with pytest.raises(checker.RefinementError, match="strong validation failed|balance deltas"):
        checker.verify_scenario(tampered)
