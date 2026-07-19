from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.dex_engine import DexEngineConfig, apply_ops
from tools.dex_engine_quote_receipt_sequence_grammar_fuzz import (
    ASSET_A,
    ASSET_B,
    ASSET_C,
    ASSET_D,
    DIRECT_POOLS,
    SENDER,
    SPLIT_POOLS,
    _direct_state,
    _make_direct_ops,
    _make_split_ops,
    _split_state,
    explore_all_targets,
    explore_target,
    minimize_case,
)

ROOT_DIR = Path(__file__).resolve().parents[2]


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def _derivations(report) -> set[str]:
    return {case.derivation for case in report.cases}


def _dex_state_facts(state) -> dict:
    return {
        "balances": state.balances.get_all_balances(),
        "pools": dict(state.pools),
        "lp_balances": state.lp_balances.get_all_balances(),
        "nonces": dict(state.nonces.get_all()),
    }


def test_dex_engine_quote_receipt_sequence_direct_paths_are_stable() -> None:
    report = explore_target("direct_quote_receipt_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 5
    assert report.unique_outcome_count == 5
    assert report.unique_path_count == 5
    assert "ok:pools=2:nonces=aaaaaaaa=1" in labels
    assert "ok:pools=2:nonces=aaaaaaaa=2" in labels
    assert any("invalid quote receipt:" in label and "verifier_error='pool_snapshot_mismatch'" in label for label in labels)
    assert any("missing quote receipt witness:" in label for label in labels)
    assert any("quote receipt hash mismatch:" in label for label in labels)
    assert "DirectSeq->SingleValidAb" in derivations
    assert "DirectSeq->ValidThenIndependentValidCd" in derivations
    assert "DirectSeq->ValidThenStaleSamePool" in derivations
    assert "DirectSeq->ValidThenIndependentMissingWitness" in derivations
    assert "DirectSeq->ValidThenIndependentHashMismatch" in derivations


def test_dex_engine_quote_receipt_live_admission_floor_rejects_stale_transport_without_state_advance() -> None:
    config = DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False)
    state = _direct_state()
    first_ops = _make_direct_ops(
        pools=DIRECT_POOLS,
        pool_id="p_ab",
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=123,
        nonce=1,
    )
    first = apply_ops(
        config=config,
        state=state,
        operations=first_ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )
    assert first.ok
    assert first.state is not None

    live_state = first.state
    before_failed_step = _dex_state_facts(live_state)
    stale_transport_ops = _make_direct_ops(
        pools=DIRECT_POOLS,
        pool_id="p_ab",
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=123,
        nonce=2,
    )

    failed = apply_ops(
        config=config,
        state=live_state,
        operations=stale_transport_ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert not failed.ok
    assert failed.state is None
    assert failed.settlement is None
    assert failed.error is not None
    assert "invalid quote receipt:" in failed.error
    assert "verifier_error='pool_snapshot_mismatch'" in failed.error
    assert _dex_state_facts(live_state) == before_failed_step
    assert dict(live_state.nonces.get_all()) == {SENDER: 1}


def test_dex_engine_quote_receipt_sequence_split_paths_are_stable() -> None:
    report = explore_target("split_quote_receipt_sequence")
    labels = _labels(report)
    derivations = _derivations(report)
    assert report.total_cases == 4
    assert report.unique_outcome_count == 4
    assert report.unique_path_count == 4
    assert "ok:pools=3:nonces=aaaaaaaa=3" in labels
    assert any("duplicate quote receipt leg binding:" in label for label in labels)
    assert any("incomplete quote receipt leg coverage:" in label for label in labels)
    assert any("intent does not match quote receipt leg:" in label for label in labels)
    assert "SplitSeq->WarmupThenSplitValid" in derivations
    assert "SplitSeq->WarmupThenSplitDuplicateLeg" in derivations
    assert "SplitSeq->WarmupThenSplitIncompleteCoverage" in derivations
    assert "SplitSeq->WarmupThenSplitSwappedLegIndices" in derivations


def test_dex_engine_quote_receipt_swapped_split_leg_indices_reject_without_state_advance() -> None:
    config = DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False)
    state = _split_state()
    warmup_ops = _make_direct_ops(
        pools=SPLIT_POOLS,
        pool_id="p_cd",
        asset_in=ASSET_C,
        asset_out=ASSET_D,
        amount_in=111,
        nonce=1,
    )
    warmup = apply_ops(
        config=config,
        state=state,
        operations=warmup_ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )
    assert warmup.ok
    assert warmup.state is not None

    live_state = warmup.state
    before_failed_step = _dex_state_facts(live_state)
    swapped_ops = _make_split_ops(nonce_start=2, swapped_leg_indices=True)

    failed = apply_ops(
        config=config,
        state=live_state,
        operations=swapped_ops,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )

    assert not failed.ok
    assert failed.state is None
    assert failed.settlement is None
    assert failed.error is not None
    assert "intent does not match quote receipt leg:" in failed.error
    assert "leg_index=1" in failed.error
    assert "pool_id='p1'" in failed.error
    assert _dex_state_facts(live_state) == before_failed_step


def test_dex_engine_quote_receipt_sequence_targets_are_covered_and_deterministic() -> None:
    left = explore_all_targets()
    right = explore_all_targets()
    assert left == right
    by_name = {report.target: report for report in left}
    assert set(by_name) == {"direct_quote_receipt_sequence", "split_quote_receipt_sequence"}
    assert by_name["direct_quote_receipt_sequence"].total_cases == 5
    assert by_name["split_quote_receipt_sequence"].total_cases == 4


def test_dex_engine_quote_receipt_sequence_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [sys.executable, str(ROOT_DIR / "tools/dex_engine_quote_receipt_sequence_grammar_fuzz.py"), "--format", "json"],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-quote-receipt-sequence-grammar-fuzz/v1"
    assert {report["target"] for report in payload["reports"]} == {
        "direct_quote_receipt_sequence",
        "split_quote_receipt_sequence",
    }


def test_dex_engine_quote_receipt_sequence_minimizer_removes_dead_tail_without_changing_path() -> None:
    witness = minimize_case("direct_quote_receipt_sequence", "DirectSeq->ValidThenStaleSamePoolWithDeadTail")
    assert "invalid quote receipt:" in witness.outcome_label
    assert "verifier_error='pool_snapshot_mismatch'" in witness.outcome_label
    assert witness.path_id == "bb2bdc1803277f80"
    assert witness.original_size == 7149
    assert witness.minimized_size == 4776
    assert witness.original_size > witness.minimized_size
    assert isinstance(witness.payload, dict)
    assert witness.payload["initial"] == "direct"
    steps = witness.payload["steps"]
    assert isinstance(steps, list)
    assert len(steps) == 2


def test_dex_engine_quote_receipt_sequence_minimizer_cli_emits_expected_schema() -> None:
    raw = subprocess.check_output(
        [
            sys.executable,
            str(ROOT_DIR / "tools/dex_engine_quote_receipt_sequence_grammar_fuzz.py"),
            "--target",
            "direct_quote_receipt_sequence",
            "--minimize-derivation",
            "DirectSeq->ValidThenStaleSamePoolWithDeadTail",
            "--format",
            "json",
        ],
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == "zenodex/dex-engine-quote-receipt-sequence-minimized-witness/v1"
    witness = payload["witness"]
    assert witness["target"] == "direct_quote_receipt_sequence"
    assert witness["derivation"] == "DirectSeq->ValidThenStaleSamePoolWithDeadTail"
    assert "invalid quote receipt:" in witness["outcome_label"]
    assert witness["path_id"] == "bb2bdc1803277f80"
    assert witness["original_size"] == 7149
    assert witness["minimized_size"] == 4776


def test_dex_engine_quote_receipt_sequence_minimizer_preserves_swapped_split_leg_projection() -> None:
    witness = minimize_case("split_quote_receipt_sequence", "SplitSeq->WarmupThenSplitSwappedLegIndices")
    assert "intent does not match quote receipt leg:" in witness.outcome_label
    assert "leg_index=1" in witness.outcome_label
    assert "pool_id='p1'" in witness.outcome_label
    assert witness.path_id == "2b05cb35a3c51b22"
    assert witness.original_size == 10853
    assert witness.minimized_size == 10853
    assert isinstance(witness.payload, dict)
    assert witness.payload["initial"] == "split"
    steps = witness.payload["steps"]
    assert isinstance(steps, list)
    assert len(steps) == 2
