# [TESTER] v1

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation
from src.integration.proof_verifier import ProofVerifierConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def test_recompute_batch_proof_verifier_accepts_valid_certificate() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    prover = repo_root / "tools" / "proof_verifiers" / "recompute_batch_prover_v1.py"
    verifier = repo_root / "tools" / "proof_verifiers" / "recompute_batch_v1.py"

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "03" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    # Minimal CREATE_POOL intent (no per-intent signatures required in this test).
    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_op = create_settlement_operation(settlement)["3"]

    ops_no_proof = {"2": [intent_dict], "3": settlement_op}
    snapshot = snapshot_from_state(state).data

    # Produce proof object.
    proc = subprocess.run(
        [sys.executable, str(prover)],
        input=json.dumps({"pre_state_snapshot": snapshot, "operations": ops_no_proof}).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    proof_obj = json.loads(proc.stdout.decode("utf-8"))

    ops_with_proof = {"2": [intent_dict], "3": dict(settlement_op, proof=proof_obj)}

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=[sys.executable, str(verifier)]),
        ),
        state=state,
        operations=ops_with_proof,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_recompute_batch_proof_verifier_v2_accepts_compressed_witness() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    prover = repo_root / "tools" / "proof_verifiers" / "recompute_batch_prover_v2.py"
    verifier = repo_root / "tools" / "proof_verifiers" / "recompute_batch_v2.py"

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "04" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_op = create_settlement_operation(settlement)["3"]

    ops_no_proof = {"2": [intent_dict], "3": settlement_op}
    snapshot = snapshot_from_state(state).data

    proc = subprocess.run(
        [sys.executable, str(prover)],
        input=json.dumps({"pre_state_snapshot": snapshot, "operations": ops_no_proof}).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    proof_obj = json.loads(proc.stdout.decode("utf-8"))

    ops_with_proof = {"2": [intent_dict], "3": dict(settlement_op, proof=proof_obj)}

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=[sys.executable, str(verifier)]),
        ),
        state=state,
        operations=ops_with_proof,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_recompute_batch_proof_verifier_v3_accepts_projected_witness() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    prover = repo_root / "tools" / "proof_verifiers" / "recompute_batch_prover_v3.py"
    verifier = repo_root / "tools" / "proof_verifiers" / "recompute_batch_v3.py"

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "05" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_op = create_settlement_operation(settlement)["3"]

    ops_no_proof = {"2": [intent_dict], "3": settlement_op}
    snapshot = snapshot_from_state(state).data

    proc = subprocess.run(
        [sys.executable, str(prover)],
        input=json.dumps({"pre_state_snapshot": snapshot, "operations": ops_no_proof}).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    proof_obj = json.loads(proc.stdout.decode("utf-8"))

    ops_with_proof = {"2": [intent_dict], "3": dict(settlement_op, proof=proof_obj)}

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=[sys.executable, str(verifier)]),
        ),
        state=state,
        operations=ops_with_proof,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_recompute_batch_proof_verifier_v4_accepts_reordered_settlement_lists() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    prover = repo_root / "tools" / "proof_verifiers" / "recompute_batch_prover_v4.py"
    verifier = repo_root / "tools" / "proof_verifiers" / "recompute_batch_v4.py"

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "06" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_op = create_settlement_operation(settlement)["3"]

    # Reorder delta arrays to ensure v4 normalization quotients list ordering.
    settlement_op = dict(settlement_op)
    settlement_op["balance_deltas"] = list(reversed(settlement_op.get("balance_deltas", [])))
    settlement_op["reserve_deltas"] = list(reversed(settlement_op.get("reserve_deltas", [])))
    settlement_op["lp_deltas"] = list(reversed(settlement_op.get("lp_deltas", [])))

    ops_no_proof = {"2": [intent_dict], "3": settlement_op}
    snapshot = snapshot_from_state(state).data

    proc = subprocess.run(
        [sys.executable, str(prover)],
        input=json.dumps({"pre_state_snapshot": snapshot, "operations": ops_no_proof}).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    proof_obj = json.loads(proc.stdout.decode("utf-8"))

    ops_with_proof = {"2": [intent_dict], "3": dict(settlement_op, proof=proof_obj)}

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=[sys.executable, str(verifier)]),
        ),
        state=state,
        operations=ops_with_proof,
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error
