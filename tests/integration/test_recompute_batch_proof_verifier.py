# [TESTER] v1

from __future__ import annotations

import base64
import json
import subprocess
import sys
import zlib
from pathlib import Path

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.fees import FeeAccumulatorState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.operations import create_settlement_operation
from src.integration.proof_verifier import ProofVerifierConfig
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import compute_pool_id


def _zlib_b64_json(value: object) -> str:
    raw = json.dumps(value, separators=(",", ":")).encode("utf-8")
    return base64.b64encode(zlib.compress(raw)).decode("ascii")


def _decode_zlib_b64_json(value: str) -> object:
    raw = zlib.decompress(base64.b64decode(value.encode("ascii"))).decode("utf-8")
    return json.loads(raw)


def _create_pool_projected_proof(
    *,
    prover_name: str,
    verifier_name: str,
    intent_byte: str,
) -> tuple[Path, dict[str, object], dict[str, object]]:
    repo_root = Path(__file__).resolve().parents[2]
    prover = repo_root / "tools" / "proof_verifiers" / prover_name
    verifier = repo_root / "tools" / "proof_verifiers" / verifier_name

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + intent_byte * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        fee_accumulator=FeeAccumulatorState(dust=77),
    )

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

    proc = subprocess.run(
        [sys.executable, str(prover)],
        input=json.dumps({"pre_state_snapshot": snapshot_from_state(state).data, "operations": ops_no_proof}).encode(
            "utf-8"
        ),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    proof_obj = json.loads(proc.stdout.decode("utf-8"))
    projected = _decode_zlib_b64_json(proof_obj["pre_state_snapshot_zlib_b64"])
    assert isinstance(projected, dict)
    return verifier, proof_obj, projected


def _verify_recompute_payload(verifier: Path, proof_obj: dict[str, object]) -> dict[str, object]:
    payload = {
        "schema": "zenodex_proof",
        "schema_version": 1,
        "pre_state_commitment": proof_obj["pre_state_commitment"],
        "batch_commitment": proof_obj["batch_commitment"],
        "proof": proof_obj,
    }
    proc = subprocess.run(
        [sys.executable, str(verifier)],
        input=json.dumps(payload).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    result = json.loads(proc.stdout.decode("utf-8"))
    assert isinstance(result, dict)
    return result


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
    state = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        fee_accumulator=FeeAccumulatorState(dust=77),
    )

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
    state = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        fee_accumulator=FeeAccumulatorState(dust=77),
    )

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
    state = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        fee_accumulator=FeeAccumulatorState(dust=77),
    )

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
    projected = _decode_zlib_b64_json(proof_obj["pre_state_snapshot_zlib_b64"])
    assert isinstance(projected, dict)
    assert projected["fee_accumulator"] == {"dust": 0}
    assert projected["vault"] is None
    assert projected["oracle"] is None

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


@pytest.mark.parametrize(
    ("prover_name", "verifier_name", "scheme"),
    [
        ("recompute_batch_prover_v3.py", "recompute_batch_v3.py", "recompute_batch_v3"),
        ("recompute_batch_prover_v4.py", "recompute_batch_v4.py", "recompute_batch_v4"),
    ],
)
def test_projected_recompute_batch_proofs_reject_unbound_fee_dust(
    prover_name: str,
    verifier_name: str,
    scheme: str,
) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    prover = repo_root / "tools" / "proof_verifiers" / prover_name
    verifier = repo_root / "tools" / "proof_verifiers" / verifier_name

    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + ("07" if scheme.endswith("_v3") else "08") * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        fee_accumulator=FeeAccumulatorState(dust=123),
    )

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

    proc = subprocess.run(
        [sys.executable, str(prover)],
        input=json.dumps(
            {"pre_state_snapshot": snapshot_from_state(state).data, "operations": ops_no_proof}
        ).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr.decode("utf-8", errors="replace")
    proof_obj = json.loads(proc.stdout.decode("utf-8"))

    projected = _decode_zlib_b64_json(proof_obj["pre_state_snapshot_zlib_b64"])
    assert isinstance(projected, dict)
    projected["fee_accumulator"] = {"dust": 123}
    tampered_proof = dict(proof_obj)
    tampered_proof["pre_state_snapshot_zlib_b64"] = _zlib_b64_json(projected)

    payload = {
        "schema": "zenodex_proof",
        "schema_version": 1,
        "pre_state_commitment": proof_obj["pre_state_commitment"],
        "batch_commitment": proof_obj["batch_commitment"],
        "proof": tampered_proof,
    }
    verify_proc = subprocess.run(
        [sys.executable, str(verifier)],
        input=json.dumps(payload).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert verify_proc.returncode == 0, verify_proc.stderr.decode("utf-8", errors="replace")
    result = json.loads(verify_proc.stdout.decode("utf-8"))
    assert result["ok"] is False
    assert "unbound fee_accumulator dust" in result["error"]


@pytest.mark.parametrize(
    ("prover_name", "verifier_name", "intent_byte"),
    [
        ("recompute_batch_prover_v3.py", "recompute_batch_v3.py", "09"),
        ("recompute_batch_prover_v4.py", "recompute_batch_v4.py", "0a"),
    ],
)
@pytest.mark.parametrize(
    ("mutation_name", "expected_error"),
    [
        ("balance", "unbound balance state"),
        ("pool", "unbound pool state"),
        ("lp_balance", "unbound lp balance state"),
        ("lp_mint_timestamp", "cannot set LP mint timestamp for an empty balance"),
        ("lp_duration_risk", "unbound lp_duration_risk state"),
        ("nonce", "unbound nonce state"),
    ],
)
def test_projected_recompute_batch_proofs_reject_unbound_projected_state(
    prover_name: str,
    verifier_name: str,
    intent_byte: str,
    mutation_name: str,
    expected_error: str,
) -> None:
    verifier, proof_obj, projected = _create_pool_projected_proof(
        prover_name=prover_name,
        verifier_name=verifier_name,
        intent_byte=intent_byte,
    )

    unbound_pubkey = "0x" + "fe" * 48
    unbound_asset0 = "0x" + "98" * 32
    unbound_asset1 = "0x" + "99" * 32
    unbound_pool_id = compute_pool_id(unbound_asset0, unbound_asset1, 30)
    if mutation_name == "balance":
        projected["balances"].append({"pubkey": unbound_pubkey, "asset": unbound_asset0, "amount": 1})
    elif mutation_name == "pool":
        projected["pools"].append(
            {
                "pool_id": unbound_pool_id,
                "asset0": unbound_asset0,
                "asset1": unbound_asset1,
                "reserve0": 1,
                "reserve1": 2,
                "fee_bps": 30,
                "lp_supply": 3,
                "status": "ACTIVE",
                "created_at": 1,
                "curve_tag": "CPMM",
                "curve_params": "",
            }
        )
    elif mutation_name == "lp_balance":
        projected["lp_balances"].append({"pubkey": unbound_pubkey, "pool_id": unbound_pool_id, "amount": 1})
    elif mutation_name == "lp_mint_timestamp":
        projected["lp_mint_timestamps"].append(
            {"pubkey": unbound_pubkey, "pool_id": unbound_pool_id, "last_mint_timestamp": 1}
        )
    elif mutation_name == "lp_duration_risk":
        projected["lp_duration_risk"].append(
            {
                "pubkey": unbound_pubkey,
                "pool_id": unbound_pool_id,
                "last_remove_timestamp": 1,
                "churn_tier": 1,
                "last_churn_update_timestamp": 1,
            }
        )
    elif mutation_name == "nonce":
        projected["nonces"].append({"pubkey": unbound_pubkey, "last_nonce": 1})
    else:
        raise AssertionError(f"unhandled mutation {mutation_name}")

    tampered_proof = dict(proof_obj)
    tampered_proof["pre_state_snapshot_zlib_b64"] = _zlib_b64_json(projected)

    result = _verify_recompute_payload(verifier, tampered_proof)

    assert result["ok"] is False
    assert expected_error in str(result["error"])


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
    state = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        fee_accumulator=FeeAccumulatorState(dust=88),
    )

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
    projected = _decode_zlib_b64_json(proof_obj["pre_state_snapshot_zlib_b64"])
    assert isinstance(projected, dict)
    assert projected["fee_accumulator"] == {"dust": 0}
    assert projected["vault"] is None
    assert projected["oracle"] is None

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


@pytest.mark.parametrize(
    ("verifier_name", "scheme"),
    [
        ("recompute_batch_v2.py", "recompute_batch_v2"),
        ("recompute_batch_v3.py", "recompute_batch_v3"),
        ("recompute_batch_v4.py", "recompute_batch_v4"),
    ],
)
def test_recompute_batch_verifiers_reject_invalid_snapshot_witness_fail_closed(
    verifier_name: str,
    scheme: str,
) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    verifier = repo_root / "tools" / "proof_verifiers" / verifier_name
    payload = {
        "schema": "zenodex_proof",
        "schema_version": 1,
        "pre_state_commitment": "0x1",
        "batch_commitment": "0x2",
        "proof": {
            "scheme": scheme,
            "pre_state_commitment": "0x1",
            "batch_commitment": "0x2",
            "pre_state_snapshot_zlib_b64": "%%%not-base64%%%",
            "operations": {},
        },
    }
    proc = subprocess.run(
        [sys.executable, str(verifier)],
        input=json.dumps(payload).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0
    result = json.loads(proc.stdout.decode("utf-8"))
    assert result["ok"] is False
    assert "invalid embedded witness" in result["error"]
    assert "invalid base64" in result["error"]


@pytest.mark.parametrize(
    ("verifier_name", "scheme"),
    [
        ("recompute_batch_v2.py", "recompute_batch_v2"),
        ("recompute_batch_v3.py", "recompute_batch_v3"),
        ("recompute_batch_v4.py", "recompute_batch_v4"),
    ],
)
def test_recompute_batch_verifiers_reject_invalid_operations_witness_fail_closed(
    verifier_name: str,
    scheme: str,
) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    verifier = repo_root / "tools" / "proof_verifiers" / verifier_name
    payload = {
        "schema": "zenodex_proof",
        "schema_version": 1,
        "pre_state_commitment": "0x1",
        "batch_commitment": "0x2",
        "proof": {
            "scheme": scheme,
            "pre_state_commitment": "0x1",
            "batch_commitment": "0x2",
            "pre_state_snapshot": {},
            "operations_zlib_b64": "%%%not-base64%%%",
        },
    }
    proc = subprocess.run(
        [sys.executable, str(verifier)],
        input=json.dumps(payload).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0
    result = json.loads(proc.stdout.decode("utf-8"))
    assert result["ok"] is False
    assert "invalid embedded witness" in result["error"]
    assert "invalid base64" in result["error"]
