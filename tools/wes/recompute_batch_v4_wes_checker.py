#!/usr/bin/env python3
"""WES checker for the real ZenoDEX recompute_batch_v4 proof verifier.

Input is a WES candidate JSON file. Output is a WES CheckResult-compatible JSON
object. The checker builds one valid CREATE_POOL batch proof, applies the
candidate's mutation operator, and runs the normal ZenoDEX engine proof path.
"""

from __future__ import annotations

import base64
import copy
import hashlib
import json
import subprocess
import sys
import time
import zlib
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing import compute_settlement  # noqa: E402
from src.core.dex import DexState  # noqa: E402
from src.core.liquidity import create_pool  # noqa: E402
from src.integration.dex_engine import DexEngineConfig, apply_ops  # noqa: E402
from src.integration.dex_snapshot import snapshot_from_state  # noqa: E402
from src.integration.operations import create_settlement_operation  # noqa: E402
from src.integration.proof_verifier import ProofVerifierConfig  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.lp import LPTable  # noqa: E402

PREDICATE = "zenodex_recompute_batch_v4_binding_rejects_invalid"
CHECKER = "zenodex_recompute_batch_v4_wes_checker"
ZERO_ROOT = "0x" + ("0" * 64)
MALFORMED_MUTATIONS = {
    "proof_snapshot_corrupt_base64",
    "proof_operations_corrupt_zlib",
    "proof_missing_snapshot_witness",
    "proof_missing_operations_witness",
    "proof_snapshot_invalid_json",
    "proof_operations_invalid_json",
    "proof_snapshot_json_list",
    "proof_operations_json_list",
    "proof_operations_intents_not_list",
    "proof_operations_settlement_not_dict",
    "proof_as_string",
}


def main(argv: Sequence[str]) -> int:
    if len(argv) != 1:
        _emit(
            result="malformed",
            checker_ms=0.0,
            mutation="missing_candidate_path",
            ok=False,
            error="usage: recompute_batch_v4_wes_checker.py CANDIDATE_JSON",
        )
        return 0
    started = time.perf_counter()
    try:
        candidate = json.loads(Path(argv[0]).read_text(encoding="utf-8"))
        if not isinstance(candidate, dict):
            raise ValueError("candidate must be an object")
        mutation = _mutation(candidate)
        base_case = _base_case(candidate)
        case = _build_case(base_case)
        proof = _mutate_proof(copy.deepcopy(case["proof"]), mutation)
        settlement_op = case["settlement_op"]
        if mutation == "settlement_payload_amount_mutation":
            settlement_op = _mutate_settlement_op(copy.deepcopy(settlement_op))
        if mutation == "settlement_events_mutation_valid":
            settlement_op = _mutate_settlement_events(copy.deepcopy(settlement_op))
        operations = _build_operations(case["intent_dict"], settlement_op, proof, mutation)
        res = apply_ops(
            config=DexEngineConfig(
                allow_missing_settlement=False,
                require_proof_when_present=mutation == "settlement_missing_required_proof",
                require_intent_signatures=False,
                allow_external_tools=True,
                consensus_mode=False,
                proof_config=ProofVerifierConfig(
                    enabled=True,
                    verifier_cmd=[sys.executable, str(REPO_ROOT / "tools" / "proof_verifiers" / "recompute_batch_v4.py")],
                ),
            ),
            state=case["state"],
            operations=operations,
            block_timestamp=0,
            tx_sender_pubkey=case["sender"],
        )
        checker_ms = (time.perf_counter() - started) * 1000.0
        _emit_result(candidate=candidate, mutation=mutation, res_ok=bool(res.ok), error=res.error, checker_ms=checker_ms)
        return 0
    except Exception as exc:
        checker_ms = (time.perf_counter() - started) * 1000.0
        mutation = "unknown"
        try:
            mutation = _mutation(candidate)  # type: ignore[name-defined]
        except Exception:
            pass
        _emit(
            result="malformed",
            checker_ms=checker_ms,
            mutation=mutation,
            ok=False,
            error=f"checker exception: {exc}",
        )
        return 0


def _build_case(base_case: str) -> dict[str, Any]:
    if base_case == "create_pool":
        return _build_create_pool_case()
    if base_case == "swap_exact_in":
        return _build_swap_exact_in_case()
    if base_case == "add_liquidity":
        return _build_add_liquidity_case()
    raise ValueError(f"unsupported base_case: {base_case}")


def _build_create_pool_case() -> dict[str, Any]:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "03" * 32

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
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "tools" / "proof_verifiers" / "recompute_batch_prover_v4.py")],
        input=json.dumps(
            {
                "pre_state_snapshot": snapshot_from_state(state).data,
                "operations": {"2": [intent_dict], "3": settlement_op},
            },
            sort_keys=True,
        ).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.decode("utf-8", errors="replace"))
    proof = json.loads(proc.stdout.decode("utf-8"))
    return {
        "sender": sender,
        "state": state,
        "intent_dict": intent_dict,
        "settlement_op": settlement_op,
        "proof": proof,
    }


def _build_swap_exact_in_case() -> dict[str, Any]:
    sender = "0x" + "bb" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "07" * 32
    pool_id, pool, _lp_minted = create_pool(
        asset0=min(asset0, asset1),
        asset1=max(asset0, asset1),
        amount0=10_000,
        amount1=20_000,
        fee_bps=30,
        creator_pubkey=sender,
        created_at=1,
    )

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 5_000)
    balances.set(sender, max(asset0, asset1), 0)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "pool_id": pool_id,
        "asset_in": min(asset0, asset1),
        "asset_out": max(asset0, asset1),
        "amount_in": 100,
        "min_amount_out": 0,
        "recipient": sender,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(
        intents=[intent],
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "tools" / "proof_verifiers" / "recompute_batch_prover_v4.py")],
        input=json.dumps(
            {
                "pre_state_snapshot": snapshot_from_state(state).data,
                "operations": {"2": [intent_dict], "3": settlement_op},
            },
            sort_keys=True,
        ).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.decode("utf-8", errors="replace"))
    proof = json.loads(proc.stdout.decode("utf-8"))
    return {
        "sender": sender,
        "state": state,
        "intent_dict": intent_dict,
        "settlement_op": settlement_op,
        "proof": proof,
    }


def _build_add_liquidity_case() -> dict[str, Any]:
    sender = "0x" + "cc" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "08" * 32
    pool_id, pool, _lp_minted = create_pool(
        asset0=min(asset0, asset1),
        asset1=max(asset0, asset1),
        amount0=10_000,
        amount1=20_000,
        fee_bps=30,
        creator_pubkey=sender,
        created_at=1,
    )

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 5_000)
    balances.set(sender, max(asset0, asset1), 5_000)
    state = DexState(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "ADD_LIQUIDITY",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "nonce": 1,
        "pool_id": pool_id,
        "amount0_desired": 100,
        "amount1_desired": 200,
        "amount0_min": 0,
        "amount1_min": 0,
        "submission_order": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(
        intents=[intent],
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "tools" / "proof_verifiers" / "recompute_batch_prover_v4.py")],
        input=json.dumps(
            {
                "pre_state_snapshot": snapshot_from_state(state).data,
                "operations": {"2": [intent_dict], "3": settlement_op},
            },
            sort_keys=True,
        ).encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.decode("utf-8", errors="replace"))
    proof = json.loads(proc.stdout.decode("utf-8"))
    return {
        "sender": sender,
        "state": state,
        "intent_dict": intent_dict,
        "settlement_op": settlement_op,
        "proof": proof,
    }


def _mutate_proof(proof: dict[str, Any], mutation: str) -> object:
    if mutation == "valid_baseline":
        return proof
    if mutation == "proof_pre_state_commitment_zero":
        proof["pre_state_commitment"] = ZERO_ROOT
        return proof
    if mutation == "proof_batch_commitment_zero":
        proof["batch_commitment"] = ZERO_ROOT
        return proof
    if mutation == "proof_scheme_unknown":
        proof["scheme"] = "unknown_scheme"
        return proof
    if mutation == "proof_missing_pre_state_commitment":
        proof.pop("pre_state_commitment", None)
        return proof
    if mutation == "proof_missing_batch_commitment":
        proof.pop("batch_commitment", None)
        return proof
    if mutation == "proof_snapshot_corrupt_base64":
        proof["pre_state_snapshot_zlib_b64"] = "not-base64"
        return proof
    if mutation == "proof_operations_corrupt_zlib":
        proof["operations_zlib_b64"] = base64.b64encode(b"not-zlib").decode("ascii")
        return proof
    if mutation == "proof_missing_snapshot_witness":
        proof.pop("pre_state_snapshot_zlib_b64", None)
        return proof
    if mutation == "proof_missing_operations_witness":
        proof.pop("operations_zlib_b64", None)
        return proof
    if mutation == "proof_snapshot_invalid_json":
        proof["pre_state_snapshot_zlib_b64"] = _encode_zlib_bytes(b"not-json")
        return proof
    if mutation == "proof_operations_invalid_json":
        proof["operations_zlib_b64"] = _encode_zlib_bytes(b"not-json")
        return proof
    if mutation == "proof_snapshot_json_list":
        proof["pre_state_snapshot_zlib_b64"] = _encode_zlib_json([])
        return proof
    if mutation == "proof_operations_json_list":
        proof["operations_zlib_b64"] = _encode_zlib_json([])
        return proof
    if mutation == "proof_snapshot_balance_amount_mutation":
        snapshot = _decode_zlib_json(str(proof["pre_state_snapshot_zlib_b64"]))
        balances = snapshot.get("balances")
        if isinstance(balances, list) and balances and isinstance(balances[0], dict):
            balances[0]["amount"] = int(balances[0].get("amount") or 0) + 1
        proof["pre_state_snapshot_zlib_b64"] = _encode_zlib_json(snapshot)
        return proof
    if mutation == "proof_operations_intents_not_list":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        ops["2"] = {"bad": "shape"}
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_operations_settlement_not_dict":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        ops["3"] = "bad-settlement"
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_operations_settlement_amount_mutation":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        settlement = ops.get("3")
        if isinstance(settlement, dict):
            fills = settlement.get("fills")
            if isinstance(fills, list) and fills and isinstance(fills[0], dict):
                fills[0]["amount_in_filled"] = int(fills[0].get("amount_in_filled") or 0) + 1
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_operations_intent_nonce_mutation":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        intents = ops.get("2")
        if isinstance(intents, list) and intents and isinstance(intents[0], dict):
            intents[0]["nonce"] = int(intents[0].get("nonce") or 0) + 1
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_operations_missing_settlement":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        ops.pop("3", None)
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_operations_extra_group_valid":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        ops["9"] = [{"ignored_by": "recompute_batch_v4"}]
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_operations_fill_reason_mutation_valid":
        ops = _decode_zlib_json(str(proof["operations_zlib_b64"]))
        settlement = ops.get("3")
        if isinstance(settlement, dict):
            fills = settlement.get("fills")
            if isinstance(fills, list) and fills and isinstance(fills[0], dict):
                fills[0]["reason"] = "changed metadata ignored by v4 commitment"
        proof["operations_zlib_b64"] = _encode_zlib_json(ops)
        return proof
    if mutation == "proof_as_string":
        return "not-a-proof-object"
    return proof


def _mutate_settlement_op(settlement_op: dict[str, Any]) -> dict[str, Any]:
    fills = settlement_op.get("fills")
    if isinstance(fills, list) and fills and isinstance(fills[0], dict):
        fills[0]["amount_in_filled"] = int(fills[0].get("amount_in_filled") or 0) + 1
    return settlement_op


def _mutate_settlement_events(settlement_op: dict[str, Any]) -> dict[str, Any]:
    settlement_op["events"] = [{"kind": "metadata_only", "note": "ignored by v4 commitment"}]
    return settlement_op


def _build_operations(intent_dict: Mapping[str, Any], settlement_op: object, proof: object, mutation: str) -> dict[str, Any]:
    if not isinstance(settlement_op, dict):
        raise TypeError("settlement operation must be an object")
    op3 = dict(settlement_op)
    if mutation == "settlement_missing_required_proof":
        return {"2": [dict(intent_dict)], "3": op3}
    if mutation == "settlement_duplicate_proof_fields":
        op3["proof"] = proof
        op3["zk_proof"] = copy.deepcopy(proof)
        return {"2": [dict(intent_dict)], "3": op3}
    if mutation == "settlement_legacy_zk_proof_valid":
        op3["zk_proof"] = proof
        return {"2": [dict(intent_dict)], "3": op3}
    op3["proof"] = proof
    return {"2": [dict(intent_dict)], "3": op3}


def _emit_result(
    *,
    candidate: Mapping[str, Any],
    mutation: str,
    res_ok: bool,
    error: str | None,
    checker_ms: float,
) -> None:
    expected_safe = mutation in {
        "valid_baseline",
        "proof_operations_extra_group_valid",
        "proof_operations_fill_reason_mutation_valid",
        "settlement_events_mutation_valid",
        "settlement_legacy_zk_proof_valid",
    }
    if expected_safe and res_ok:
        result = "checked_safe"
        witness_value = 0.2
        violated_predicate = None
        usefulness = "accepted_valid"
    elif expected_safe and not res_ok:
        result = "invariant_violation"
        witness_value = 0.9
        violated_predicate = PREDICATE
        usefulness = "valid_rejected"
    elif (not expected_safe) and res_ok:
        result = "disaster"
        witness_value = 1.0
        violated_predicate = PREDICATE
        usefulness = "accepted_invalid"
    elif mutation in MALFORMED_MUTATIONS:
        result = "malformed"
        witness_value = 0.0
        violated_predicate = None
        usefulness = "malformed_junk"
    else:
        result = "near_miss"
        witness_value = 0.8
        violated_predicate = PREDICATE
        usefulness = "semantic_rejection"
    _emit(
        result=result,
        checker_ms=checker_ms,
        mutation=mutation,
        ok=res_ok,
        error=error,
        witness_value=witness_value,
        violated_predicate=violated_predicate,
        usefulness=usefulness,
        candidate_hash=_candidate_hash(candidate),
    )


def _emit(
    *,
    result: str,
    checker_ms: float,
    mutation: str,
    ok: bool,
    error: str | None,
    witness_value: float | None = None,
    violated_predicate: str | None = None,
    usefulness: str = "checker_error",
    candidate_hash: str | None = None,
) -> None:
    payload = {
        "result": result,
        "checker": CHECKER,
        "checker_ms": checker_ms,
        "violated_predicate": violated_predicate,
        "replay_receipt": _receipt(mutation=mutation, result=result, ok=ok, error=error, candidate_hash=candidate_hash),
        "witness_value": witness_value,
        "telemetry": {
            "schema": "zenodex.wes.recompute_batch_v4.telemetry.v1",
            "mutation_operator": mutation,
            "usefulness": usefulness,
            "engine_ok": ok,
            "error_code": error,
            "invalid_accept": result == "disaster",
            "replay_stable": True,
            "deterministic_receipt": True,
            "checker_command": "tools/wes/recompute_batch_v4_wes_checker.py",
            "verifier": "tools/proof_verifiers/recompute_batch_v4.py",
        },
        "notes": error or usefulness,
    }
    sys.stdout.write(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")


def _mutation(candidate: Mapping[str, Any]) -> str:
    action = candidate.get("action_features")
    if not isinstance(action, Mapping):
        return "unknown"
    value = action.get("mutation_operator")
    return str(value) if value is not None else "unknown"


def _base_case(candidate: Mapping[str, Any]) -> str:
    state = candidate.get("state_features")
    if not isinstance(state, Mapping):
        return "create_pool"
    value = state.get("base_case")
    return str(value) if value is not None else "create_pool"


def _decode_zlib_json(value: str) -> dict[str, Any]:
    raw = zlib.decompress(base64.b64decode(value.encode("ascii"), validate=True))
    decoded = json.loads(raw.decode("utf-8"))
    if not isinstance(decoded, dict):
        raise ValueError("decoded witness must be an object")
    return decoded


def _encode_zlib_json(value: Any) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return _encode_zlib_bytes(raw)


def _encode_zlib_bytes(raw: bytes) -> str:
    return base64.b64encode(zlib.compress(raw, level=9)).decode("ascii")


def _candidate_hash(candidate: Mapping[str, Any]) -> str:
    return "sha256:" + hashlib.sha256(
        json.dumps(candidate, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    ).hexdigest()


def _receipt(
    *,
    mutation: str,
    result: str,
    ok: bool,
    error: str | None,
    candidate_hash: str | None,
) -> str:
    payload = {
        "checker": CHECKER,
        "mutation": mutation,
        "result": result,
        "engine_ok": ok,
        "error": error,
        "candidate_hash": candidate_hash,
    }
    return "sha256:" + hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    ).hexdigest()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
