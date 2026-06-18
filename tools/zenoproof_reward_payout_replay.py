#!/usr/bin/env python3
"""Replay a bounded ZenoProof reward gate through proof-mining payout checks."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.core.proof_mining_claims import build_proof_mining_claim, validate_proof_mining_claim_artifact  # noqa: E402
from src.core.proof_mining_claim_gate import PROOF_MINING_BASE_REWARD_MAX, PROOF_MINING_POOL_BALANCE_MAX  # noqa: E402
from src.core.proof_mining_manager import (  # noqa: E402
    ProofMiningManagerSnapshot,
    apply_submit_proof_packet,
    build_submit_proof_packet,
)
from src.integration.proof_mining_claimability import evaluate_proof_mining_claimability  # noqa: E402
from src.integration.proof_mining_context import (  # noqa: E402
    ProofMiningContext,
    derive_proof_mining_verification_flags,
    proof_mining_context_to_obj,
    proof_payload_hash,
)
from src.integration.proof_mining_runtime import ProofMiningRuntimeState, proof_mining_runtime_state_to_obj  # noqa: E402
from tools import zenoproof_verify as zv  # noqa: E402


SCHEMA = "zenodex.zenoproof.reward_payout_replay.v0"
DEFAULT_REGISTRY = ROOT / "tools" / "zenoproof_registry_manifest.json"
DEFAULT_UNIT_SCALE_E8 = 1_000_000
DEFAULT_NOW_EPOCH = 150
DEFAULT_REWARD_POOL_PUBKEY = "0x" + "11" * 48
DEFAULT_MINER_PUBKEY = "0x" + "22" * 48


def _plain_jsonish(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {str(key): _plain_jsonish(inner) for key, inner in value.items()}
    if isinstance(value, tuple):
        return [_plain_jsonish(inner) for inner in value]
    return value


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to an object")
    return obj


def _scaled_amount(value: Any, *, unit_scale_e8: int, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if not isinstance(unit_scale_e8, int) or isinstance(unit_scale_e8, bool) or unit_scale_e8 <= 0:
        raise ValueError("unit_scale_e8 must be positive")
    if int(value) % int(unit_scale_e8) != 0:
        raise ValueError(f"{name} is not divisible by unit_scale_e8")
    return int(value) // int(unit_scale_e8)


def _rejected_result(
    *,
    stage: str,
    errors: list[str],
    reward_gate_result: Mapping[str, Any] | None = None,
    unit_scale_e8: int = DEFAULT_UNIT_SCALE_E8,
) -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "ok": False,
        "status": "rejected",
        "stage": stage,
        "errors": list(errors),
        "unit_scale_e8": int(unit_scale_e8),
        "reward_gate_result": None if reward_gate_result is None else dict(reward_gate_result),
        "proof_mining": None,
        "not_claimed": [
            "does_not_claim_live_proof_mining_payouts",
            "does_not_claim_token_settlement",
            "does_not_claim_live_proof_network",
        ],
    }


def build_status(
    *,
    reward_gate: Mapping[str, Any] | None = None,
    registry: Mapping[str, Any] | None = None,
    now_epoch: int = DEFAULT_NOW_EPOCH,
    unit_scale_e8: int = DEFAULT_UNIT_SCALE_E8,
    reward_pool_pubkey: str = DEFAULT_REWARD_POOL_PUBKEY,
    miner_pubkey: str = DEFAULT_MINER_PUBKEY,
) -> dict[str, Any]:
    active_registry = dict(registry) if registry is not None else _load_json(DEFAULT_REGISTRY)
    active_gate = dict(reward_gate) if reward_gate is not None else zv.sample_reward_gate()
    gate_result = zv.verify_reward_gate(active_gate, active_registry, now_epoch=int(now_epoch)).to_json_obj()
    if gate_result.get("status") != "accepted":
        return _rejected_result(
            stage="zenoproof_reward_gate",
            errors=[str(error) for error in gate_result.get("errors", [])],
            reward_gate_result=gate_result,
            unit_scale_e8=unit_scale_e8,
        )

    try:
        reward_pool_before_units = _scaled_amount(
            active_gate.get("reward_pool_before_e8"),
            unit_scale_e8=int(unit_scale_e8),
            name="reward_pool_before_e8",
        )
        reward_amount_units = _scaled_amount(
            active_gate.get("reward_amount_e8"),
            unit_scale_e8=int(unit_scale_e8),
            name="reward_amount_e8",
        )
        reward_pool_after_units = _scaled_amount(
            active_gate.get("reward_pool_after_e8"),
            unit_scale_e8=int(unit_scale_e8),
            name="reward_pool_after_e8",
        )
        if reward_amount_units <= 0:
            raise ValueError("scaled reward amount must be positive")
        if reward_amount_units > PROOF_MINING_BASE_REWARD_MAX:
            raise ValueError("scaled reward amount exceeds proof-mining base reward bound")
        if reward_pool_before_units > PROOF_MINING_POOL_BALANCE_MAX:
            raise ValueError("scaled reward pool exceeds proof-mining pool bound")
        if reward_pool_before_units - reward_amount_units != reward_pool_after_units:
            raise ValueError("scaled reward pool delta mismatch")
    except (TypeError, ValueError) as exc:
        return _rejected_result(
            stage="unit_scaling",
            errors=[str(exc)],
            reward_gate_result=gate_result,
            unit_scale_e8=unit_scale_e8,
        )

    proof_payload = {
        "schema": "zenodex.zenoproof.reward_gate_payload.v0",
        "reward_gate": active_gate,
        "reward_gate_result": gate_result,
    }
    witness_hash = proof_payload_hash(proof_payload)
    chain_id = "tau-testnet-alpha"
    prev_state_hash = zv.sample_hash("zenoproof.reward_payout.prev_state")
    batch_hash = zv.sample_hash("zenoproof.reward_payout.batch")
    dex_hash_after = zv.sample_hash("zenoproof.reward_payout.dex_after")

    round_obj = {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": str(gate_result["proof_id"]),
        "winner": {
            "miner_id": str(miner_pubkey),
            "witness_sha256": witness_hash,
            "improvement_u64": int(reward_amount_units),
        },
        "candidates": [],
        "argmax_certificate": None,
    }
    claim_artifact = build_proof_mining_claim(
        round_obj=round_obj,
        round_id="zenoproof-reward-gate-v0",
        reward_pool_before=int(reward_pool_before_units),
        base_reward=int(reward_amount_units),
        epoch=0,
        proposal_slot=0,
        prover_id=2,
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        dex_hash_after=dex_hash_after,
    )
    claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=True)
    context = ProofMiningContext(
        chain_id=chain_id,
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
        proposal_hash=str(claim["proposal_hash"]),
        proof_scheme="zenoproof_v0_reward_gate",
    )
    verification_flags = derive_proof_mining_verification_flags(claim_artifact=claim_artifact, context=context)

    snapshot = ProofMiningManagerSnapshot(
        epoch=0,
        base_reward=int(reward_amount_units),
        initial_pool=int(reward_pool_before_units),
        reward_pool_balance=int(reward_pool_before_units),
        total_paid=0,
        claimed_slots={},
    )
    packet = build_submit_proof_packet(
        claim_artifact=claim_artifact,
        snapshot=snapshot,
        verification_flags=verification_flags,
    )
    manager_result = apply_submit_proof_packet(
        packet=packet,
        snapshot=snapshot,
        verification_flags=verification_flags,
    )

    runtime_state = ProofMiningRuntimeState(
        reward_pool_pubkey=str(reward_pool_pubkey),
        snapshot=snapshot,
    )
    app_state = {
        "schema": "zenodex/tau_app_state/v1",
        "proof_mining": proof_mining_runtime_state_to_obj(runtime_state),
    }
    chain_balances = {str(reward_pool_pubkey): int(reward_pool_before_units)}
    claimability = evaluate_proof_mining_claimability(
        reward_pool_pubkey=str(reward_pool_pubkey),
        app_state_json=json.dumps(app_state, sort_keys=True),
        chain_balances=chain_balances,
        claim_artifact=claim_artifact,
        tx_sender_pubkey=str(miner_pubkey),
        expected_proposal_hash=str(claim["proposal_hash"]),
        proof_mining_context_obj=proof_mining_context_to_obj(context),
    )
    claimability_obj = claimability.to_public_dict()

    manager_ok = bool(manager_result.ok and manager_result.effects is not None and manager_result.state_after is not None)
    payout_math_ok = bool(
        manager_ok
        and int(manager_result.effects["reward_amount"]) == int(reward_amount_units)
        and int(manager_result.state_after["reward_pool_balance"]) == int(reward_pool_after_units)
        and int(manager_result.state_after["total_paid"]) == int(reward_amount_units)
    )
    claimability_ok = bool(claimability.claimable)
    errors: list[str] = []
    if not manager_ok:
        errors.append(str(manager_result.error_message or manager_result.error_code or "manager rejected"))
    if not payout_math_ok:
        errors.append("manager payout math mismatch")
    if not claimability_ok:
        errors.append(str(claimability.error or "claimability rejected"))
    status = "accepted" if not errors else "rejected"

    return {
        "schema": SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "stage": "accepted" if status == "accepted" else "proof_mining_payout",
        "errors": errors,
        "unit_scale_e8": int(unit_scale_e8),
        "reward_gate_result": gate_result,
        "reward_gate_amounts_e8": {
            "reward_pool_before_e8": int(active_gate["reward_pool_before_e8"]),
            "reward_amount_e8": int(active_gate["reward_amount_e8"]),
            "reward_pool_after_e8": int(active_gate["reward_pool_after_e8"]),
        },
        "proof_mining": {
            "claim_hash": str(claim_artifact["claim_hash"]),
            "proposal_hash": str(claim["proposal_hash"]),
            "assigned_slot": int(packet.assigned_slot),
            "verification_flags": dict(verification_flags),
            "units": {
                "reward_pool_before": int(reward_pool_before_units),
                "reward_amount": int(reward_amount_units),
                "reward_pool_after": int(reward_pool_after_units),
                "base_reward": int(reward_amount_units),
                "epoch": 0,
            },
            "manager_apply": {
                "ok": bool(manager_result.ok),
                "effects": None if manager_result.effects is None else _plain_jsonish(manager_result.effects),
                "state_after": None if manager_result.state_after is None else _plain_jsonish(manager_result.state_after),
                "claimed_slots_after": {str(k): v for k, v in sorted(dict(manager_result.claimed_slots_after).items())},
                "error_code": manager_result.error_code,
                "error_message": manager_result.error_message,
            },
            "claimability": claimability_obj,
            "proof_mining_context": proof_mining_context_to_obj(context),
        },
        "not_claimed": [
            "does_not_claim_live_proof_mining_payouts",
            "does_not_claim_token_settlement",
            "does_not_claim_live_proof_network",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Replay a ZenoProof reward gate through bounded proof-mining payout checks")
    parser.add_argument("--registry", default=str(DEFAULT_REGISTRY))
    parser.add_argument("--reward-gate", help="Optional reward gate JSON path. Defaults to the built-in accepted sample.")
    parser.add_argument("--now-epoch", type=int, default=DEFAULT_NOW_EPOCH)
    parser.add_argument("--unit-scale-e8", type=int, default=DEFAULT_UNIT_SCALE_E8)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    args = parser.parse_args(argv)

    registry = _load_json(Path(args.registry))
    reward_gate = _load_json(Path(args.reward_gate)) if args.reward_gate else None
    status = build_status(
        reward_gate=reward_gate,
        registry=registry,
        now_epoch=int(args.now_epoch),
        unit_scale_e8=int(args.unit_scale_e8),
    )
    if args.format == "json":
        print(json.dumps(status, sort_keys=True))
    else:
        print(f"schema = {status['schema']}")
        print(f"status = {status['status']}")
        print(f"stage = {status['stage']}")
        print(f"unit_scale_e8 = {status['unit_scale_e8']}")
        print(f"errors = {len(status['errors'])}")
        proof_mining = status.get("proof_mining")
        if isinstance(proof_mining, Mapping):
            manager = proof_mining["manager_apply"]
            claimability = proof_mining["claimability"]
            print(f"manager_ok = {manager['ok']}")
            print(f"claimable = {claimability['claimable']}")
            print(f"reward_amount_units = {proof_mining['units']['reward_amount']}")
    return 0 if status.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
