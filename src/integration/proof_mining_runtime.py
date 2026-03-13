from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..core.proof_mining_manager import (
    ProofMiningManagerSnapshot,
    ProofMiningManagerApplyResult,
    apply_submit_proof_packet,
    build_submit_proof_packet,
)
from ..core.proof_mining_claims import validate_proof_mining_claim_artifact
from .proof_mining_context import (
    ProofMiningContext,
    derive_proof_mining_verification_flags,
)


@dataclass(frozen=True)
class ProofMiningRuntimeState:
    reward_pool_pubkey: str
    snapshot: ProofMiningManagerSnapshot


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def proof_mining_runtime_state_from_obj(obj: Mapping[str, Any]) -> ProofMiningRuntimeState:
    body = _require_mapping(obj, name="proof_mining")
    schema = _require_str(body.get("schema"), name="proof_mining.schema")
    if schema != "zenodex/proof_mining_runtime_state/v1":
        raise ValueError("unsupported proof mining runtime schema")
    claimed_entries = body.get("claimed_slots", [])
    if claimed_entries is None:
        claimed_entries = []
    if not isinstance(claimed_entries, list):
        raise TypeError("proof_mining.claimed_slots must be a list")
    claimed_slots: dict[int, str] = {}
    for idx, entry in enumerate(claimed_entries):
        row = _require_mapping(entry, name=f"proof_mining.claimed_slots[{idx}]")
        slot = _require_int(row.get("slot"), name=f"proof_mining.claimed_slots[{idx}].slot")
        proposal_hash = _require_str(row.get("proposal_hash"), name=f"proof_mining.claimed_slots[{idx}].proposal_hash")
        if slot in claimed_slots:
            raise ValueError("duplicate proof mining claimed slot")
        claimed_slots[int(slot)] = proposal_hash
    snapshot = ProofMiningManagerSnapshot(
        epoch=_require_int(body.get("epoch"), name="proof_mining.epoch"),
        base_reward=_require_int(body.get("base_reward"), name="proof_mining.base_reward"),
        initial_pool=_require_int(body.get("initial_pool"), name="proof_mining.initial_pool"),
        reward_pool_balance=_require_int(body.get("reward_pool_balance"), name="proof_mining.reward_pool_balance"),
        total_paid=_require_int(body.get("total_paid"), name="proof_mining.total_paid"),
        claimed_slots=claimed_slots,
    )
    return ProofMiningRuntimeState(
        reward_pool_pubkey=_require_str(body.get("reward_pool_pubkey"), name="proof_mining.reward_pool_pubkey"),
        snapshot=snapshot,
    )


def proof_mining_runtime_state_to_obj(state: ProofMiningRuntimeState) -> dict[str, Any]:
    claimed_slots = [
        {"slot": int(slot), "proposal_hash": str(proposal_hash)}
        for slot, proposal_hash in sorted(dict(state.snapshot.claimed_slots).items())
    ]
    return {
        "schema": "zenodex/proof_mining_runtime_state/v1",
        "reward_pool_pubkey": str(state.reward_pool_pubkey),
        "epoch": int(state.snapshot.epoch),
        "base_reward": int(state.snapshot.base_reward),
        "initial_pool": int(state.snapshot.initial_pool),
        "reward_pool_balance": int(state.snapshot.reward_pool_balance),
        "total_paid": int(state.snapshot.total_paid),
        "claimed_slots": claimed_slots,
    }


def initialize_proof_mining_runtime_state(
    *,
    reward_pool_pubkey: str,
    reward_pool_balance: int,
    claim_artifact: Mapping[str, Any],
) -> ProofMiningRuntimeState:
    claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=False)
    balance = _require_int(reward_pool_balance, name="reward_pool_balance")
    if balance < 0:
        raise ValueError("reward_pool_balance must be non-negative")
    return ProofMiningRuntimeState(
        reward_pool_pubkey=_require_str(reward_pool_pubkey, name="reward_pool_pubkey"),
        snapshot=ProofMiningManagerSnapshot(
            epoch=_require_int(claim.get("epoch"), name="claim.epoch"),
            base_reward=_require_int(claim.get("base_reward"), name="claim.base_reward"),
            initial_pool=balance,
            reward_pool_balance=balance,
            total_paid=0,
            claimed_slots={},
        ),
    )


def apply_proof_mining_claim(
    *,
    runtime_state: ProofMiningRuntimeState,
    claim_artifact: Mapping[str, Any],
    actual_reward_pool_balance: int,
    proof_mining_context: ProofMiningContext,
) -> tuple[ProofMiningRuntimeState, ProofMiningManagerApplyResult]:
    balance = _require_int(actual_reward_pool_balance, name="actual_reward_pool_balance")
    if balance != int(runtime_state.snapshot.reward_pool_balance):
        raise ValueError("reward pool balance does not match runtime snapshot")
    verification_flags = derive_proof_mining_verification_flags(
        claim_artifact=claim_artifact,
        context=proof_mining_context,
    )
    packet = build_submit_proof_packet(
        claim_artifact=claim_artifact,
        snapshot=runtime_state.snapshot,
        verification_flags=verification_flags,
    )
    result = apply_submit_proof_packet(
        packet=packet,
        snapshot=runtime_state.snapshot,
        verification_flags=verification_flags,
    )
    if not result.ok or result.state_after is None:
        return runtime_state, result
    next_state = ProofMiningRuntimeState(
        reward_pool_pubkey=str(runtime_state.reward_pool_pubkey),
        snapshot=ProofMiningManagerSnapshot(
            epoch=int(result.state_after["epoch"]),
            base_reward=int(result.state_after["base_reward"]),
            initial_pool=int(result.state_after["initial_pool"]),
            reward_pool_balance=int(result.state_after["reward_pool_balance"]),
            total_paid=int(result.state_after["total_paid"]),
            claimed_slots=dict(result.claimed_slots_after),
        ),
    )
    return next_state, result
