from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Mapping, Optional

from ..core.proof_mining_claimability_gate import (
    REJECT_CODE_TO_ERROR,
    REJECT_MANAGER_REJECTED,
    ProofMiningClaimabilityGateOutcome,
    evaluate_proof_mining_claimability_gate,
)
from ..core.proof_mining_claims import validate_proof_mining_claim_artifact
from ..state.canonical import canonical_hex_fixed_allow_0x
from .proof_mining_context import ProofMiningContext, proof_mining_context_from_obj
from .proof_mining_runtime import (
    ProofMiningRuntimeState,
    apply_proof_mining_claim,
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_from_obj,
)

_APP_STATE_SCHEMA = "zenodex/tau_app_state/v1"


@dataclass(frozen=True)
class ProofMiningClaimabilityStatus:
    enabled: bool
    claimable: bool
    error: Optional[str]
    reward_pool_pubkey: Optional[str]
    proposal_hash: Optional[str]
    reward_amount: Optional[int]
    reward_pool_before: Optional[int]
    reward_pool_after: Optional[int]
    checks: Mapping[str, bool]

    def to_public_dict(self) -> dict[str, Any]:
        return {
            "enabled": bool(self.enabled),
            "claimable": bool(self.claimable),
            "error": self.error,
            "reward_pool_pubkey": self.reward_pool_pubkey,
            "proposal_hash": self.proposal_hash,
            "reward_amount": self.reward_amount,
            "reward_pool_before": self.reward_pool_before,
            "reward_pool_after": self.reward_pool_after,
            "checks": {str(k): bool(v) for k, v in dict(self.checks).items()},
        }


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _canonical_pubkey(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)
    except Exception as exc:
        raise ValueError(f"{name} must be a canonical 48-byte hex pubkey") from exc


def _canonical_asset(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    except Exception as exc:
        raise ValueError(f"{name} must be a canonical 32-byte hex asset") from exc


def _require_balance_int(value: Any, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _reward_pool_balance_from_chain(
    chain_balances: Mapping[str, Any],
    *,
    reward_pool_pubkey: str,
    reward_asset_id: str | None,
) -> int:
    raw_balance = chain_balances.get(reward_pool_pubkey, 0)
    if isinstance(raw_balance, Mapping):
        if reward_asset_id is None:
            raise ValueError("reward_asset_id is required when reward pool balance is asset-scoped")
        canonical_asset = _canonical_asset(reward_asset_id, name="reward_asset_id")
        return _require_balance_int(
            raw_balance.get(canonical_asset, 0),
            name="chain_balances[reward_pool_pubkey][reward_asset_id]",
        )
    return _require_balance_int(raw_balance, name="chain_balances[reward_pool_pubkey]")


def _load_proof_mining_state_from_app_state(app_state_json: str) -> Optional[ProofMiningRuntimeState]:
    raw = (app_state_json or "").strip()
    if not raw:
        return None
    try:
        obj = json.loads(raw)
    except Exception as exc:
        raise ValueError(f"invalid app_state_json: {exc}") from exc
    if not isinstance(obj, Mapping):
        raise ValueError("app_state_json must decode to an object")
    if obj.get("schema") != _APP_STATE_SCHEMA:
        return None
    proof_obj = obj.get("proof_mining")
    if proof_obj is None:
        return None
    return proof_mining_runtime_state_from_obj(_require_mapping(proof_obj, name="app_state.proof_mining"))


def _status_from_gate(
    *,
    gate: ProofMiningClaimabilityGateOutcome,
    checks: Mapping[str, bool],
    reward_pool_pubkey: Optional[str],
    proposal_hash: Optional[str],
    manager_error: Optional[str],
) -> ProofMiningClaimabilityStatus:
    if gate.claimable:
        error = None
    elif gate.reject_code == REJECT_MANAGER_REJECTED and manager_error:
        error = str(manager_error)
    else:
        error = REJECT_CODE_TO_ERROR.get(gate.reject_code, "proof mining manager rejected")
    if not gate.enabled:
        return ProofMiningClaimabilityStatus(
            enabled=False,
            claimable=False,
            error=error,
            reward_pool_pubkey=None,
            proposal_hash=None,
            reward_amount=None,
            reward_pool_before=None,
            reward_pool_after=None,
            checks=checks,
        )
    return ProofMiningClaimabilityStatus(
        enabled=True,
        claimable=bool(gate.claimable),
        error=error,
        reward_pool_pubkey=reward_pool_pubkey,
        proposal_hash=proposal_hash,
        reward_amount=int(gate.reward_amount),
        reward_pool_before=int(gate.reward_pool_before),
        reward_pool_after=int(gate.reward_pool_after),
        checks=checks,
    )


def evaluate_proof_mining_claimability(
    *,
    reward_pool_pubkey: Optional[str],
    app_state_json: str,
    chain_balances: Mapping[str, Any],
    claim_artifact: Mapping[str, Any],
    tx_sender_pubkey: str,
    expected_proposal_hash: str,
    reward_asset_id: str | None = None,
    proof_mining_context_obj: Mapping[str, Any] | None = None,
) -> ProofMiningClaimabilityStatus:
    checks: dict[str, bool] = {
        "reward_pool_configured": False,
        "sender_valid": False,
        "claim_valid": False,
        "winner_matches_sender": False,
        "proposal_hash_matches_context": False,
        "verified_context_present": False,
        "reward_pool_balance_non_negative": False,
        "runtime_state_present": False,
        "reward_pool_pubkey_matches_state": False,
        "reward_pool_balance_matches_state": False,
        "runtime_apply_ok": False,
    }
    canonical_pool = None
    claim = None
    verified_context: ProofMiningContext | None = None
    if reward_pool_pubkey:
        canonical_pool = _canonical_pubkey(reward_pool_pubkey, name="reward_pool_pubkey")
        checks["reward_pool_configured"] = True
    else:
        gate = evaluate_proof_mining_claimability_gate(
            reward_pool_configured=False,
            winner_matches_sender=False,
            proposal_hash_matches_context=False,
            reward_pool_balance_non_negative=False,
            runtime_state_present=False,
            reward_pool_pubkey_matches_state=False,
            reward_pool_balance_matches_state=False,
            manager_ok=False,
            reward_amount=0,
            reward_pool_before=0,
            reward_pool_after=0,
        )
        checks.update(gate.checks)
        return _status_from_gate(
            gate=gate,
            checks=checks,
            reward_pool_pubkey=None,
            proposal_hash=None,
            manager_error=None,
        )

    sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
    checks["sender_valid"] = True
    try:
        claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=True)
    except (TypeError, ValueError) as exc:
        return ProofMiningClaimabilityStatus(
            enabled=True,
            claimable=False,
            error=str(exc),
            reward_pool_pubkey=canonical_pool,
            proposal_hash=None,
            reward_amount=None,
            reward_pool_before=None,
            reward_pool_after=None,
            checks=checks,
        )
    checks["claim_valid"] = True
    if proof_mining_context_obj is not None:
        verified_context = proof_mining_context_from_obj(proof_mining_context_obj)
        checks["verified_context_present"] = True
    proposal_hash = str(claim["proposal_hash"])
    reward_amount = int(claim["payout_amount"])
    reward_pool_before = int(claim["reward_pool_before"])
    reward_pool_after = int(claim["reward_pool_after"])
    winner_pubkey = _canonical_pubkey(claim["winner"].get("miner_id"), name="claim winner.miner_id")
    checks["winner_matches_sender"] = bool(winner_pubkey == sender)
    checks["proposal_hash_matches_context"] = bool(str(expected_proposal_hash) == proposal_hash)
    actual_pool_balance = _reward_pool_balance_from_chain(
        chain_balances,
        reward_pool_pubkey=canonical_pool,
        reward_asset_id=reward_asset_id,
    )
    checks["reward_pool_balance_non_negative"] = bool(actual_pool_balance >= 0)

    runtime_state_present = False
    runtime_pubkey_matches_state = False
    runtime_balance_matches_state = False
    runtime_state = _load_proof_mining_state_from_app_state(app_state_json)
    if runtime_state is not None:
        runtime_state_present = True
        runtime_pubkey_matches_state = bool(str(runtime_state.reward_pool_pubkey) == canonical_pool)
        runtime_balance_matches_state = bool(
            runtime_pubkey_matches_state and int(runtime_state.snapshot.reward_pool_balance) == actual_pool_balance
        )
    checks["runtime_state_present"] = runtime_state_present
    checks["reward_pool_pubkey_matches_state"] = runtime_pubkey_matches_state
    checks["reward_pool_balance_matches_state"] = runtime_balance_matches_state

    manager_ok = False
    manager_error = None
    gate = None
    if (
        checks["winner_matches_sender"]
        and checks["proposal_hash_matches_context"]
        and checks["verified_context_present"]
        and checks["reward_pool_balance_non_negative"]
        and (not runtime_state_present or (runtime_pubkey_matches_state and runtime_balance_matches_state))
    ):
        if runtime_state is None:
            runtime_state = initialize_proof_mining_runtime_state(
                reward_pool_pubkey=canonical_pool,
                reward_pool_balance=actual_pool_balance,
                claim_artifact=claim_artifact,
            )
        try:
            next_state, result = apply_proof_mining_claim(
                runtime_state=runtime_state,
                claim_artifact=claim_artifact,
                actual_reward_pool_balance=actual_pool_balance,
                proof_mining_context=verified_context,
            )
            manager_ok = bool(result.ok and result.effects is not None)
            manager_error = result.error_message
            if manager_ok:
                reward_pool_before = int(runtime_state.snapshot.reward_pool_balance)
                reward_pool_after = int(next_state.snapshot.reward_pool_balance)
                reward_amount = int(result.effects.get("reward_amount", reward_pool_before - reward_pool_after))
        except (TypeError, ValueError) as exc:
            manager_error = str(exc)
    elif (
        checks["winner_matches_sender"]
        and checks["proposal_hash_matches_context"]
        and not checks["verified_context_present"]
    ):
        manager_error = "proof mining claim requires verified DEX proof context"
    gate = evaluate_proof_mining_claimability_gate(
        reward_pool_configured=checks["reward_pool_configured"],
        winner_matches_sender=checks["winner_matches_sender"],
        proposal_hash_matches_context=checks["proposal_hash_matches_context"],
        reward_pool_balance_non_negative=checks["reward_pool_balance_non_negative"],
        runtime_state_present=runtime_state_present,
        reward_pool_pubkey_matches_state=runtime_pubkey_matches_state,
        reward_pool_balance_matches_state=runtime_balance_matches_state,
        manager_ok=manager_ok,
        reward_amount=reward_amount,
        reward_pool_before=reward_pool_before,
        reward_pool_after=reward_pool_after,
    )
    checks.update(gate.checks)
    return _status_from_gate(
        gate=gate,
        checks=checks,
        reward_pool_pubkey=canonical_pool,
        proposal_hash=proposal_hash,
        manager_error=manager_error,
    )
