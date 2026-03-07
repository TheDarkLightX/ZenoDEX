from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Mapping, Optional

from ..core.proof_mining_claims import validate_proof_mining_claim_artifact
from ..state.canonical import canonical_hex_fixed_allow_0x
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


def evaluate_proof_mining_claimability(
    *,
    reward_pool_pubkey: Optional[str],
    app_state_json: str,
    chain_balances: Mapping[str, Any],
    claim_artifact: Mapping[str, Any],
    tx_sender_pubkey: str,
    expected_proposal_hash: str,
) -> ProofMiningClaimabilityStatus:
    checks: dict[str, bool] = {
        "reward_pool_configured": False,
        "sender_valid": False,
        "claim_valid": False,
        "winner_matches_sender": False,
        "proposal_hash_matches_context": False,
        "reward_pool_balance_non_negative": False,
        "runtime_state_present": False,
        "reward_pool_pubkey_matches_state": False,
        "reward_pool_balance_matches_state": False,
        "runtime_apply_ok": False,
    }
    canonical_pool = None
    claim = None
    if reward_pool_pubkey:
        canonical_pool = _canonical_pubkey(reward_pool_pubkey, name="reward_pool_pubkey")
        checks["reward_pool_configured"] = True
    else:
        return ProofMiningClaimabilityStatus(
            enabled=False,
            claimable=False,
            error="proof mining disabled (set TAU_DEX_PROOF_MINING_POOL_PUBKEY)",
            reward_pool_pubkey=None,
            proposal_hash=None,
            reward_amount=None,
            reward_pool_before=None,
            reward_pool_after=None,
            checks=checks,
        )
    sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
    checks["sender_valid"] = True
    claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=True)
    checks["claim_valid"] = True
    winner_pubkey = _canonical_pubkey(claim["winner"].get("miner_id"), name="claim winner.miner_id")
    if winner_pubkey == sender:
        checks["winner_matches_sender"] = True
    else:
        return ProofMiningClaimabilityStatus(
            enabled=True,
            claimable=False,
            error="proof mining winner.miner_id mismatch",
            reward_pool_pubkey=canonical_pool,
            proposal_hash=str(claim["proposal_hash"]),
            reward_amount=int(claim["payout_amount"]),
            reward_pool_before=int(claim["reward_pool_before"]),
            reward_pool_after=int(claim["reward_pool_after"]),
            checks=checks,
        )
    if str(expected_proposal_hash) == str(claim["proposal_hash"]):
        checks["proposal_hash_matches_context"] = True
    else:
        return ProofMiningClaimabilityStatus(
            enabled=True,
            claimable=False,
            error="proof mining claim proposal_hash mismatch",
            reward_pool_pubkey=canonical_pool,
            proposal_hash=str(claim["proposal_hash"]),
            reward_amount=int(claim["payout_amount"]),
            reward_pool_before=int(claim["reward_pool_before"]),
            reward_pool_after=int(claim["reward_pool_after"]),
            checks=checks,
        )
    actual_pool_balance = int(chain_balances.get(canonical_pool, 0))
    if actual_pool_balance < 0:
        return ProofMiningClaimabilityStatus(
            enabled=True,
            claimable=False,
            error="reward pool chain balance must be non-negative",
            reward_pool_pubkey=canonical_pool,
            proposal_hash=str(claim["proposal_hash"]),
            reward_amount=int(claim["payout_amount"]),
            reward_pool_before=int(claim["reward_pool_before"]),
            reward_pool_after=int(claim["reward_pool_after"]),
            checks=checks,
        )
    checks["reward_pool_balance_non_negative"] = True
    runtime_state = _load_proof_mining_state_from_app_state(app_state_json)
    if runtime_state is not None:
        checks["runtime_state_present"] = True
        if str(runtime_state.reward_pool_pubkey) != canonical_pool:
            return ProofMiningClaimabilityStatus(
                enabled=True,
                claimable=False,
                error="proof mining reward pool pubkey mismatch",
                reward_pool_pubkey=canonical_pool,
                proposal_hash=str(claim["proposal_hash"]),
                reward_amount=int(claim["payout_amount"]),
                reward_pool_before=int(claim["reward_pool_before"]),
                reward_pool_after=int(claim["reward_pool_after"]),
                checks=checks,
            )
        checks["reward_pool_pubkey_matches_state"] = True
        if int(runtime_state.snapshot.reward_pool_balance) != actual_pool_balance:
            return ProofMiningClaimabilityStatus(
                enabled=True,
                claimable=False,
                error="proof mining reward pool balance drift",
                reward_pool_pubkey=canonical_pool,
                proposal_hash=str(claim["proposal_hash"]),
                reward_amount=int(claim["payout_amount"]),
                reward_pool_before=int(claim["reward_pool_before"]),
                reward_pool_after=int(claim["reward_pool_after"]),
                checks=checks,
            )
        checks["reward_pool_balance_matches_state"] = True
    else:
        runtime_state = initialize_proof_mining_runtime_state(
            reward_pool_pubkey=canonical_pool,
            reward_pool_balance=actual_pool_balance,
            claim_artifact=claim_artifact,
        )
    next_state, result = apply_proof_mining_claim(
        runtime_state=runtime_state,
        claim_artifact=claim_artifact,
        actual_reward_pool_balance=actual_pool_balance,
    )
    if result.ok and result.effects is not None:
        checks["runtime_apply_ok"] = True
        reward_after = int(next_state.snapshot.reward_pool_balance)
        reward_before = int(runtime_state.snapshot.reward_pool_balance)
        reward_amount = int(result.effects.get("reward_amount", reward_before - reward_after))
        return ProofMiningClaimabilityStatus(
            enabled=True,
            claimable=True,
            error=None,
            reward_pool_pubkey=canonical_pool,
            proposal_hash=str(claim["proposal_hash"]),
            reward_amount=reward_amount,
            reward_pool_before=reward_before,
            reward_pool_after=reward_after,
            checks=checks,
        )
    return ProofMiningClaimabilityStatus(
        enabled=True,
        claimable=False,
        error=result.error_message or "proof mining manager rejected",
        reward_pool_pubkey=canonical_pool,
        proposal_hash=str(claim["proposal_hash"]),
        reward_amount=int(claim["payout_amount"]),
        reward_pool_before=int(claim["reward_pool_before"]),
        reward_pool_after=int(claim["reward_pool_after"]),
        checks=checks,
    )
