from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..core.dex import DexState
from ..core.proof_mining_claims import (
    explicit_proposal_hash,
    validate_proof_mining_claim_artifact,
)
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .dex_snapshot import snapshot_from_state


@dataclass(frozen=True)
class ProofMiningContext:
    chain_id: str
    prev_state_hash: str
    batch_hash: str
    witness_hash: str
    dex_hash_after: str
    proposal_hash: str
    proof_scheme: str | None = None


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def proof_payload_hash(proof: Mapping[str, Any]) -> str:
    if not isinstance(proof, Mapping):
        raise TypeError("proof must be an object")
    return sha256_hex(domain_sep_bytes("dex_proof_payload", version=1) + canonical_json_bytes(dict(proof)))


def dex_snapshot_hash(state: DexState) -> str:
    return snapshot_from_state(state).commitment_hex()


def build_proof_mining_context(
    *,
    chain_id: str,
    prev_state_hash: str,
    batch_hash: str,
    proof: Mapping[str, Any],
    next_state: DexState,
    proof_scheme: str | None = None,
) -> ProofMiningContext:
    witness_hash = proof_payload_hash(proof)
    dex_hash_after = dex_snapshot_hash(next_state)
    proposal_hash = explicit_proposal_hash(
        chain_id=str(chain_id),
        prev_state_hash=str(prev_state_hash),
        batch_hash=str(batch_hash),
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
    )
    return ProofMiningContext(
        chain_id=str(chain_id),
        prev_state_hash=str(prev_state_hash),
        batch_hash=str(batch_hash),
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
        proposal_hash=proposal_hash,
        proof_scheme=None if proof_scheme is None else str(proof_scheme),
    )


def proof_mining_context_to_obj(context: ProofMiningContext) -> dict[str, Any]:
    return {
        "chain_id": str(context.chain_id),
        "prev_state_hash": str(context.prev_state_hash),
        "batch_hash": str(context.batch_hash),
        "witness_hash": str(context.witness_hash),
        "dex_hash_after": str(context.dex_hash_after),
        "proposal_hash": str(context.proposal_hash),
        "proof_scheme": None if context.proof_scheme is None else str(context.proof_scheme),
    }


def proof_mining_context_from_obj(obj: Mapping[str, Any]) -> ProofMiningContext:
    body = _require_mapping(obj, name="proof_mining_context")
    proof_scheme_raw = body.get("proof_scheme")
    if proof_scheme_raw is not None and not isinstance(proof_scheme_raw, str):
        raise TypeError("proof_mining_context.proof_scheme must be a string when present")
    return ProofMiningContext(
        chain_id=_require_str(body.get("chain_id"), name="proof_mining_context.chain_id"),
        prev_state_hash=_require_str(body.get("prev_state_hash"), name="proof_mining_context.prev_state_hash"),
        batch_hash=_require_str(body.get("batch_hash"), name="proof_mining_context.batch_hash"),
        witness_hash=_require_str(body.get("witness_hash"), name="proof_mining_context.witness_hash"),
        dex_hash_after=_require_str(body.get("dex_hash_after"), name="proof_mining_context.dex_hash_after"),
        proposal_hash=_require_str(body.get("proposal_hash"), name="proof_mining_context.proposal_hash"),
        proof_scheme=None if proof_scheme_raw is None else str(proof_scheme_raw),
    )


def derive_proof_mining_verification_flags(
    *,
    claim_artifact: Mapping[str, Any],
    context: ProofMiningContext,
) -> dict[str, bool]:
    """
    Derive trusted submit_proof flags from a verifier-produced DEX proof context.

    These flags are intentionally not taken from the claim artifact. They are
    granted only when the claim explicitly binds to the verified proof context
    emitted by the DEX execution path after proof, policy, and nonce checks.
    """

    claim = validate_proof_mining_claim_artifact(claim_artifact, require_admissible=False)
    body = _require_mapping(claim_artifact.get("body"), name="claim.body")
    binding = _require_mapping(body.get("proposal_binding"), name="claim.body.proposal_binding")
    mode = _require_str(binding.get("mode"), name="claim.body.proposal_binding.mode")
    if mode != "explicit_v1":
        raise ValueError("proof mining claim requires explicit_v1 proposal binding")
    if _require_str(claim.get("proposal_hash"), name="claim.proposal_hash") != str(context.proposal_hash):
        raise ValueError("proof mining claim proposal_hash mismatch")
    if _require_str(binding.get("chain_id"), name="claim.body.proposal_binding.chain_id") != str(context.chain_id):
        raise ValueError("proof mining claim chain_id mismatch")
    if _require_str(binding.get("prev_state_hash"), name="claim.body.proposal_binding.prev_state_hash") != str(context.prev_state_hash):
        raise ValueError("proof mining claim prev_state_hash mismatch")
    if _require_str(binding.get("batch_hash"), name="claim.body.proposal_binding.batch_hash") != str(context.batch_hash):
        raise ValueError("proof mining claim batch_hash mismatch")
    if _require_str(binding.get("witness_hash"), name="claim.body.proposal_binding.witness_hash") != str(context.witness_hash):
        raise ValueError("proof mining claim witness_hash mismatch")
    if _require_str(binding.get("dex_hash_after"), name="claim.body.proposal_binding.dex_hash_after") != str(context.dex_hash_after):
        raise ValueError("proof mining claim dex_hash_after mismatch")
    if not isinstance(context.proof_scheme, str) or not context.proof_scheme.strip():
        raise ValueError("proof mining context missing verified proof scheme")
    return {
        "proof_ok": True,
        "binding_ok": True,
        "policy_ok": True,
        "nonce_ok": True,
    }
