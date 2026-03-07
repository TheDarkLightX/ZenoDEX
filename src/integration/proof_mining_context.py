from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..core.dex import DexState
from ..core.proof_mining_claims import explicit_proposal_hash
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
