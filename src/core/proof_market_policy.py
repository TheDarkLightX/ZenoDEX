from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

REJECT_OK = "Ok"
REJECT_VERIFIER = "VerifierRejected"
REJECT_THEOREM_BINDING = "TheoremBindingMismatch"
REJECT_ARTIFACT_HASH = "ArtifactHashMismatch"
REJECT_PUBLIC_INPUTS = "PublicInputsMismatch"
REJECT_ASSUMPTIONS = "AssumptionsMismatch"
REJECT_VACUOUS = "VacuousProof"
REJECT_DUPLICATE_PROPOSAL = "DuplicateProposal"
REJECT_BUYER_SIGNOFF = "BuyerSignoffMissing"
REJECT_ESCROW = "EscrowNotFunded"


@dataclass(frozen=True)
class ProofMarketPolicyOutcome:
    seller_payable: bool
    full_payload_releasable: bool
    reject_code: str
    checks: Mapping[str, bool]
    advisory: Mapping[str, Any]


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_non_negative_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _reject_code_for_checks(checks: Mapping[str, bool]) -> str:
    if not checks["verifier_accepts"]:
        return REJECT_VERIFIER
    if not checks["theorem_binding_matches"]:
        return REJECT_THEOREM_BINDING
    if not checks["artifact_hash_matches"]:
        return REJECT_ARTIFACT_HASH
    if not checks["public_inputs_hash_matches"]:
        return REJECT_PUBLIC_INPUTS
    if not checks["assumptions_hash_matches"]:
        return REJECT_ASSUMPTIONS
    if not checks["non_vacuity_witness"]:
        return REJECT_VACUOUS
    if not checks["proposal_hash_unclaimed"]:
        return REJECT_DUPLICATE_PROPOSAL
    if not checks["buyer_signoff_ok"]:
        return REJECT_BUYER_SIGNOFF
    if not checks["escrow_funded"]:
        return REJECT_ESCROW
    return REJECT_OK


def evaluate_proof_market_policy(
    *,
    verifier_accepts: bool,
    theorem_binding_matches: bool,
    artifact_hash_matches: bool,
    public_inputs_hash_matches: bool,
    assumptions_hash_matches: bool,
    non_vacuity_witness: bool,
    proposal_hash_unclaimed: bool,
    buyer_signoff_required: bool,
    buyer_signoff_present: bool,
    escrow_funded: bool,
    reveal_requested: bool,
    payment_finalized_or_escrow_locked: bool,
    seller_reputation_score: int,
    seller_reputation_threshold: int = 0,
) -> ProofMarketPolicyOutcome:
    reputation_score = _require_non_negative_int(
        seller_reputation_score,
        name="seller_reputation_score",
    )
    reputation_threshold = _require_non_negative_int(
        seller_reputation_threshold,
        name="seller_reputation_threshold",
    )
    signoff_required = _require_bool(buyer_signoff_required, name="buyer_signoff_required")
    signoff_present = _require_bool(buyer_signoff_present, name="buyer_signoff_present")
    checks = {
        "verifier_accepts": _require_bool(verifier_accepts, name="verifier_accepts"),
        "theorem_binding_matches": _require_bool(
            theorem_binding_matches,
            name="theorem_binding_matches",
        ),
        "artifact_hash_matches": _require_bool(
            artifact_hash_matches,
            name="artifact_hash_matches",
        ),
        "public_inputs_hash_matches": _require_bool(
            public_inputs_hash_matches,
            name="public_inputs_hash_matches",
        ),
        "assumptions_hash_matches": _require_bool(
            assumptions_hash_matches,
            name="assumptions_hash_matches",
        ),
        "non_vacuity_witness": _require_bool(
            non_vacuity_witness,
            name="non_vacuity_witness",
        ),
        "proposal_hash_unclaimed": _require_bool(
            proposal_hash_unclaimed,
            name="proposal_hash_unclaimed",
        ),
        "buyer_signoff_ok": (not signoff_required) or signoff_present,
        "escrow_funded": _require_bool(escrow_funded, name="escrow_funded"),
        "reveal_requested": _require_bool(reveal_requested, name="reveal_requested"),
        "payment_finalized_or_escrow_locked": _require_bool(
            payment_finalized_or_escrow_locked,
            name="payment_finalized_or_escrow_locked",
        ),
    }
    reject_code = _reject_code_for_checks(checks)
    seller_payable = reject_code == REJECT_OK
    full_payload_releasable = bool(
        seller_payable
        and checks["reveal_requested"]
        and checks["payment_finalized_or_escrow_locked"]
    )
    return ProofMarketPolicyOutcome(
        seller_payable=seller_payable,
        full_payload_releasable=full_payload_releasable,
        reject_code=reject_code,
        checks=checks,
        advisory={
            "seller_reputation_score": reputation_score,
            "seller_reputation_threshold": reputation_threshold,
            "seller_reputation_meets_threshold": reputation_score >= reputation_threshold,
        },
    )
