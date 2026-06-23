from __future__ import annotations

import pytest

from src.core.proof_market_policy import (
    REJECT_ARTIFACT_HASH,
    REJECT_ASSUMPTIONS,
    REJECT_BUYER_SIGNOFF,
    REJECT_DUPLICATE_PROPOSAL,
    REJECT_ESCROW,
    REJECT_OK,
    REJECT_PUBLIC_INPUTS,
    REJECT_THEOREM_BINDING,
    REJECT_VACUOUS,
    REJECT_VERIFIER,
    evaluate_proof_market_policy,
)


def _valid_kwargs() -> dict[str, object]:
    return {
        "verifier_accepts": True,
        "theorem_binding_matches": True,
        "artifact_hash_matches": True,
        "public_inputs_hash_matches": True,
        "assumptions_hash_matches": True,
        "non_vacuity_witness": True,
        "proposal_hash_unclaimed": True,
        "buyer_signoff_required": True,
        "buyer_signoff_present": True,
        "escrow_funded": True,
        "reveal_requested": True,
        "payment_finalized_or_escrow_locked": True,
        "seller_reputation_score": 3,
        "seller_reputation_threshold": 2,
    }


def test_proof_market_policy_accepts_bound_nonvacuous_escrowed_proof() -> None:
    outcome = evaluate_proof_market_policy(**_valid_kwargs())

    assert outcome.reject_code == REJECT_OK
    assert outcome.seller_payable is True
    assert outcome.full_payload_releasable is True
    assert outcome.checks["buyer_signoff_ok"] is True
    assert outcome.advisory["seller_reputation_meets_threshold"] is True


@pytest.mark.parametrize(
    ("override", "reject_code"),
    [
        ({"verifier_accepts": False}, REJECT_VERIFIER),
        ({"theorem_binding_matches": False}, REJECT_THEOREM_BINDING),
        ({"artifact_hash_matches": False}, REJECT_ARTIFACT_HASH),
        ({"public_inputs_hash_matches": False}, REJECT_PUBLIC_INPUTS),
        ({"assumptions_hash_matches": False}, REJECT_ASSUMPTIONS),
        ({"non_vacuity_witness": False}, REJECT_VACUOUS),
        ({"proposal_hash_unclaimed": False}, REJECT_DUPLICATE_PROPOSAL),
        ({"buyer_signoff_present": False}, REJECT_BUYER_SIGNOFF),
        ({"escrow_funded": False}, REJECT_ESCROW),
    ],
)
def test_proof_market_policy_rejects_unsafe_sale_boundaries(
    override: dict[str, object],
    reject_code: str,
) -> None:
    kwargs = _valid_kwargs()
    kwargs.update(override)

    outcome = evaluate_proof_market_policy(**kwargs)

    assert outcome.reject_code == reject_code
    assert outcome.seller_payable is False
    assert outcome.full_payload_releasable is False


def test_reputation_is_advisory_and_cannot_override_verifier_rejection() -> None:
    kwargs = _valid_kwargs()
    kwargs.update({"verifier_accepts": False, "seller_reputation_score": 1_000})

    outcome = evaluate_proof_market_policy(**kwargs)

    assert outcome.reject_code == REJECT_VERIFIER
    assert outcome.seller_payable is False
    assert outcome.advisory["seller_reputation_meets_threshold"] is True


def test_low_reputation_does_not_block_a_verified_bound_sale() -> None:
    kwargs = _valid_kwargs()
    kwargs.update({"seller_reputation_score": 0, "seller_reputation_threshold": 5})

    outcome = evaluate_proof_market_policy(**kwargs)

    assert outcome.reject_code == REJECT_OK
    assert outcome.seller_payable is True
    assert outcome.advisory["seller_reputation_meets_threshold"] is False


def test_full_proof_payload_is_not_released_before_payment_lock() -> None:
    kwargs = _valid_kwargs()
    kwargs["payment_finalized_or_escrow_locked"] = False

    outcome = evaluate_proof_market_policy(**kwargs)

    assert outcome.reject_code == REJECT_OK
    assert outcome.seller_payable is True
    assert outcome.full_payload_releasable is False


def test_buyer_signoff_is_required_only_when_policy_requires_it() -> None:
    kwargs = _valid_kwargs()
    kwargs.update({"buyer_signoff_required": False, "buyer_signoff_present": False})

    outcome = evaluate_proof_market_policy(**kwargs)

    assert outcome.reject_code == REJECT_OK
    assert outcome.seller_payable is True
    assert outcome.checks["buyer_signoff_ok"] is True


def test_policy_rejects_invalid_reputation_fields() -> None:
    kwargs = _valid_kwargs()
    kwargs["seller_reputation_score"] = -1

    with pytest.raises(ValueError, match="seller_reputation_score must be non-negative"):
        evaluate_proof_market_policy(**kwargs)
