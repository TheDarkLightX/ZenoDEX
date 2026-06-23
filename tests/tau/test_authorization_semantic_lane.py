from __future__ import annotations

from src.core.perp_submission_auth_gate import (
    REJECT_DEADLINE_EXPIRED,
    REJECT_OK,
    REJECT_SENDER_BINDING_INVALID,
    evaluate_perp_submission_auth_gate,
)


def test_signed_submission_auth_accepts_only_when_all_signed_checks_hold() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=1,
        mode_sender_bound=0,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=1,
        nonce_domain_ok=1,
        nonce_expected_ok=1,
        signature_ok=1,
        tx_sender_binding_ok=1,
    )

    assert outcome.admission_ok is True
    assert outcome.consume_nonce is True
    assert outcome.reject_code == REJECT_OK


def test_signed_submission_auth_rejects_expired_deadline_without_consuming_nonce() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=1,
        mode_sender_bound=0,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=0,
        nonce_domain_ok=1,
        nonce_expected_ok=1,
        signature_ok=1,
        tx_sender_binding_ok=1,
    )

    assert outcome.admission_ok is False
    assert outcome.consume_nonce is False
    assert outcome.reject_code == REJECT_DEADLINE_EXPIRED


def test_sender_bound_mode_requires_sender_binding_and_never_consumes_nonce() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=0,
        mode_sender_bound=1,
        signed_surface_ok=0,
        signer_role_set_ok=0,
        deadline_ok=0,
        nonce_domain_ok=0,
        nonce_expected_ok=0,
        signature_ok=0,
        tx_sender_binding_ok=0,
    )

    assert outcome.admission_ok is False
    assert outcome.consume_nonce is False
    assert outcome.reject_code == REJECT_SENDER_BINDING_INVALID
