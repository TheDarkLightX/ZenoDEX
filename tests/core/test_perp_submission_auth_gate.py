from __future__ import annotations

import pytest

from src.core.perp_submission_auth_gate import (
    REJECT_DEADLINE_EXPIRED,
    REJECT_INVALID_MODE,
    REJECT_NONCE_DOMAIN_INVALID,
    REJECT_NONCE_EXPECTED_INVALID,
    REJECT_SENDER_BINDING_INVALID,
    REJECT_SIGNATURE_INVALID,
    REJECT_SIGNED_SURFACE_INVALID,
    REJECT_SIGNER_ROLE_INVALID,
    evaluate_perp_submission_auth_gate,
    perp_submission_auth_gate_error,
)


def test_perp_submission_auth_gate_accepts_signed_relayable_path() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=1,
        mode_sender_bound=0,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=1,
        nonce_domain_ok=1,
        nonce_expected_ok=1,
        signature_ok=1,
        tx_sender_binding_ok=0,
    )
    assert outcome.admission_ok is True
    assert outcome.relay_allowed is True
    assert outcome.consume_nonce is True
    assert outcome.reject_code == "Ok"


def test_perp_submission_auth_gate_rejects_signed_deadline_before_nonce_or_signature() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=1,
        mode_sender_bound=0,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=0,
        nonce_domain_ok=1,
        nonce_expected_ok=0,
        signature_ok=0,
        tx_sender_binding_ok=1,
    )
    assert outcome.admission_ok is False
    assert outcome.consume_nonce is False
    assert outcome.reject_code == REJECT_DEADLINE_EXPIRED
    assert perp_submission_auth_gate_error(outcome) == "signature expired (deadline)"


def test_perp_submission_auth_gate_rejects_nonce_replay_without_consumption() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=1,
        mode_sender_bound=0,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=1,
        nonce_domain_ok=1,
        nonce_expected_ok=0,
        signature_ok=1,
        tx_sender_binding_ok=1,
    )
    assert outcome.admission_ok is False
    assert outcome.relay_allowed is True
    assert outcome.consume_nonce is False
    assert outcome.reject_code == REJECT_NONCE_EXPECTED_INVALID
    assert perp_submission_auth_gate_error(outcome) == "nonce invalid"


def test_perp_submission_auth_gate_rejects_sender_bound_mismatch_without_nonce_consumption() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=0,
        mode_sender_bound=1,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=1,
        nonce_domain_ok=1,
        nonce_expected_ok=1,
        signature_ok=1,
        tx_sender_binding_ok=0,
    )
    assert outcome.admission_ok is False
    assert outcome.relay_allowed is False
    assert outcome.consume_nonce is False
    assert outcome.reject_code == REJECT_SENDER_BINDING_INVALID
    assert perp_submission_auth_gate_error(outcome) == "account_pubkey must match tx sender"


def test_perp_submission_auth_gate_rejects_invalid_mode() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=1,
        mode_sender_bound=1,
        signed_surface_ok=1,
        signer_role_set_ok=1,
        deadline_ok=1,
        nonce_domain_ok=1,
        nonce_expected_ok=1,
        signature_ok=1,
        tx_sender_binding_ok=1,
    )
    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_INVALID_MODE
    assert perp_submission_auth_gate_error(outcome) == "invalid perps auth mode"


def _signed_kwargs() -> dict[str, object]:
    return {
        "mode_signed": 1,
        "mode_sender_bound": 0,
        "signed_surface_ok": 1,
        "signer_role_set_ok": 1,
        "deadline_ok": 1,
        "nonce_domain_ok": 1,
        "nonce_expected_ok": 1,
        "signature_ok": 1,
        "tx_sender_binding_ok": 1,
    }


def test_perp_submission_auth_gate_accepts_sender_bound_path_without_nonce_consumption() -> None:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=0,
        mode_sender_bound=1,
        signed_surface_ok=0,
        signer_role_set_ok=0,
        deadline_ok=0,
        nonce_domain_ok=0,
        nonce_expected_ok=0,
        signature_ok=0,
        tx_sender_binding_ok=1,
    )

    assert outcome.admission_ok is True
    assert outcome.relay_allowed is False
    assert outcome.consume_nonce is False
    assert outcome.reject_code == "Ok"


@pytest.mark.parametrize(
    ("overrides", "expected_reject", "expected_error"),
    [
        ({"signed_surface_ok": 0}, REJECT_SIGNED_SURFACE_INVALID, "signed auth surface invalid"),
        ({"signer_role_set_ok": 0}, REJECT_SIGNER_ROLE_INVALID, "signer not authorized for this operation"),
        ({"nonce_domain_ok": 0}, REJECT_NONCE_DOMAIN_INVALID, "nonce invalid"),
        ({"signature_ok": 0}, REJECT_SIGNATURE_INVALID, "invalid signature"),
    ],
)
def test_perp_submission_auth_gate_signed_error_precedence(
    overrides: dict[str, object],
    expected_reject: str,
    expected_error: str,
) -> None:
    kwargs = _signed_kwargs()
    kwargs.update(overrides)

    outcome = evaluate_perp_submission_auth_gate(**kwargs)

    assert outcome.admission_ok is False
    assert outcome.consume_nonce is False
    assert outcome.reject_code == expected_reject
    assert perp_submission_auth_gate_error(outcome) == expected_error
