from __future__ import annotations

from dataclasses import dataclass

REJECT_OK = "ok"
REJECT_INVALID_MODE = "invalid_mode"
REJECT_DEADLINE_EXPIRED = "deadline_expired"
REJECT_SENDER_BINDING_INVALID = "sender_binding_invalid"


@dataclass(frozen=True)
class SubmissionAuthOutcome:
    admission_ok: bool
    consume_nonce: bool
    reject_code: str


def evaluate_modeled_submission_auth_lane(
    *,
    mode_signed: int,
    mode_sender_bound: int,
    signed_surface_ok: int,
    signer_role_set_ok: int,
    deadline_ok: int,
    nonce_domain_ok: int,
    nonce_expected_ok: int,
    signature_ok: int,
    tx_sender_binding_ok: int,
) -> SubmissionAuthOutcome:
    exactly_one_mode = bool(mode_signed) ^ bool(mode_sender_bound)
    if not exactly_one_mode:
        return SubmissionAuthOutcome(
            admission_ok=False,
            consume_nonce=False,
            reject_code=REJECT_INVALID_MODE,
        )

    if bool(mode_signed):
        all_signed_checks_hold = all(
            (
                signed_surface_ok,
                signer_role_set_ok,
                deadline_ok,
                nonce_domain_ok,
                nonce_expected_ok,
                signature_ok,
            )
        )
        if all_signed_checks_hold:
            return SubmissionAuthOutcome(
                admission_ok=True,
                consume_nonce=True,
                reject_code=REJECT_OK,
            )
        reject_code = REJECT_DEADLINE_EXPIRED if not deadline_ok else "signed_check_failed"
        return SubmissionAuthOutcome(
            admission_ok=False,
            consume_nonce=False,
            reject_code=reject_code,
        )

    if not tx_sender_binding_ok:
        return SubmissionAuthOutcome(
            admission_ok=False,
            consume_nonce=False,
            reject_code=REJECT_SENDER_BINDING_INVALID,
        )

    return SubmissionAuthOutcome(
        admission_ok=True,
        consume_nonce=False,
        reject_code=REJECT_OK,
    )


def test_signed_submission_auth_accepts_only_when_all_signed_checks_hold() -> None:
    outcome = evaluate_modeled_submission_auth_lane(
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
    outcome = evaluate_modeled_submission_auth_lane(
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
    outcome = evaluate_modeled_submission_auth_lane(
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
