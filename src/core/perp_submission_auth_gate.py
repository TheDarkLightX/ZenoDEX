from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping


REJECT_OK = "Ok"
REJECT_INVALID_MODE = "InvalidMode"
REJECT_SIGNED_SURFACE_INVALID = "SignedSurfaceInvalid"
REJECT_SIGNER_ROLE_INVALID = "SignerRoleInvalid"
REJECT_DEADLINE_EXPIRED = "DeadlineExpired"
REJECT_NONCE_DOMAIN_INVALID = "NonceDomainInvalid"
REJECT_NONCE_EXPECTED_INVALID = "NonceExpectedInvalid"
REJECT_SIGNATURE_INVALID = "SignatureInvalid"
REJECT_SENDER_BINDING_INVALID = "SenderBindingInvalid"


@dataclass(frozen=True)
class PerpSubmissionAuthGateOutcome:
    signed_mode: bool
    sender_bound_mode: bool
    mode_ok: bool
    signed_surface_ok: bool
    signer_role_set_ok: bool
    deadline_ok: bool
    nonce_domain_ok: bool
    nonce_expected_ok: bool
    signature_ok: bool
    tx_sender_binding_ok: bool
    relay_allowed: bool
    consume_nonce: bool
    admission_ok: bool
    reject_code: str
    checks: Mapping[str, bool]


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


def evaluate_perp_submission_auth_gate(
    *,
    mode_signed: Any,
    mode_sender_bound: Any,
    signed_surface_ok: Any,
    signer_role_set_ok: Any,
    deadline_ok: Any,
    nonce_domain_ok: Any,
    nonce_expected_ok: Any,
    signature_ok: Any,
    tx_sender_binding_ok: Any,
) -> PerpSubmissionAuthGateOutcome:
    signed_mode = _require_flag(mode_signed, name="mode_signed")
    sender_bound_mode = _require_flag(mode_sender_bound, name="mode_sender_bound")
    signed_surface = _require_flag(signed_surface_ok, name="signed_surface_ok")
    signer_role_ok = _require_flag(signer_role_set_ok, name="signer_role_set_ok")
    deadline = _require_flag(deadline_ok, name="deadline_ok")
    nonce_domain = _require_flag(nonce_domain_ok, name="nonce_domain_ok")
    nonce_expected = _require_flag(nonce_expected_ok, name="nonce_expected_ok")
    signature = _require_flag(signature_ok, name="signature_ok")
    sender_binding = _require_flag(tx_sender_binding_ok, name="tx_sender_binding_ok")

    checks = {
        "mode_signed": signed_mode,
        "mode_sender_bound": sender_bound_mode,
        "signed_surface_ok": signed_surface,
        "signer_role_set_ok": signer_role_ok,
        "deadline_ok": deadline,
        "nonce_domain_ok": nonce_domain,
        "nonce_expected_ok": nonce_expected,
        "signature_ok": signature,
        "tx_sender_binding_ok": sender_binding,
    }

    mode_ok = bool(signed_mode != sender_bound_mode)
    relay_allowed = bool(mode_ok and signed_mode)

    if not mode_ok:
        reject_code = REJECT_INVALID_MODE
    elif sender_bound_mode and not sender_binding:
        reject_code = REJECT_SENDER_BINDING_INVALID
    elif signed_mode and not signed_surface:
        reject_code = REJECT_SIGNED_SURFACE_INVALID
    elif signed_mode and not signer_role_ok:
        reject_code = REJECT_SIGNER_ROLE_INVALID
    elif signed_mode and not deadline:
        reject_code = REJECT_DEADLINE_EXPIRED
    elif signed_mode and not nonce_domain:
        reject_code = REJECT_NONCE_DOMAIN_INVALID
    elif signed_mode and not nonce_expected:
        reject_code = REJECT_NONCE_EXPECTED_INVALID
    elif signed_mode and not signature:
        reject_code = REJECT_SIGNATURE_INVALID
    else:
        reject_code = REJECT_OK

    admission_ok = bool(reject_code == REJECT_OK)
    consume_nonce = bool(admission_ok and signed_mode)

    return PerpSubmissionAuthGateOutcome(
        signed_mode=signed_mode,
        sender_bound_mode=sender_bound_mode,
        mode_ok=mode_ok,
        signed_surface_ok=signed_surface,
        signer_role_set_ok=signer_role_ok,
        deadline_ok=deadline,
        nonce_domain_ok=nonce_domain,
        nonce_expected_ok=nonce_expected,
        signature_ok=signature,
        tx_sender_binding_ok=sender_binding,
        relay_allowed=relay_allowed,
        consume_nonce=consume_nonce,
        admission_ok=admission_ok,
        reject_code=reject_code,
        checks=checks,
    )


def perp_submission_auth_gate_error(outcome: PerpSubmissionAuthGateOutcome) -> str | None:
    if outcome.reject_code == REJECT_INVALID_MODE:
        return "invalid perps auth mode"
    if outcome.reject_code == REJECT_SIGNED_SURFACE_INVALID:
        return "signed auth surface invalid"
    if outcome.reject_code == REJECT_SIGNER_ROLE_INVALID:
        return "signer not authorized for this operation"
    if outcome.reject_code == REJECT_DEADLINE_EXPIRED:
        return "signature expired (deadline)"
    if outcome.reject_code in (REJECT_NONCE_DOMAIN_INVALID, REJECT_NONCE_EXPECTED_INVALID):
        return "nonce invalid"
    if outcome.reject_code == REJECT_SIGNATURE_INVALID:
        return "invalid signature"
    if outcome.reject_code == REJECT_SENDER_BINDING_INVALID:
        return "account_pubkey must match tx sender"
    return None
