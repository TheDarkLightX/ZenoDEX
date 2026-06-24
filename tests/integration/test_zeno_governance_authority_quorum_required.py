"""Regression tests: governance authority must fail closed without a quorum.

These tests deliberately avoid the BLS dependency: the bug they pin down was that
an empty `signature_envelopes` list skipped `verify_signature_quorum_v0` entirely
(no verification call, no error), so the authority receipt could report `ok=True`
with zero signatures. The fix appends `signature_quorum_missing` whenever no
quorum report was produced. None of these paths reach signature verification, so
they run even when py_ecc is unavailable (the main authority test module is
skipped in that case).
"""

from __future__ import annotations

import pytest

import src.integration.zeno_governance_authority as governance_authority
from src.integration.zeno_governance_authority import (
    evaluate_governance_authority_v0,
    governance_action_payload_hash_v0,
)


ROOT_B = "0x" + "bb" * 32


def _tau_receipt() -> dict[str, object]:
    return {
        "schema": "zenodex/tau_policy/host_verified_receipt/v0",
        "ok": True,
        "policy_hash": ROOT_B,
        "production_security_claim": True,
    }


def _evaluate(**overrides: object) -> dict[str, object]:
    action = {"action_id": "gov:test-action", "proposal_epoch": 10}
    args: dict[str, object] = {
        "action_id": "gov:test-action",
        "payload_kind": "governance_action",
        "payload_hash": governance_action_payload_hash_v0(action),
        "registry": {},
        "signature_envelopes": [],
        "current_epoch": 20,
        "proposal_epoch": 10,
        "min_delay_epochs": 3,
        "tau_policy_receipt": _tau_receipt(),
        "backend_descriptors": [],
        "production_mode": False,
    }
    args.update(overrides)
    return evaluate_governance_authority_v0(**args)  # type: ignore[arg-type]


def test_zero_signature_envelopes_fails_closed_with_quorum_missing() -> None:
    receipt = _evaluate()

    assert receipt["ok"] is False
    assert receipt["quorum_report"] is None
    assert "signature_quorum_missing" in receipt["errors"]


def test_non_sequence_envelopes_fails_closed_with_quorum_missing() -> None:
    receipt = _evaluate(signature_envelopes="not-a-sequence")

    assert receipt["ok"] is False
    assert receipt["quorum_report"] is None
    assert "signature_envelopes_must_be_sequence" in receipt["errors"]
    assert "signature_quorum_missing" in receipt["errors"]


def test_quorum_verification_failure_reports_single_quorum_error() -> None:
    # A non-empty envelope list against an invalid registry raises inside
    # verify_signature_quorum_v0 before any signature check. The receipt must
    # carry the precise signature_quorum_invalid error and must NOT also stack
    # signature_quorum_missing for the same root cause.
    receipt = _evaluate(signature_envelopes=[{"signer_id": "alice", "key_id": "k"}])

    assert receipt["ok"] is False
    assert receipt["quorum_report"] is None
    quorum_errors = [
        error for error in receipt["errors"] if str(error).startswith("signature_quorum_")
    ]
    assert len(quorum_errors) == 1
    assert str(quorum_errors[0]).startswith("signature_quorum_invalid:")


def test_quorum_missing_fires_in_production_mode_too() -> None:
    receipt = _evaluate(production_mode=True)

    assert receipt["ok"] is False
    assert "signature_quorum_missing" in receipt["errors"]


def test_governance_authority_errors_are_capped_and_internal_faults_hidden(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    detail = "x" * 700

    assert governance_authority._safe_governance_error(ValueError(detail)) == detail[:512]
    assert governance_authority._safe_governance_error(RuntimeError("secret " + detail)) == (
        "internal error: RuntimeError"
    )

    def faulting_root(_value: object, *, name: str) -> str:
        raise ValueError(detail)

    monkeypatch.setattr(governance_authority, "_require_root", faulting_root)

    receipt = _evaluate(tau_policy_receipt={"ok": True, "policy_hash": ROOT_B})

    assert receipt["ok"] is False
    assert "tau_policy_receipt_invalid:" + detail[:512] in receipt["errors"]
