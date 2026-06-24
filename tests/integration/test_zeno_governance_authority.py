from __future__ import annotations

import copy
from typing import cast

import pytest

import src.integration.zeno_ledger_signature as sig
import src.integration.zenodex_external_threshold_bls as external_threshold_bls
from src.integration.zeno_governance_authority import (
    GOVERNANCE_AUTHORITY_RECEIPT_SCHEMA_V0,
    GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
    evaluate_governance_authority_v0,
    governance_action_payload_hash_v0,
)
from src.integration.zeno_key_manager_v0 import (
    BACKEND_MPC_PLACEHOLDER,
    BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
    BACKEND_THRESHOLD_BLS_LOCAL,
    BACKEND_TAU_BLS_IMPORT,
    KeyBackendDescriptor,
)
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zenodex_external_threshold_bls import (
    build_external_threshold_bls_backend_descriptor_v0,
    build_external_threshold_bls_evidence_v0,
    build_external_threshold_bls_sign_request_v0,
)


pytestmark = pytest.mark.skipif(not sig._BLS_AVAILABLE, reason="py_ecc BLS dependency unavailable")


ROOT_A = "0x" + "aa" * 32
ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32
SK1 = "0x" + ("01" * 32)
SK2 = "0x" + ("02" * 32)


def _action() -> dict[str, object]:
    return {
        "action_id": "gov:rotate-wallet-authority",
        "chain_id": "tau-testnet-1",
        "proposal_epoch": 10,
        "target": "perps_wallet_authority_profile",
        "new_profile_hash": ROOT_A,
    }


def _registry() -> dict[str, object]:
    return build_signer_registry_v0(
        registry_id="governance-registry",
        payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
        threshold=2,
        signers=[
            {
                "signer_id": "alice",
                "key_id": "key-a",
                "public_key": sig.bls_public_key_hex_from_private_key_v0(SK1),
                "weight": 1,
                "status": "active",
            },
            {
                "signer_id": "bob",
                "key_id": "key-b",
                "public_key": sig.bls_public_key_hex_from_private_key_v0(SK2),
                "weight": 1,
                "status": "active",
            },
        ],
    )


def _envelopes(payload_hash: str) -> list[dict[str, object]]:
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
            payload_hash=payload_hash,
            signer_id="alice",
            key_id="key-a",
            private_key_hex=SK1,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
            payload_hash=payload_hash,
            signer_id="bob",
            key_id="key-b",
            private_key_hex=SK2,
        ),
    ]


def _tau_receipt(*, ok: bool = True) -> dict[str, object]:
    return {
        "schema": "zenodex/tau_policy/host_verified_receipt/v0",
        "ok": ok,
        "policy_hash": ROOT_B,
        "production_security_claim": True,
    }


def _external_threshold_evidence() -> dict[str, object]:
    return build_external_threshold_bls_evidence_v0(
        provider_stack="ssv-dkg-drand-threshold-bls12-381-v1",
        service_id="wallet-threshold-service",
        service_version="1.0.0",
        binary_sha256=ROOT_A,
        public_key=sig.bls_public_key_hex_from_private_key_v0(SK1),
        threshold=2,
        participants=[
            {
                "participant_id": "alice",
                "public_share_key": sig.bls_public_key_hex_from_private_key_v0(SK1),
                "operator_key_hash": ROOT_B,
            },
            {
                "participant_id": "bob",
                "public_share_key": sig.bls_public_key_hex_from_private_key_v0(SK2),
                "operator_key_hash": ROOT_C,
            },
        ],
        dkg_transcript_hash=ROOT_B,
        audit_evidence=[
            {
                "name": "ssv-dkg-drand-kudelski-and-chainsecurity-references",
                "report_uri": "https://docs.drand.love/blog/2023/05/26/tlock-security-assessment/",
                "report_hash": ROOT_C,
                "scope": "ssv-dkg-drand-threshold-bls12-381-v1 external threshold BLS stack",
            }
        ],
    )


def _backend(kind: str = BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE) -> KeyBackendDescriptor:
    if kind == BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE:
        return build_external_threshold_bls_backend_descriptor_v0(
            key_id="tau-threshold-main",
            backend_id="external-threshold-bls",
            policy_hash=ROOT_C,
            evidence=_external_threshold_evidence(),
        )
    return KeyBackendDescriptor(
        key_id="tau-threshold-main",
        backend_kind=kind,
        backend_id="threshold-bls-test-backend",
        policy_hash=ROOT_C,
        active=True,
        no_raw_private_key_exposure=True,
        metadata={"threshold": 2, "participants": 3},
    )


def test_external_threshold_bls_receipt_rejects_inconsistent_bls_dependency_state(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(external_threshold_bls, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(external_threshold_bls, "G2Basic", None)

    ok, err = external_threshold_bls.verify_external_threshold_bls_signature_receipt_v0(
        {},
        evidence={},
        payload={},
    )

    assert ok is False
    assert err is not None
    assert "py_ecc.bls is required to verify external threshold BLS receipts" in err


@pytest.mark.parametrize("timeout_s", [float("nan"), float("inf"), True])
def test_external_threshold_bls_signer_rejects_nonfinite_timeout(timeout_s: object) -> None:
    request = build_external_threshold_bls_sign_request_v0(
        key_id="threshold-key",
        evidence_hash=ROOT_A,
        payload={"payload_kind": "governance_action"},
    )

    with pytest.raises(ValueError, match="timeout_s must be positive"):
        external_threshold_bls.run_external_threshold_bls_signer_v0(
            command=["unused-signer"],
            request=request,
            timeout_s=timeout_s,  # type: ignore[arg-type]
        )


@pytest.mark.parametrize("max_stdout_bytes", [0, True, 1.5])
def test_external_threshold_bls_signer_rejects_non_int_stdout_cap(max_stdout_bytes: object) -> None:
    request = build_external_threshold_bls_sign_request_v0(
        key_id="threshold-key",
        evidence_hash=ROOT_A,
        payload={"payload_kind": "governance_action"},
    )

    with pytest.raises(ValueError, match="max_stdout_bytes must be positive"):
        external_threshold_bls.run_external_threshold_bls_signer_v0(
            command=["unused-signer"],
            request=request,
            max_stdout_bytes=max_stdout_bytes,  # type: ignore[arg-type]
        )


def _evidence(*, placeholder: bool = False, evidence_hash: str | None = None) -> list[dict[str, object]]:
    return [
        {
            "claim_kind": "mpc",
            "evidence_hash": evidence_hash or str(_external_threshold_evidence()["evidence_hash"]),
            "ok": True,
            "placeholder": placeholder,
            "production_security_claim": True,
        }
    ]


def _evaluate(**overrides: object) -> dict[str, object]:
    action = _action()
    payload_hash = governance_action_payload_hash_v0(action)
    args = {
        "action_id": str(action["action_id"]),
        "payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
        "payload_hash": payload_hash,
        "registry": _registry(),
        "signature_envelopes": _envelopes(payload_hash),
        "current_epoch": 20,
        "proposal_epoch": 10,
        "min_delay_epochs": 3,
        "tau_policy_receipt": _tau_receipt(),
        "backend_descriptors": [_backend()],
        "evidence_claims": _evidence(),
        "required_evidence_claims": ("mpc",),
        "production_mode": True,
    }
    args.update(overrides)
    return evaluate_governance_authority_v0(**args)  # type: ignore[arg-type]


def test_governance_authority_accepts_quorum_timelock_tau_policy_and_external_threshold_backend() -> None:
    receipt = _evaluate()

    assert receipt["schema"] == GOVERNANCE_AUTHORITY_RECEIPT_SCHEMA_V0
    assert receipt["ok"] is True
    assert receipt["errors"] == ()
    assert receipt["quorum_report"]["accepted_weight"] == 2


@pytest.mark.parametrize(
    "overrides,expected_error",
    [
        ({"current_epoch": 12}, "governance_timelock_not_elapsed"),
        ({"tau_policy_receipt": _tau_receipt(ok=False)}, "tau_policy_receipt_not_ok"),
        ({"backend_descriptors": [_backend(BACKEND_MPC_PLACEHOLDER)]}, "production_placeholder_backend:mpc-placeholder"),
        ({"backend_descriptors": [_backend(BACKEND_THRESHOLD_BLS_LOCAL)]}, "production_reference_backend:threshold-bls-local"),
        ({"evidence_claims": _evidence(placeholder=True)}, "production_placeholder_evidence_claim:mpc"),
        ({"evidence_claims": _evidence(evidence_hash=ROOT_A)}, "external_threshold_bls_mpc_evidence_claim_missing:"),
        ({"required_evidence_claims": ("mpc", "tee")}, "required_evidence_claim_missing:tee"),
    ],
)
def test_governance_authority_rejects_missing_or_placeholder_production_evidence(
    overrides: dict[str, object],
    expected_error: str,
) -> None:
    receipt = _evaluate(**overrides)

    assert receipt["ok"] is False
    assert any(str(error).startswith(expected_error) for error in receipt["errors"])


@pytest.mark.parametrize("flag_name", ["active", "no_raw_private_key_exposure"])
def test_governance_authority_rejects_ints_for_backend_descriptor_bool_flags(flag_name: str) -> None:
    descriptor = _backend().public_dict()
    descriptor[flag_name] = 1

    receipt = _evaluate(backend_descriptors=[descriptor])
    errors = cast(tuple[object, ...], receipt["errors"])

    assert receipt["ok"] is False
    assert any(
        str(error).startswith(f"backend_descriptors[0]_invalid:backend_descriptors[0].{flag_name} must be bool")
        for error in errors
    )


def test_governance_authority_rejects_insufficient_or_tampered_quorum() -> None:
    action = _action()
    payload_hash = governance_action_payload_hash_v0(action)
    envelopes = _envelopes(payload_hash)

    insufficient = _evaluate(signature_envelopes=envelopes[:1])
    assert insufficient["ok"] is False
    assert any("threshold not met" in error for error in insufficient["errors"])

    tampered = copy.deepcopy(envelopes)
    tampered[1]["payload_hash"] = ROOT_A
    tampered_quorum = _evaluate(signature_envelopes=tampered)
    assert tampered_quorum["ok"] is False
    assert any("binding mismatch" in error for error in tampered_quorum["errors"])


def test_governance_authority_allows_non_placeholder_existing_tau_backend() -> None:
    receipt = _evaluate(backend_descriptors=[_backend(BACKEND_TAU_BLS_IMPORT)])

    assert receipt["ok"] is True
