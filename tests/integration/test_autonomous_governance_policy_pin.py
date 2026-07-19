"""Tests for the quorum-gated autonomous-governance policy-pin lineage.

Two tiers:

- BLS-real tests (skipped when py_ecc is unavailable, same gate as the main
  authority test module): genesis and rotation under an actual verified
  2-of-2 signature quorum, payload binding, replay/rollback refusal, and the
  composition with the trajectory runner (pin -> expected_policy_hash).
- BLS-independent fail-closed tests: zero envelopes (relies on the
  signature_quorum_missing fix being load-bearing), malformed policies,
  tampered pins, chain-walk forgeries.
"""

from __future__ import annotations

from copy import deepcopy
from typing import Any, Callable, TypeVar, cast

import pytest

import src.integration.zeno_ledger_signature as sig
from src.integration.autonomous_governance_policy_pin import (
    AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1,
    GENESIS_PREVIOUS_PIN_HASH,
    ROTATION_ACTION_ID_V1,
    build_genesis_policy_pin_v1,
    rotate_policy_pin_v1,
    rotation_action_payload_v1,
    signer_registry_hash_v1,
    verify_policy_pin_chain_v1,
    verify_policy_pin_v1,
)
from src.integration.autonomous_governance_q_policy import (
    policy_content_hash_v1,
)
from src.integration.autonomous_governance_trajectory import (
    run_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_governance_authority import (
    GOVERNANCE_ACTION_PAYLOAD_KIND_V0,
    governance_action_payload_hash_v0,
)
from src.integration.zeno_key_manager_v0 import BACKEND_TAU_BLS_IMPORT, KeyBackendDescriptor
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_surface_q_policy_v1,
)

ROOT_B = "0x" + "bb" * 32
ROOT_C = "0x" + "cc" * 32
SK1 = "0x" + ("01" * 32)
SK2 = "0x" + ("02" * 32)
SURROGATE = "ev\ud800il"
_TestFunc = TypeVar("_TestFunc", bound=Callable[..., Any])


def _policy(policy_id: str = "pin_test_policy_a") -> dict[str, Any]:
    policy = deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    policy["policy_id"] = policy_id
    policy["policy_hash"] = policy_content_hash_v1(policy)
    return cast(dict[str, Any], policy)


def _registry() -> dict[str, Any]:
    registry = build_signer_registry_v0(
        registry_id="autogov-pin-registry",
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
    return cast(dict[str, Any], registry)


def _tau_receipt() -> dict[str, Any]:
    return {
        "schema": "zenodex/tau_policy/host_verified_receipt/v0",
        "ok": True,
        "policy_hash": ROOT_B,
        "production_security_claim": True,
    }


def _backend() -> KeyBackendDescriptor:
    return KeyBackendDescriptor(
        key_id="autogov-pin-key",
        backend_kind=BACKEND_TAU_BLS_IMPORT,
        backend_id="tau-bls-import-backend",
        policy_hash=ROOT_C,
        active=True,
        no_raw_private_key_exposure=True,
        metadata={"threshold": 2, "participants": 2},
    )


def _envelopes_for(payload_hash: str) -> list[dict[str, Any]]:
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


def _genesis_payload_hash(policy: dict[str, Any], registry: dict[str, Any]) -> str:
    payload = rotation_action_payload_v1(
        new_policy_hash=policy["policy_hash"],
        previous_pin_hash=GENESIS_PREVIOUS_PIN_HASH,
        rotation_index=0,
        registry_hash=signer_registry_hash_v1(registry),
        proposal_epoch=10,
    )
    return str(governance_action_payload_hash_v0(payload))


def _build_genesis(policy: dict[str, Any], registry: dict[str, Any], **overrides: Any) -> dict[str, Any]:
    kwargs: dict[str, Any] = {
        "policy": policy,
        "registry": registry,
        "signature_envelopes": _envelopes_for(_genesis_payload_hash(policy, registry)),
        "current_epoch": 20,
        "proposal_epoch": 10,
        "min_delay_epochs": 3,
        "tau_policy_receipt": _tau_receipt(),
        "backend_descriptors": [_backend()],
        "production_mode": True,
    }
    kwargs.update(overrides)
    return build_genesis_policy_pin_v1(**kwargs)


def _bls_test(fn: _TestFunc) -> _TestFunc:
    return cast(
        _TestFunc,
        pytest.mark.skipif(
            not sig._BLS_AVAILABLE,
            reason="py_ecc BLS dependency unavailable",
        )(fn),
    )


# --------------------------------------------------------------------------- #
# BLS-real lineage
# --------------------------------------------------------------------------- #
@_bls_test
def test_genesis_pin_requires_and_records_real_quorum() -> None:
    policy = _policy()
    registry = _registry()

    rotation = _build_genesis(policy, registry)

    assert rotation["ok"] is True, rotation["errors"]
    pin = rotation["pin"]
    assert pin["schema"] == AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1
    assert pin["policy_hash"] == policy["policy_hash"]
    assert pin["previous_pin_hash"] == GENESIS_PREVIOUS_PIN_HASH
    assert pin["rotation_index"] == 0
    assert rotation["authority_receipt"]["ok"] is True
    assert rotation["authority_receipt"]["quorum_report"]["accepted_weight"] == 2
    assert rotation["rotation_payload"]["action_id"] == ROTATION_ACTION_ID_V1

    verification = verify_policy_pin_v1(pin=pin, policy=policy, registry=registry)
    assert verification["ok"] is True
    assert verification["policy_bound"] is True
    assert verification["registry_bound"] is True


@_bls_test
def test_rotation_links_lineage_and_chain_verifies() -> None:
    policy_a = _policy("pin_test_policy_a")
    policy_b = _policy("pin_test_policy_b")
    registry = _registry()
    genesis = _build_genesis(policy_a, registry)
    head = genesis["pin"]

    payload = rotation_action_payload_v1(
        new_policy_hash=policy_b["policy_hash"],
        previous_pin_hash=head["pin_hash"],
        rotation_index=1,
        registry_hash=signer_registry_hash_v1(registry),
        proposal_epoch=30,
    )
    rotation = rotate_policy_pin_v1(
        current_pin=head,
        policy=policy_b,
        registry=registry,
        signature_envelopes=_envelopes_for(governance_action_payload_hash_v0(payload)),
        current_epoch=40,
        proposal_epoch=30,
        min_delay_epochs=3,
        tau_policy_receipt=_tau_receipt(),
        backend_descriptors=[_backend()],
    )

    assert rotation["ok"] is True, rotation["errors"]
    new_pin = rotation["pin"]
    assert new_pin["previous_pin_hash"] == head["pin_hash"]
    assert new_pin["rotation_index"] == 1
    assert new_pin["policy_hash"] == policy_b["policy_hash"]

    chain = verify_policy_pin_chain_v1([head, new_pin])
    assert chain["ok"] is True
    assert chain["head_pin_hash"] == new_pin["pin_hash"]


@_bls_test
def test_quorum_signed_for_other_policy_cannot_rotate_this_one() -> None:
    policy_a = _policy("pin_test_policy_a")
    policy_b = _policy("pin_test_policy_b")
    registry = _registry()

    # Envelopes sign the rotation payload for policy A; attempting to pin
    # policy B with them must fail signature binding inside the quorum check.
    rotation = _build_genesis(
        policy_b, registry,
        signature_envelopes=_envelopes_for(_genesis_payload_hash(policy_a, registry)),
    )

    assert rotation["ok"] is False
    assert rotation["pin"] == {}
    assert "authority_rejected" in rotation["errors"]
    # The payload hash is part of the signed message, so the cross-policy
    # replay surfaces as an invalid-signature quorum failure.
    assert any(
        str(error).startswith("authority:signature_quorum_invalid")
        for error in rotation["errors"]
    )


@_bls_test
def test_rotation_approval_cannot_be_replayed_after_head_advances() -> None:
    policy_a = _policy("pin_test_policy_a")
    policy_b = _policy("pin_test_policy_b")
    policy_c = _policy("pin_test_policy_c")
    registry = _registry()
    genesis = _build_genesis(policy_a, registry)
    head = genesis["pin"]

    def rotate(policy: dict[str, Any], pin: dict[str, Any], index: int, envelopes: list[dict[str, Any]]) -> dict[str, Any]:
        return rotate_policy_pin_v1(
            current_pin=pin,
            policy=policy,
            registry=registry,
            signature_envelopes=envelopes,
            current_epoch=40,
            proposal_epoch=30,
            min_delay_epochs=3,
            tau_policy_receipt=_tau_receipt(),
            backend_descriptors=[_backend()],
        )

    payload_b = rotation_action_payload_v1(
        new_policy_hash=policy_b["policy_hash"],
        previous_pin_hash=head["pin_hash"],
        rotation_index=1,
        registry_hash=signer_registry_hash_v1(registry),
        proposal_epoch=30,
    )
    envelopes_b = _envelopes_for(governance_action_payload_hash_v0(payload_b))
    rotation_b = rotate(policy_b, head, 1, envelopes_b)
    assert rotation_b["ok"] is True
    head_b = rotation_b["pin"]

    # Replaying the SAME approved envelopes from the new head must fail: the
    # payload now binds a different previous_pin_hash and rotation_index.
    replayed = rotate(policy_b, head_b, 2, envelopes_b)
    assert replayed["ok"] is False
    assert "authority_rejected" in replayed["errors"]

    # And a rollback (rotating from the stale genesis head again) yields a pin
    # whose previous_pin_hash no longer matches the live head — the chain walk
    # refuses the forked lineage.
    payload_c = rotation_action_payload_v1(
        new_policy_hash=policy_c["policy_hash"],
        previous_pin_hash=head["pin_hash"],
        rotation_index=1,
        registry_hash=signer_registry_hash_v1(registry),
        proposal_epoch=30,
    )
    rotation_c = rotate(policy_c, head, 1, _envelopes_for(governance_action_payload_hash_v0(payload_c)))
    assert rotation_c["ok"] is True
    forked = verify_policy_pin_chain_v1([head, head_b, rotation_c["pin"]])
    assert forked["ok"] is False
    assert any("chain_link_mismatch" in str(error) or "rotation_index_mismatch" in str(error) for error in forked["errors"])


@_bls_test
def test_pin_composes_with_trajectory_runner() -> None:
    policy = _policy()
    registry = _registry()
    genesis = _build_genesis(policy, registry)
    pin = genesis["pin"]

    pin_check = verify_policy_pin_v1(pin=pin, policy=policy)
    assert pin_check["ok"] is True

    receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state={
            "fee_bps": 30, "buyburn_bps": 6_000, "stakers_bps": 0,
            "reserve_bps": 2_000, "hosts_bps": 2_000, "mcr_bps": 11_000,
            "ccr_bps": 15_000, "staker_bps": 5_000, "funding_cap_bps": 120,
        },
        steps=[
            {
                "observation": {
                    "observed_price_bps": 10_500, "target_price_bps": 10_000,
                    "volatility_bps": 250, "divergence_bps": 10,
                    "freshness_lag_epochs": 0, "liquidity_depth_bps": 5_000,
                },
                "current_epoch": 100,
                "proposal_epoch": 76,
            }
        ],
        expected_policy_hash=pin["policy_hash"],
        trajectory_budget={"fee_bps": 50, "funding_cap_bps": 25, "buyburn_bps": 200, "reserve_bps": 200},
    )
    assert receipt["ok"] is True
    assert receipt["policy_hash"] == pin["policy_hash"]

    # A policy that does not match the pin is refused by the runner pin gate.
    other = _policy("pin_test_policy_b")
    mismatched = run_autonomous_governance_surface_trajectory_v1(
        policy=other,
        initial_surface_state={
            "fee_bps": 30, "buyburn_bps": 6_000, "stakers_bps": 0,
            "reserve_bps": 2_000, "hosts_bps": 2_000, "mcr_bps": 11_000,
            "ccr_bps": 15_000, "staker_bps": 5_000, "funding_cap_bps": 120,
        },
        steps=[
            {
                "observation": {
                    "observed_price_bps": 10_500, "target_price_bps": 10_000,
                    "volatility_bps": 250, "divergence_bps": 10,
                    "freshness_lag_epochs": 0, "liquidity_depth_bps": 5_000,
                },
                "current_epoch": 100,
                "proposal_epoch": 76,
            }
        ],
        expected_policy_hash=pin["policy_hash"],
    )
    assert mismatched["status"] == "rejected_structural"
    assert "policy_hash_mismatch" in mismatched["errors"]


# --------------------------------------------------------------------------- #
# BLS-independent fail-closed paths
# --------------------------------------------------------------------------- #
def test_zero_envelopes_cannot_create_a_pin() -> None:
    # Composition with the v1 quorum fix: with no signatures the authority
    # receipt fails closed, so no pin can exist.
    rotation = build_genesis_policy_pin_v1(
        policy=_policy(),
        registry={"payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0},
        signature_envelopes=[],
        current_epoch=20,
        proposal_epoch=10,
        min_delay_epochs=3,
        tau_policy_receipt=_tau_receipt(),
        backend_descriptors=[_backend()],
        production_mode=False,
    )

    assert rotation["ok"] is False
    assert rotation["pin"] == {}
    assert "authority_rejected" in rotation["errors"]
    assert "authority:signature_quorum_missing" in rotation["errors"]


def test_malformed_policy_cannot_be_pinned() -> None:
    policy = _policy()
    del policy["safety"]["min_cooldown_epochs"]
    policy["policy_hash"] = policy_content_hash_v1(policy)

    rotation = build_genesis_policy_pin_v1(
        policy=policy,
        registry={"payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0},
        signature_envelopes=[],
        current_epoch=20,
        proposal_epoch=10,
        min_delay_epochs=3,
        tau_policy_receipt=_tau_receipt(),
        backend_descriptors=[_backend()],
        production_mode=False,
    )

    assert rotation["ok"] is False
    assert "incomplete_safety_envelope:min_cooldown_epochs" in rotation["errors"]


def test_authority_evidence_inputs_are_gated_before_policy_rotation() -> None:
    surrogate_claim = {
        "claim_kind": SURROGATE,
        "evidence_hash": "0x" + "00" * 32,
        "ok": True,
    }
    cases: list[tuple[str, dict[str, Any], str]] = [
        (
            "required",
            {"required_evidence_claims": (SURROGATE,)},
            "required_evidence_claims_not_canonically_encodable",
        ),
        (
            "claim_kind",
            {"evidence_claims": (surrogate_claim,)},
            "evidence_claims_not_canonically_encodable",
        ),
    ]

    for name, overrides, expected_error in cases:
        rotation = build_genesis_policy_pin_v1(
            policy=_policy(),
            registry={"payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0},
            signature_envelopes=[],
            current_epoch=20,
            proposal_epoch=10,
            min_delay_epochs=3,
            tau_policy_receipt=_tau_receipt(),
            backend_descriptors=[_backend()],
            production_mode=False,
            **overrides,
        )
        assert rotation["ok"] is False, name
        assert rotation["pin"] == {}, name
        assert expected_error in rotation["errors"], rotation["errors"]


def test_tampered_pin_is_refused_everywhere() -> None:
    pin_body = {
        "schema": AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1,
        "policy_id": "x",
        "policy_hash": ROOT_B,
        "registry_hash": ROOT_C,
        "previous_pin_hash": "",
        "rotation_index": 0,
        "approved_at_epoch": 20,
        "authority_receipt_hash": ROOT_B,
    }
    from src.integration.autonomous_governance_policy_pin import _pin_body_hash

    pin = {**pin_body, "pin_hash": _pin_body_hash(pin_body)}
    assert verify_policy_pin_v1(pin=pin)["ok"] is True

    tampered = dict(pin)
    tampered["policy_hash"] = ROOT_C
    assert verify_policy_pin_v1(pin=tampered)["ok"] is False
    assert "pin_hash_mismatch" in verify_policy_pin_v1(pin=tampered)["errors"]

    rotation = rotate_policy_pin_v1(
        current_pin=tampered,
        policy=_policy(),
        registry={"payload_kind": GOVERNANCE_ACTION_PAYLOAD_KIND_V0},
        signature_envelopes=[],
        current_epoch=40,
        proposal_epoch=30,
        min_delay_epochs=3,
        tau_policy_receipt=_tau_receipt(),
        backend_descriptors=[_backend()],
        production_mode=False,
    )
    assert rotation["ok"] is False
    assert "current_pin_hash_mismatch" in rotation["errors"]

    chain = verify_policy_pin_chain_v1([tampered])
    assert chain["ok"] is False


def test_pin_chain_rejects_bad_genesis_and_gaps() -> None:
    assert verify_policy_pin_chain_v1([])["ok"] is False
    assert verify_policy_pin_chain_v1("nope")["ok"] is False

    from src.integration.autonomous_governance_policy_pin import _pin_body_hash

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_POLICY_PIN_SCHEMA_V1,
        "policy_id": "x",
        "policy_hash": ROOT_B,
        "registry_hash": ROOT_C,
        "previous_pin_hash": "0x" + "11" * 32,  # genesis must anchor at ""
        "rotation_index": 0,
        "approved_at_epoch": 20,
        "authority_receipt_hash": ROOT_B,
    }
    non_anchored = {**body, "pin_hash": _pin_body_hash(body)}
    chain = verify_policy_pin_chain_v1([non_anchored])
    assert chain["ok"] is False
    assert any("chain_link_mismatch" in str(error) for error in chain["errors"])


def test_verify_pin_fail_closed_on_junk() -> None:
    assert verify_policy_pin_v1(pin=[])["ok"] is False
    assert verify_policy_pin_v1(pin={})["ok"] is False
    result = verify_policy_pin_v1(pin={"schema": "nope"})
    assert result["ok"] is False
