from __future__ import annotations

import pytest

from src.integration.production_key_management_v0 import (
    DEFAULT_ACTION_POLICIES_V0,
    admission_receipt_content_hash_v0,
    build_admission_receipt_v0,
    build_key_descriptor_v0,
    build_privileged_action_packet_v0,
    build_signature_envelope_v0,
)
from src.integration.zeno_ledger_production_key_gates_v0 import (
    ZENO_LEDGER_PRODUCTION_KEY_GATES_V0,
    validate_emergency_pause_gate_v0,
    validate_emergency_unpause_gate_v0,
    validate_oracle_reporter_registry_update_gate_v0,
    validate_public_network_config_update_gate_v0,
    validate_release_artifact_publish_gate_v0,
    validate_validator_set_update_gate_v0,
    validate_verifier_registry_update_gate_v0,
    validate_zeno_ledger_production_key_gate_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0


def _admission(action: str) -> dict[str, object]:
    policy = DEFAULT_ACTION_POLICIES_V0[action]
    packet = build_privileged_action_packet_v0(
        environment="production",
        action=action,
        target_kind="zeno_ledger_privileged_operation",
        target_hash=hash_v0("zeno_ledger_pkm_gate_target", {"action": action}),
        policy_hash=str(policy["policy_hash"]),
        nonce=1,
        epoch=10,
        not_before_epoch=5,
        expires_at_epoch=20,
        payload_hash=hash_v0("zeno_ledger_pkm_gate_payload", {"action": action}),
    )
    keys = [
        build_key_descriptor_v0(
            key_id=f"{action}-key-{index}",
            public_key=f"{action}-pub-{index}",
            role=str(policy["role"]),
            environment="production",
            status="active",
            storage_class="hardware",
            custodian_id=f"{action}-custodian-{index}",
            valid_from_epoch=0,
            valid_until_epoch=100,
            break_glass=(policy["role"] == "emergency"),
        )
        for index in range(int(policy["threshold"]))
    ]
    envelopes = [
        build_signature_envelope_v0(
            key_id=str(key["key_id"]),
            public_key=str(key["public_key"]),
            packet_hash=str(packet["packet_hash"]),
            signature_scheme="external-verifier-v0",
            signature=f"fixture:{key['key_id']}:{packet['packet_hash']}",
        )
        for key in keys
    ]
    receipt = build_admission_receipt_v0(
        packet,
        policy,
        keys,
        envelopes,
        transparency_log_hash=hash_v0("zeno_ledger_pkm_gate_transparency", {"action": action}),
        signature_verifier=lambda p, d, e: e["signature"] == f"fixture:{d['key_id']}:{p['packet_hash']}",
    )
    return {"receipt": receipt, "packet": packet, "key_descriptors": keys, "signature_envelopes": envelopes}


def _gate_context(action: str) -> dict[str, object]:
    admission = _admission(action)
    return {
        **admission,
        "signature_verifier": lambda p, d, e: e["signature"] == f"fixture:{d['key_id']}:{p['packet_hash']}",
    }


@pytest.mark.parametrize("operation,action", sorted(ZENO_LEDGER_PRODUCTION_KEY_GATES_V0.items()))
def test_every_zeno_ledger_privileged_operation_has_gate(operation: str, action: str) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation=operation, **_gate_context(action))


def test_named_gate_helpers_accept_matching_receipts() -> None:
    validate_public_network_config_update_gate_v0(**_gate_context("public_network_config_update"))
    validate_validator_set_update_gate_v0(**_gate_context("validator_set_update"))
    validate_oracle_reporter_registry_update_gate_v0(**_gate_context("oracle_reporter_registry_update"))
    validate_verifier_registry_update_gate_v0(**_gate_context("verifier_registry_update"))
    validate_release_artifact_publish_gate_v0(**_gate_context("release_artifact_publish"))
    validate_emergency_pause_gate_v0(**_gate_context("emergency_pause"))
    validate_emergency_unpause_gate_v0(**_gate_context("emergency_unpause"))


def test_gate_rejects_missing_and_wrong_receipt() -> None:
    with pytest.raises(ValueError, match="receipt is required"):
        validate_zeno_ledger_production_key_gate_v0(operation="validator_set_update", receipt=None)

    with pytest.raises(ValueError, match="action mismatch"):
        validate_zeno_ledger_production_key_gate_v0(
            operation="validator_set_update",
            **_gate_context("public_network_config_update"),
        )

    with pytest.raises(ValueError, match="operation is not allowed"):
        validate_zeno_ledger_production_key_gate_v0(
            operation="unknown_operation",
            **_gate_context("public_network_config_update"),
        )


def test_gate_rejects_self_hashed_receipt_without_signed_packet_context() -> None:
    forged = dict(_gate_context("verifier_registry_update")["receipt"])

    with pytest.raises(TypeError, match="privileged_action_packet must be a JSON object"):
        validate_verifier_registry_update_gate_v0(forged)


def test_gate_rejects_receipt_not_bound_to_verified_signatures() -> None:
    context = _gate_context("verifier_registry_update")
    forged = dict(context["receipt"])
    forged["accepted_key_ids"] = ["attacker-key-0", "attacker-key-1"]
    forged["receipt_hash"] = admission_receipt_content_hash_v0(forged)

    with pytest.raises(ValueError, match="not bound to verified signatures"):
        validate_verifier_registry_update_gate_v0(forged, **{k: v for k, v in context.items() if k != "receipt"})
