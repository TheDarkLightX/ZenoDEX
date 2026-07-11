"""Production key-management gates for ZenoLedger privileged operations."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.production_key_management_v0 import SignatureVerifierV0, validate_production_key_admission_v0


ZENO_LEDGER_PRODUCTION_KEY_GATES_V0 = {
    "public_network_config_update": "public_network_config_update",
    "validator_set_update": "validator_set_update",
    "oracle_reporter_registry_update": "oracle_reporter_registry_update",
    "verifier_registry_update": "verifier_registry_update",
    "release_artifact_publish": "release_artifact_publish",
    "emergency_pause": "emergency_pause",
    "emergency_unpause": "emergency_unpause",
}


def validate_zeno_ledger_production_key_gate_v0(
    *,
    operation: str,
    receipt: Mapping[str, Any] | None,
    packet: Mapping[str, Any] | None = None,
    key_descriptors: Sequence[Mapping[str, Any]] | None = None,
    signature_envelopes: Sequence[Mapping[str, Any]] | None = None,
    signature_verifier: SignatureVerifierV0 | None = None,
    expected_target_kind: str | None = None,
    expected_target_hash: str | None = None,
    expected_payload_hash: str | None = None,
) -> None:
    required_action = ZENO_LEDGER_PRODUCTION_KEY_GATES_V0.get(operation)
    if required_action is None:
        raise ValueError("ZenoLedger production key-management operation is not allowed")
    if receipt is None:
        raise ValueError(f"{operation} production key-management admission receipt is required")
    validate_production_key_admission_v0(
        receipt=receipt,
        required_action=required_action,
        packet=packet,
        key_descriptors=key_descriptors,
        signature_envelopes=signature_envelopes,
        signature_verifier=signature_verifier,
        expected_target_kind=expected_target_kind,
        expected_target_hash=expected_target_hash,
        expected_payload_hash=expected_payload_hash,
    )


def validate_public_network_config_update_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="public_network_config_update", receipt=receipt, **context)


def validate_validator_set_update_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="validator_set_update", receipt=receipt, **context)


def validate_oracle_reporter_registry_update_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="oracle_reporter_registry_update", receipt=receipt, **context)


def validate_verifier_registry_update_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="verifier_registry_update", receipt=receipt, **context)


def validate_release_artifact_publish_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="release_artifact_publish", receipt=receipt, **context)


def validate_emergency_pause_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="emergency_pause", receipt=receipt, **context)


def validate_emergency_unpause_gate_v0(receipt: Mapping[str, Any] | None, **context: Any) -> None:
    validate_zeno_ledger_production_key_gate_v0(operation="emergency_unpause", receipt=receipt, **context)
