"""Production social recovery for perps wallet with live BLS guardian quorum signing.

Implements live guardian key registration, recovery proposal submission, quorum
collection with BLS12-381 signature aggregation, recovery execution, key rotation
ceremony, and device approval flow. Guardian signatures are real BLS signatures
verified against registered public keys, not pre-computed fixtures.

Copyright (c) DarkLightX/Dana Edwards. All rights reserved.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Mapping

from src.integration.zeno_key_manager import (
    KEY_STATUS_ACTIVE,
    KEY_STATUS_REVOKED,
    RecoveryGuardian,
    SocialRecoveryPolicy,
    validate_tau_bls_public_key,
)
from src.integration.zeno_ledger_signature import (
    build_bls_signed_artifact_envelope_v0,
    validate_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import (
    build_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x, hex_to_bytes_fixed

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover
    G2Basic = None
    _BLS_AVAILABLE = False

# --- Schemas ----------------------------------------------------------------

GUARDIAN_REGISTRATION_SCHEMA_V1 = "zenodex/perps-wallet-guardian-registration/v1"
RECOVERY_PROPOSAL_SCHEMA_V1 = "zenodex/perps-wallet-recovery-proposal/v1"
KEY_ROTATION_PROPOSAL_SCHEMA_V1 = "zenodex/perps-wallet-key-rotation-proposal/v1"
DEVICE_APPROVAL_PROPOSAL_SCHEMA_V1 = "zenodex/perps-wallet-device-approval-proposal/v1"
RECOVERY_QUORUM_REPORT_SCHEMA_V1 = "zenodex/perps-wallet-recovery-quorum-report/v1"
RECOVERY_EXECUTION_SCHEMA_V1 = "zenodex/perps-wallet-recovery-execution/v1"
KEY_ROTATION_EXECUTION_SCHEMA_V1 = "zenodex/perps-wallet-key-rotation-execution/v1"
DEVICE_APPROVAL_EXECUTION_SCHEMA_V1 = "zenodex/perps-wallet-device-approval-execution/v1"
COORDINATOR_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-social-recovery-coordinator-status/v1"

# Payload kinds — must be in SUPPORTED_PAYLOAD_KINDS_V0
PAYLOAD_KIND_RECOVERY = "perps_wallet_recovery_exercise"
PAYLOAD_KIND_ROTATION = "perps_wallet_rotation_exercise"
PAYLOAD_KIND_DEVICE_APPROVAL = "governance_action"

PROPOSAL_STATUS_PENDING = "pending"
PROPOSAL_STATUS_QUORUM_MET = "quorum_met"
PROPOSAL_STATUS_EXECUTED = "executed"
PROPOSAL_STATUS_REJECTED = "rejected"


# --- Validation helpers -----------------------------------------------------

def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_nonneg_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_pos_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be bool")
    return value


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise RuntimeError("py_ecc.bls is required for live BLS guardian signing")


# --- BLS aggregation primitives ---------------------------------------------

def _envelope_message_digest(envelope: Mapping[str, Any]) -> bytes:
    """Reconstruct the BLS message digest from a signed artifact envelope body."""
    body = {k: v for k, v in dict(envelope).items() if k not in ("signature", "envelope_hash")}
    return hashlib.sha256(
        canonical_json_bytes_v0({"domain": "zenodex.zeno_ledger.signed_artifact.v0", "body": body})
    ).digest()


def aggregate_guardian_bls_signatures_v1(envelopes: list[Mapping[str, Any]]) -> str:
    """Aggregate individual guardian BLS signatures via G2Basic.Aggregate.

    Exploits the homomorphic property of BLS: the sum of individual G2 signatures
    is a valid G2 point verifiable via AggregateVerify against the corresponding
    public keys and per-signer messages.
    """
    _require_bls()
    if not envelopes:
        raise ValueError("at least one envelope is required")
    raw_sigs: list[bytes] = []
    for i, env in enumerate(envelopes):
        sig_hex = canonical_hex_fixed_allow_0x(
            _require_str(env.get("signature"), name=f"envelopes[{i}].signature"),
            nbytes=96, name=f"envelopes[{i}].signature",
        )
        raw_sigs.append(hex_to_bytes_fixed(sig_hex, nbytes=96, name="signature"))
    return "0x" + G2Basic.Aggregate(raw_sigs).hex()


def verify_aggregate_guardian_bls_signatures_v1(
    *, envelopes: list[Mapping[str, Any]], public_keys: list[str],
) -> bool:
    """Verify an aggregate BLS signature via G2Basic.AggregateVerify.

    Each guardian signs a distinct message (envelope body includes signer_id),
    so we use the multi-message AggregateVerify variant.
    """
    _require_bls()
    if len(envelopes) != len(public_keys):
        raise ValueError("envelopes and public_keys must have equal length")
    if not envelopes:
        raise ValueError("at least one envelope is required")
    msgs = [_envelope_message_digest(env) for env in envelopes]
    pks = [
        hex_to_bytes_fixed(
            canonical_hex_fixed_allow_0x(pk, nbytes=48, name="public_key"),
            nbytes=48, name="public_key",
        )
        for pk in public_keys
    ]
    agg_hex = aggregate_guardian_bls_signatures_v1(envelopes)
    return bool(G2Basic.AggregateVerify(pks, msgs, bytes.fromhex(agg_hex[2:])))


# --- Data structures --------------------------------------------------------

@dataclass(frozen=True)
class GuardianRegistrationV1:
    """A guardian who has registered a BLS public key for social recovery signing."""

    guardian_id: str
    public_key: str
    weight: int = 1
    status: str = KEY_STATUS_ACTIVE
    registered_at_epoch: int = 0

    def __post_init__(self) -> None:
        _require_str(self.guardian_id, name="guardian_id")
        validate_tau_bls_public_key(self.public_key, name="guardian_public_key")
        _require_pos_int(self.weight, name="guardian_weight")
        if self.status not in {KEY_STATUS_ACTIVE, KEY_STATUS_REVOKED}:
            raise ValueError("guardian status must be active or revoked")
        _require_nonneg_int(self.registered_at_epoch, name="registered_at_epoch")

    def public_dict(self) -> dict[str, Any]:
        body = {
            "schema": GUARDIAN_REGISTRATION_SCHEMA_V1,
            "guardian_id": self.guardian_id,
            "public_key": validate_tau_bls_public_key(self.public_key),
            "weight": self.weight, "status": self.status,
            "registered_at_epoch": self.registered_at_epoch,
        }
        return {**body, "registration_hash": hash_v0("perps_wallet_guardian_registration_v1", body)}


@dataclass
class RecoveryProposalV1:
    """A recovery/rotation/device-approval proposal awaiting guardian quorum."""

    proposal_id: str
    proposal_type: str
    body: dict[str, Any]
    proposal_hash: str
    policy_id: str
    status: str = PROPOSAL_STATUS_PENDING
    guardian_envelopes: list[dict[str, Any]] = field(default_factory=list)
    quorum_report: dict[str, Any] | None = None

    def public_dict(self) -> dict[str, Any]:
        return {
            **self.body, "proposal_hash": self.proposal_hash, "status": self.status,
            "guardian_envelopes": list(self.guardian_envelopes),
            "quorum_report": self.quorum_report,
        }


# --- Coordinator ------------------------------------------------------------

class SocialRecoveryCoordinatorV1:
    """Production social-recovery coordinator with live BLS guardian quorum signing.

    Manages guardian key registration, recovery/rotation/device-approval proposals,
    quorum collection with BLS12-381 signature aggregation, and ceremony execution.
    Sets production_security_claim=True when live guardian signing is used; falls
    back to fixture mode only when explicitly configured for local-testnet.
    """

    def __init__(self, *, chain_id: str, authority_id: str, fixture_mode: bool = False) -> None:
        self._chain_id = _require_str(chain_id, name="chain_id")
        self._authority_id = _require_str(authority_id, name="authority_id")
        self._fixture_mode = _require_bool(fixture_mode, name="fixture_mode")
        self._guardians: dict[str, GuardianRegistrationV1] = {}
        self._policies: dict[str, SocialRecoveryPolicy] = {}
        self._proposals: dict[str, RecoveryProposalV1] = {}

    @property
    def fixture_mode(self) -> bool:
        return self._fixture_mode

    @property
    def production_security_claim(self) -> bool:
        """True when live guardian signing is used (not fixture mode)."""
        return not self._fixture_mode

    def register_guardian(
        self, *, guardian_id: str, public_key: str,
        weight: int = 1, registered_at_epoch: int = 0,
    ) -> dict[str, Any]:
        """Register a guardian's BLS public key for social recovery signing."""
        reg = GuardianRegistrationV1(
            guardian_id=_require_str(guardian_id, name="guardian_id"),
            public_key=validate_tau_bls_public_key(public_key, name="public_key"),
            weight=_require_pos_int(weight, name="weight"),
            status=KEY_STATUS_ACTIVE,
            registered_at_epoch=_require_nonneg_int(registered_at_epoch, name="registered_at_epoch"),
        )
        self._guardians[guardian_id] = reg
        return reg.public_dict()

    def set_recovery_policy(
        self, *, policy_id: str, subject_key_id: str,
        threshold: int, delay_epochs: int = 0,
    ) -> dict[str, Any]:
        """Bind registered guardians to a subject key via a social recovery policy."""
        guardians = tuple(
            RecoveryGuardian(
                guardian_id=g.guardian_id, public_key=g.public_key,
                weight=g.weight, status=g.status,
            )
            for g in sorted(self._guardians.values(), key=lambda item: item.guardian_id)
        )
        policy = SocialRecoveryPolicy(
            policy_id=_require_str(policy_id, name="policy_id"),
            subject_key_id=_require_str(subject_key_id, name="subject_key_id"),
            threshold=_require_pos_int(threshold, name="threshold"),
            delay_epochs=_require_nonneg_int(delay_epochs, name="delay_epochs"),
            guardians=guardians,
        )
        self._policies[policy_id] = policy
        return policy.public_dict()

    def _submit_proposal(
        self, *, proposal_id: str, proposal_type: str, schema: str,
        hash_domain: str, body_fields: dict[str, Any], policy_id: str,
    ) -> dict[str, Any]:
        _require_str(proposal_id, name="proposal_id")
        _require_str(policy_id, name="policy_id")
        if policy_id not in self._policies:
            raise ValueError(f"recovery policy {policy_id} not found")
        policy = self._policies[policy_id]
        target_key = (
            body_fields.get("subject_key_id")
            or body_fields.get("rotated_key_id")
            or body_fields.get("key_id")
        )
        if target_key and target_key != policy.subject_key_id:
            raise ValueError(
                f"proposal target key {target_key} does not match policy subject_key_id {policy.subject_key_id}"
            )
        body: dict[str, Any] = {
            "schema": schema, "authority_id": self._authority_id,
            "chain_id": self._chain_id, "proposal_id": proposal_id,
            "proposal_type": proposal_type, "policy_id": policy_id, **body_fields,
        }
        proposal_hash = hash_v0(hash_domain, body)
        self._proposals[proposal_hash] = RecoveryProposalV1(
            proposal_id=proposal_id, proposal_type=proposal_type,
            body=body, proposal_hash=proposal_hash, policy_id=policy_id,
        )
        return {**body, "proposal_hash": proposal_hash}

    def submit_recovery_proposal(
        self, *, proposal_id: str, subject_key_id: str, replacement_key_id: str,
        replacement_public_key: str, requested_at_epoch: int, policy_id: str,
    ) -> dict[str, Any]:
        """Submit a key-recovery proposal for guardian quorum signing."""
        return self._submit_proposal(
            proposal_id=proposal_id, proposal_type="recovery",
            schema=RECOVERY_PROPOSAL_SCHEMA_V1,
            hash_domain="perps_wallet_recovery_proposal_v1",
            body_fields={
                "subject_key_id": _require_str(subject_key_id, name="subject_key_id"),
                "replacement_key_id": _require_str(replacement_key_id, name="replacement_key_id"),
                "replacement_public_key": validate_tau_bls_public_key(
                    replacement_public_key, name="replacement_public_key"),
                "requested_at_epoch": _require_nonneg_int(requested_at_epoch, name="requested_at_epoch"),
            },
            policy_id=policy_id,
        )

    def submit_rotation_proposal(
        self, *, proposal_id: str, rotated_key_id: str, replacement_key_id: str,
        replacement_public_key: str, requested_at_epoch: int,
        broadcast_at_epoch: int, policy_id: str,
    ) -> dict[str, Any]:
        """Submit a key-rotation proposal for guardian quorum signing."""
        return self._submit_proposal(
            proposal_id=proposal_id, proposal_type="rotation",
            schema=KEY_ROTATION_PROPOSAL_SCHEMA_V1,
            hash_domain="perps_wallet_key_rotation_proposal_v1",
            body_fields={
                "rotated_key_id": _require_str(rotated_key_id, name="rotated_key_id"),
                "replacement_key_id": _require_str(replacement_key_id, name="replacement_key_id"),
                "replacement_public_key": validate_tau_bls_public_key(
                    replacement_public_key, name="replacement_public_key"),
                "requested_at_epoch": _require_nonneg_int(requested_at_epoch, name="requested_at_epoch"),
                "broadcast_at_epoch": _require_nonneg_int(broadcast_at_epoch, name="broadcast_at_epoch"),
            },
            policy_id=policy_id,
        )

    def submit_device_approval_proposal(
        self, *, proposal_id: str, key_id: str,
        device_descriptor: Mapping[str, Any], requested_at_epoch: int, policy_id: str,
    ) -> dict[str, Any]:
        """Submit a device-approval proposal for guardian quorum signing."""
        return self._submit_proposal(
            proposal_id=proposal_id, proposal_type="device_approval",
            schema=DEVICE_APPROVAL_PROPOSAL_SCHEMA_V1,
            hash_domain="perps_wallet_device_approval_proposal_v1",
            body_fields={
                "key_id": _require_str(key_id, name="key_id"),
                "device_descriptor": dict(_require_mapping(device_descriptor, name="device_descriptor")),
                "requested_at_epoch": _require_nonneg_int(requested_at_epoch, name="requested_at_epoch"),
            },
            policy_id=policy_id,
        )

    def guardian_sign_proposal(
        self, *, guardian_id: str, guardian_private_key_hex: str,
        proposal: Mapping[str, Any], payload_kind: str = PAYLOAD_KIND_RECOVERY,
    ) -> dict[str, Any]:
        """A guardian signs a proposal hash with their BLS private key.

        Produces a signed_artifact_envelope that is immediately verified against
        the guardian's registered public key to ensure key match.
        """
        _require_bls()
        _require_str(guardian_id, name="guardian_id")
        guardian = self._guardians.get(guardian_id)
        if guardian is None:
            raise ValueError(f"guardian {guardian_id} not registered")
        if guardian.status != KEY_STATUS_ACTIVE:
            raise ValueError(f"guardian {guardian_id} is not active")
        proposal_hash = _require_str(
            proposal.get("proposal_hash") if isinstance(proposal, Mapping) else None,
            name="proposal_hash",
        )
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind=payload_kind, payload_hash=proposal_hash,
            signer_id=guardian_id, key_id=guardian_id,
            private_key_hex=guardian_private_key_hex,
        )
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope, expected_payload_kind=payload_kind,
            expected_payload_hash=proposal_hash, expected_public_key=guardian.public_key,
        )
        return envelope

    def verify_quorum(
        self, *, proposal: Mapping[str, Any], envelopes: list[Mapping[str, Any]],
        payload_kind: str = PAYLOAD_KIND_RECOVERY,
    ) -> dict[str, Any]:
        """Verify guardian quorum: individual BLS checks + threshold + aggregate proof.

        Each envelope is individually verified via verify_signature_quorum_v0.
        Accepted signatures are then aggregated and verified via AggregateVerify
        to produce a compact cryptographic proof that the full quorum signed.
        """
        proposal_hash = _require_str(
            proposal.get("proposal_hash") if isinstance(proposal, Mapping) else None,
            name="proposal_hash",
        )
        policy_id = _require_str(
            proposal.get("policy_id") if isinstance(proposal, Mapping) else None,
            name="policy_id",
        )
        policy = self._policies.get(policy_id)
        if policy is None:
            raise ValueError(f"recovery policy {policy_id} not found")
        registry = build_signer_registry_v0(
            registry_id=f"{policy.policy_id}:guardian-signers",
            payload_kind=payload_kind, threshold=int(policy.threshold),
            signers=tuple(
                {"signer_id": g.guardian_id, "key_id": g.guardian_id,
                 "public_key": g.public_key, "weight": int(g.weight), "status": g.status}
                for g in sorted(policy.guardians, key=lambda item: item.guardian_id)
            ),
        )
        quorum_met = False
        accepted_weight = 0
        accepted_sigs: list[dict[str, Any]] = []
        aggregate_signature: str | None = None
        aggregate_verified = False
        errors: list[str] = []
        try:
            report = verify_signature_quorum_v0(
                registry=registry, payload_kind=payload_kind,
                payload_hash=proposal_hash, envelopes=envelopes,
            )
            quorum_met = True
            accepted_weight = int(report["accepted_weight"])
            accepted_sigs = [
                {"guardian_id": str(item["signer_id"]), "key_id": str(item["key_id"]),
                 "weight": int(item["weight"]), "envelope_hash": item["envelope_hash"]}
                for item in report["accepted_signatures"]
            ]
        except ValueError as exc:
            errors.append(str(exc))
        except Exception as exc:  # pragma: no cover
            errors.append(f"quorum verification failed: {exc}")

        if quorum_met and accepted_sigs:
            sig_by_guardian = {
                str(env.get("signer_id")): env for env in envelopes if isinstance(env, Mapping)
            }
            sorted_envs: list[Mapping[str, Any]] = []
            sorted_pks: list[str] = []
            for sig in sorted(accepted_sigs, key=lambda x: x["guardian_id"]):
                gid = sig["guardian_id"]
                env = sig_by_guardian.get(gid)
                if env is not None and gid in self._guardians:
                    sorted_envs.append(env)
                    sorted_pks.append(self._guardians[gid].public_key)
            if sorted_envs:
                try:
                    aggregate_signature = aggregate_guardian_bls_signatures_v1(sorted_envs)
                    aggregate_verified = verify_aggregate_guardian_bls_signatures_v1(
                        envelopes=sorted_envs, public_keys=sorted_pks,
                    )
                    if not aggregate_verified:
                        errors.append("BLS aggregate signature verification failed")
                except Exception as exc:
                    errors.append(f"BLS aggregate verification failed: {exc}")

        body = {
            "schema": RECOVERY_QUORUM_REPORT_SCHEMA_V1,
            "proposal_hash": proposal_hash, "payload_kind": payload_kind,
            "threshold": int(policy.threshold), "accepted_weight": accepted_weight,
            "accepted_signatures": accepted_sigs, "quorum_met": bool(quorum_met),
            "aggregate_signature": aggregate_signature,
            "aggregate_verified": bool(aggregate_verified),
            "production_security_claim": self.production_security_claim,
            "fixture_mode": self._fixture_mode, "errors": errors,
        }
        return {**body, "quorum_report_hash": hash_v0("perps_wallet_recovery_quorum_report_v1", body)}

    def _execute(
        self, *, proposal: Mapping[str, Any], envelopes: list[Mapping[str, Any]],
        current_epoch: int, payload_kind: str,
        execution_schema: str, execution_hash_domain: str,
    ) -> dict[str, Any]:
        proposal_hash = _require_str(
            proposal.get("proposal_hash") if isinstance(proposal, Mapping) else None,
            name="proposal_hash",
        )
        _require_nonneg_int(current_epoch, name="current_epoch")
        quorum_report = self.verify_quorum(
            proposal=proposal, envelopes=envelopes, payload_kind=payload_kind,
        )
        executed = False
        errors: list[str] = list(quorum_report.get("errors", []))
        if not quorum_report.get("quorum_met"):
            errors.append("quorum threshold not met")
        policy = self._policies.get(
            proposal.get("policy_id", "") if isinstance(proposal, Mapping) else ""
        )
        if policy is not None:
            stored_proposal = self._proposals.get(proposal_hash)
            if stored_proposal is not None:
                requested_at = stored_proposal.body.get("requested_at_epoch", 0)
            else:
                errors.append("proposal not found in stored proposals — cannot verify delay")
                requested_at = None
            if isinstance(requested_at, int) and current_epoch < requested_at + policy.delay_epochs:
                errors.append("recovery delay period not elapsed")
        if not errors:
            executed = True
            stored = self._proposals.get(proposal_hash)
            if stored is not None:
                stored.status = PROPOSAL_STATUS_EXECUTED
                stored.quorum_report = quorum_report
                stored.guardian_envelopes = [dict(e) for e in envelopes]
        body = {
            "schema": execution_schema, "proposal_hash": proposal_hash,
            "executed": bool(executed), "current_epoch": current_epoch,
            "quorum_report": quorum_report,
            "production_security_claim": self.production_security_claim, "errors": errors,
        }
        return {**body, "execution_hash": hash_v0(execution_hash_domain, body)}

    def execute_recovery(
        self, *, proposal: Mapping[str, Any], envelopes: list[Mapping[str, Any]],
        current_epoch: int,
    ) -> dict[str, Any]:
        """Execute key recovery when guardian quorum threshold is met and delay elapsed."""
        return self._execute(
            proposal=proposal, envelopes=envelopes, current_epoch=current_epoch,
            payload_kind=PAYLOAD_KIND_RECOVERY,
            execution_schema=RECOVERY_EXECUTION_SCHEMA_V1,
            execution_hash_domain="perps_wallet_recovery_execution_v1",
        )

    def execute_rotation(
        self, *, proposal: Mapping[str, Any], envelopes: list[Mapping[str, Any]],
        current_epoch: int,
    ) -> dict[str, Any]:
        """Execute key rotation when guardian quorum threshold is met."""
        return self._execute(
            proposal=proposal, envelopes=envelopes, current_epoch=current_epoch,
            payload_kind=PAYLOAD_KIND_ROTATION,
            execution_schema=KEY_ROTATION_EXECUTION_SCHEMA_V1,
            execution_hash_domain="perps_wallet_key_rotation_execution_v1",
        )

    def execute_device_approval(
        self, *, proposal: Mapping[str, Any], envelopes: list[Mapping[str, Any]],
        current_epoch: int,
    ) -> dict[str, Any]:
        """Execute device approval when guardian quorum threshold is met."""
        return self._execute(
            proposal=proposal, envelopes=envelopes, current_epoch=current_epoch,
            payload_kind=PAYLOAD_KIND_DEVICE_APPROVAL,
            execution_schema=DEVICE_APPROVAL_EXECUTION_SCHEMA_V1,
            execution_hash_domain="perps_wallet_device_approval_execution_v1",
        )

    def coordinator_status(self) -> dict[str, Any]:
        """Return the coordinator's current status with guardian and proposal summaries."""
        body = {
            "schema": COORDINATOR_STATUS_SCHEMA_V1,
            "chain_id": self._chain_id, "authority_id": self._authority_id,
            "fixture_mode": self._fixture_mode,
            "production_security_claim": self.production_security_claim,
            "guardian_count": len(self._guardians),
            "active_guardian_count": sum(
                1 for g in self._guardians.values() if g.status == KEY_STATUS_ACTIVE),
            "policy_count": len(self._policies),
            "proposal_count": len(self._proposals),
            "pending_proposal_count": sum(
                1 for p in self._proposals.values() if p.status == PROPOSAL_STATUS_PENDING),
            "executed_proposal_count": sum(
                1 for p in self._proposals.values() if p.status == PROPOSAL_STATUS_EXECUTED),
            "guardians": [g.public_dict() for g in sorted(self._guardians.values(), key=lambda x: x.guardian_id)],
            "policies": [p.public_dict() for p in sorted(self._policies.values(), key=lambda x: x.policy_id)],
        }
        return {**body, "status_hash": hash_v0("perps_wallet_social_recovery_coordinator_status_v1", body)}
