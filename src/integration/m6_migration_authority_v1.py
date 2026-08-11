"""Research-only verifier port for M6-R11 migration evidence.

The core witness remains pure and opaque.  This port owns the external receipt
boundary, including the optional local BLS quorum check used by the durable
research shell.  A durable store must use the authenticated mode and persist
the complete receipt so a fresh process can re-verify it before replaying
history.  Writer shutdown, economic publication, and production authority
remain outside this module.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Mapping, Protocol

from ..core.m6_migration_lifecycle_v1 import (
    _M6_MIGRATION_REPLAY_TOKEN,
    _M6_MIGRATION_VERIFIED_TOKEN,
    M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
    M6_MIGRATION_MAX_WRITER_EPOCH_V1,
    M6_MIGRATION_RECEIPT_DOMAIN_V1,
    M6MigrationPhaseV1,
    M6MigrationPlanV1,
    M6MigrationStateV1,
    M6MigrationStepV1,
    M6MigrationStructuralReplayV1,
    VerifiedM6MigrationStepV1,
)
from ..core.m6_safe_mount_types_v1 import _require_root, canonical_bytes_v1, hash_v1
from .zeno_ledger_signature import M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1
from .zeno_ledger_signer_registry import (
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)

M6_MIGRATION_AUTHORITY_REQUEST_SCHEMA_V1 = (
    "zenodex/m6/migration-authority-verification-request/v1"
)
M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1 = "zenodex/m6/migration-authority-proof/v1"
M6_MIGRATION_AUTHORITY_PAYLOAD_DOMAIN_V1 = "m6-migration-authority-payload-v1"
M6_MIGRATION_WRITER_MEMBERSHIP_REQUEST_SCHEMA_V1 = (
    "zenodex/m6/migration-writer-membership-verification-request/v1"
)
M6_MIGRATION_WRITER_MEMBERSHIP_RECEIPT_SCHEMA_V1 = (
    "zenodex/m6/migration-writer-membership-verification-receipt/v1"
)
M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_DOMAIN_V1 = "m6-migration-writer-membership-proof-v1"
M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1 = 1 << 20
M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_DEPTH_V1 = 64
M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_NODES_V1 = 65536
M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1 = 32768


class M6MigrationAuthorityVerificationError(ValueError):
    """Base error for a migration evidence verification refusal."""


class M6MigrationAuthorityVerifierUnavailableV1(
    M6MigrationAuthorityVerificationError
):
    """No external verifier is configured."""


class M6MigrationAuthorityProofRejectedV1(
    M6MigrationAuthorityVerificationError
):
    """The external verifier did not return the exact expected receipt."""


class M6MigrationAuthorityBackendV1(Protocol):
    def verify_m6_migration_step(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]: ...


class M6MigrationWriterMembershipBackendV1(Protocol):
    def verify_m6_migration_writer_membership(
        self,
        request: Mapping[str, object],
    ) -> Mapping[str, object]: ...


def expected_m6_migration_receipt_body_v1(
    step: M6MigrationStepV1,
    plan: M6MigrationPlanV1,
    branch_root: str,
    *,
    pre_state_root: str,
    pre_phase: M6MigrationPhaseV1,
) -> dict[str, object]:
    """Return the receipt body bound to the exact transition context."""

    _require_root(branch_root, name="migration verification branch root")
    _require_root(pre_state_root, name="migration verification pre-state root")
    if not isinstance(pre_phase, M6MigrationPhaseV1):
        raise TypeError("migration verification pre-phase is not closed")
    return {
        "schema": M6_MIGRATION_LIFECYCLE_SCHEMA_V1,
        "ok": True,
        "plan_root": plan.plan_root,
        "step_root": step.step_root,
        "source_subject_root": step.source_subject_root,
        "target_subject_root": step.target_subject_root,
        "source_state_root": step.source_state_root,
        "target_state_root": step.target_state_root,
        "source_writer_epoch": step.source_writer_epoch,
        "target_writer_epoch": step.target_writer_epoch,
        "allowed_writer_set_root": step.allowed_writer_set_root,
        "authority_registry_root": plan.authority_registry_root,
        "rollback_state_root": step.rollback_state_root,
        "evidence_root": step.evidence_root,
        "kind": step.kind.value,
        "branch_root": branch_root,
        "pre_state_root": pre_state_root,
        "pre_phase": pre_phase.value,
    }


def migration_authority_payload_hash_v1(body: Mapping[str, object]) -> str:
    """Hash the exact public receipt body signed by the authority quorum."""

    return hash_v1(M6_MIGRATION_AUTHORITY_PAYLOAD_DOMAIN_V1, dict(body))


def _normalize_membership_proof_value(
    value: object,
    *,
    path: str,
    active_containers: set[int] | None = None,
    depth: int = 0,
    counters: list[int] | None = None,
) -> object:
    """Copy a JSON-shaped proof while rejecting ambiguous mapping keys."""

    if value is None or type(value) in (bool, int, str):
        return value
    if depth > M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_DEPTH_V1:
        raise ValueError("migration writer membership proof exceeds the nesting limit")
    counts = counters if counters is not None else [0, 0]
    counts[0] += 1
    if counts[0] > M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_NODES_V1:
        raise ValueError("migration writer membership proof exceeds the node limit")
    active = active_containers if active_containers is not None else set()
    container_id = id(value)
    if container_id in active:
        raise ValueError("migration writer membership proof contains a cycle")
    active.add(container_id)
    try:
        if isinstance(value, Mapping):
            pairs = list(value.items())
            counts[1] += len(pairs)
            if counts[1] > M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1:
                raise ValueError("migration writer membership proof exceeds the item limit")
            normalized: dict[str, object] = {}
            for key, item in pairs:
                if type(key) is not str:
                    raise TypeError(f"{path} mapping keys must be strings")
                if key in normalized:
                    raise ValueError(f"{path} contains duplicate mapping keys")
                normalized[key] = _normalize_membership_proof_value(
                    item,
                    path=f"{path}.{key}",
                    active_containers=active,
                    depth=depth + 1,
                    counters=counts,
                )
            return normalized
        if isinstance(value, (list, tuple)):
            counts[1] += len(value)
            if counts[1] > M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1:
                raise ValueError("migration writer membership proof exceeds the item limit")
            return [
                _normalize_membership_proof_value(
                    item,
                    path=f"{path}[{index}]",
                    active_containers=active,
                    depth=depth + 1,
                    counters=counts,
                )
                for index, item in enumerate(value)
            ]
        raise TypeError(f"{path} contains a value outside the JSON proof subset")
    finally:
        active.remove(container_id)


@dataclass(frozen=True, slots=True)
class M6MigrationWriterMembershipProofV1:
    """One immutable snapshot of an untrusted writer-membership proof."""

    canonical_json: bytes

    def __post_init__(self) -> None:
        if type(self.canonical_json) is not bytes or not self.canonical_json:
            raise TypeError("migration writer membership proof bytes are invalid")
        if len(self.canonical_json) > M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1:
            raise ValueError("migration writer membership proof exceeds the size limit")
        try:
            raw = json.loads(self.canonical_json.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError("migration writer membership proof is not canonical JSON") from exc
        if not isinstance(raw, dict) or not raw:
            raise ValueError("migration writer membership proof must be a non-empty object")
        normalized = _normalize_membership_proof_value(raw, path="proof")
        if canonical_bytes_v1(normalized) != self.canonical_json:
            raise ValueError("migration writer membership proof is not canonical")

    @classmethod
    def from_mapping(cls, value: object) -> "M6MigrationWriterMembershipProofV1":
        if not isinstance(value, Mapping) or not value:
            raise TypeError("migration writer membership proof must be a non-empty object")
        normalized = _normalize_membership_proof_value(value, path="proof")
        if not isinstance(normalized, dict):
            raise TypeError("migration writer membership proof must be an object")
        return cls(canonical_bytes_v1(normalized))

    @classmethod
    def from_value(cls, value: object) -> "M6MigrationWriterMembershipProofV1":
        if isinstance(value, cls):
            return value
        return cls.from_mapping(value)

    def to_mapping(self) -> dict[str, object]:
        raw = json.loads(self.canonical_json.decode("utf-8"))
        if not isinstance(raw, dict):
            raise ValueError("migration writer membership proof is not an object")
        return raw

    @property
    def proof_root(self) -> str:
        return hash_v1(
            M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_DOMAIN_V1,
            self.to_mapping(),
        )


def expected_m6_migration_writer_membership_receipt_body_v1(
    state: M6MigrationStateV1,
    *,
    writer_subject_root: str,
    writer_epoch: int,
    membership_proof: M6MigrationWriterMembershipProofV1 | Mapping[str, object],
) -> dict[str, object]:
    """Bind writer membership to the exact active migration snapshot.

    The external backend owns the membership-proof algorithm.  This local
    contract requires its receipt to bind the proof hash, plan, branch, state,
    phase, writer epoch, and allowed-writer-set root before a writer can be
    marked allowed.
    """

    if not isinstance(state, M6MigrationStateV1):
        raise TypeError("migration writer membership state is invalid")
    _require_root(writer_subject_root, name="migration writer subject root")
    if (
        type(writer_epoch) is not int
        or writer_epoch < 0
        or writer_epoch > M6_MIGRATION_MAX_WRITER_EPOCH_V1
    ):
        raise ValueError("migration writer membership epoch must be a u64")
    proof = M6MigrationWriterMembershipProofV1.from_value(membership_proof)
    return {
        "schema": M6_MIGRATION_WRITER_MEMBERSHIP_RECEIPT_SCHEMA_V1,
        "ok": True,
        "plan_root": state.plan.plan_root,
        "authority_registry_root": state.plan.authority_registry_root,
        "allowed_writer_set_root": state.plan.allowed_writer_set_root,
        "writer_subject_root": writer_subject_root,
        "writer_epoch": writer_epoch,
        "state_root": state.state_root,
        "phase": state.phase.value,
        "branch_root": state.branch_root,
        "membership_proof_root": proof.proof_root,
    }


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("migration authority receipt contains duplicate keys")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> object:
    raise ValueError(f"migration authority receipt contains forbidden JSON constant: {value}")


def _decode_canonical_receipt_json(data: str) -> dict[str, object]:
    if not isinstance(data, str) or not data:
        raise ValueError("migration authority receipt JSON must be non-empty")
    try:
        raw = json.loads(
            data,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
            parse_float=lambda _value: (_ for _ in ()).throw(
                ValueError("floats are forbidden in migration authority receipts")
            ),
        )
    except (TypeError, ValueError, json.JSONDecodeError) as exc:
        raise ValueError(f"invalid migration authority receipt JSON: {exc}") from exc
    if not isinstance(raw, dict) or canonical_bytes_v1(raw).decode("utf-8") != data:
        raise ValueError("migration authority receipt JSON is not canonical")
    return raw


def _require_canonical_envelope_order(envelopes: object) -> None:
    """Require the wire order used to bind a quorum report to one receipt."""

    if not isinstance(envelopes, list):
        raise M6MigrationAuthorityProofRejectedV1(
            "migration authority envelopes must be a canonical JSON list"
        )
    identities: list[tuple[str, str]] = []
    for index, raw_envelope in enumerate(envelopes):
        if not isinstance(raw_envelope, Mapping):
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration authority envelope {index} is not an object"
            )
        signer_id = raw_envelope.get("signer_id")
        key_id = raw_envelope.get("key_id")
        if not isinstance(signer_id, str) or not signer_id:
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration authority envelope {index} signer_id is invalid"
            )
        if not isinstance(key_id, str) or not key_id:
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration authority envelope {index} key_id is invalid"
            )
        identities.append((signer_id, key_id))
    if identities != sorted(identities):
        raise M6MigrationAuthorityProofRejectedV1(
            "migration authority envelope order is not canonical"
        )


@dataclass(frozen=True, slots=True)
class M6MigrationAuthorityReceiptV1:
    """Immutable retained wire evidence for one verifier decision.

    The receipt is data, not authority.  The verifier reconstructs authority
    only after checking its binding and, in authenticated mode, its signatures.
    """

    receipt_root: str
    canonical_json: str

    def __post_init__(self) -> None:
        _require_root(self.receipt_root, name="migration authority receipt root")
        raw = _decode_canonical_receipt_json(self.canonical_json)
        raw_root = raw.get("receipt_hash")
        if raw_root != self.receipt_root:
            raise ValueError("migration authority receipt root does not match its wire evidence")

    @classmethod
    def from_mapping(cls, value: Mapping[str, object]) -> "M6MigrationAuthorityReceiptV1":
        if not isinstance(value, Mapping):
            raise TypeError("migration authority receipt must be an object")
        raw = dict(value)
        receipt_root = raw.get("receipt_hash")
        if not isinstance(receipt_root, str):
            raise ValueError("migration authority receipt_hash is required")
        return cls(
            receipt_root=receipt_root,
            canonical_json=canonical_bytes_v1(raw).decode("utf-8"),
        )

    @classmethod
    def from_canonical(cls, value: object) -> "M6MigrationAuthorityReceiptV1":
        if not isinstance(value, Mapping):
            raise TypeError("migration authority receipt record must be an object")
        if set(value) != {"receipt_root", "canonical_json"}:
            raise ValueError("migration authority receipt record fields are not closed")
        return cls(
            receipt_root=value["receipt_root"],
            canonical_json=value["canonical_json"],
        )

    def to_mapping(self) -> dict[str, object]:
        return _decode_canonical_receipt_json(self.canonical_json)

    def to_canonical(self) -> dict[str, object]:
        return {
            "receipt_root": self.receipt_root,
            "canonical_json": self.canonical_json,
        }


@dataclass(frozen=True, slots=True)
class M6MigrationVerifiedAdmissionV1:
    """Exact pairing of an opaque step witness and its retained receipt."""

    verified_step: VerifiedM6MigrationStepV1
    receipt: M6MigrationAuthorityReceiptV1

    def __post_init__(self) -> None:
        if not isinstance(self.verified_step, VerifiedM6MigrationStepV1):
            raise TypeError("migration verified admission step is invalid")
        if not isinstance(self.receipt, M6MigrationAuthorityReceiptV1):
            raise TypeError("migration verified admission receipt is invalid")
        if self.verified_step.receipt_root != self.receipt.receipt_root:
            raise ValueError("migration verified admission receipt is not step-bound")

    def to_canonical(self) -> dict[str, object]:
        return {
            "verified_step": self.verified_step,
            "receipt": self.receipt,
        }


def _validated_receipt_root(
    receipt: Mapping[str, object],
    expected_body: Mapping[str, object],
    signer_registry: Mapping[str, object] | None,
) -> str:
    actual = dict(receipt)
    if signer_registry is None:
        receipt_body = dict(expected_body)
    else:
        proof = actual.get("authority_proof")
        if not isinstance(proof, Mapping):
            raise M6MigrationAuthorityProofRejectedV1(
                "authenticated migration receipt is missing authority proof"
            )
        expected_proof_keys = {
            "schema",
            "payload_kind",
            "payload_hash",
            "registry_hash",
            "envelopes",
            "quorum_report",
        }
        if set(proof) != expected_proof_keys:
            raise M6MigrationAuthorityProofRejectedV1(
                "authenticated migration receipt proof fields are not closed"
            )
        expected_payload_hash = migration_authority_payload_hash_v1(expected_body)
        if proof["schema"] != M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1:
            raise M6MigrationAuthorityProofRejectedV1("migration authority proof schema mismatch")
        if proof["payload_kind"] != M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1:
            raise M6MigrationAuthorityProofRejectedV1("migration authority proof payload kind mismatch")
        if proof["payload_hash"] != expected_payload_hash:
            raise M6MigrationAuthorityProofRejectedV1("migration authority proof payload binding mismatch")
        expected_registry_root = expected_body.get("authority_registry_root")
        if proof["registry_hash"] != expected_registry_root:
            raise M6MigrationAuthorityProofRejectedV1(
                "migration authority proof is bound to a different plan registry"
            )
        if proof["registry_hash"] != signer_registry.get("registry_hash"):
            raise M6MigrationAuthorityProofRejectedV1("migration authority signer registry mismatch")
        _require_canonical_envelope_order(proof["envelopes"])
        try:
            quorum_report = verify_signature_quorum_v0(
                registry=signer_registry,
                payload_kind=M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1,
                payload_hash=expected_payload_hash,
                envelopes=proof["envelopes"],
            )
        except (TypeError, ValueError, RuntimeError) as exc:
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration authority signature quorum rejected: {exc}"
            ) from exc
        if proof["quorum_report"] != quorum_report:
            raise M6MigrationAuthorityProofRejectedV1(
                "migration authority quorum report binding mismatch"
            )
        receipt_body = {**dict(expected_body), "authority_proof": dict(proof)}
    receipt_hash = hash_v1(M6_MIGRATION_RECEIPT_DOMAIN_V1, receipt_body)
    if actual != {**receipt_body, "receipt_hash": receipt_hash}:
        raise M6MigrationAuthorityProofRejectedV1(
            "migration authority receipt binding mismatch"
        )
    return receipt_hash


@dataclass(frozen=True, slots=True)
class M6MigrationAuthorityVerifierV1:
    backend: M6MigrationAuthorityBackendV1 | None
    signer_registry: Mapping[str, object] | None = None

    @property
    def authenticated(self) -> bool:
        """Whether this verifier performs the local signature-quorum check."""

        return self.signer_registry is not None

    def validate_plan_binding(self, plan: M6MigrationPlanV1) -> None:
        """Require an authenticated verifier registry committed by the plan."""

        if not isinstance(plan, M6MigrationPlanV1):
            raise TypeError("migration verification plan is invalid")
        if self.signer_registry is None:
            raise M6MigrationAuthorityVerifierUnavailableV1(
                "authenticated migration verifier registry is not configured"
            )
        try:
            validate_signer_registry_v0(self.signer_registry)
        except (TypeError, ValueError) as exc:
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration authority signer registry is invalid: {exc}"
            ) from exc
        if self.signer_registry.get("registry_hash") != plan.authority_registry_root:
            raise M6MigrationAuthorityProofRejectedV1(
                "migration authority signer registry is not bound to the migration plan"
            )

    def _request(
        self,
        plan: M6MigrationPlanV1,
        step: M6MigrationStepV1,
        branch_root: str,
        *,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> dict[str, object]:
        expected = expected_m6_migration_receipt_body_v1(
            step,
            plan,
            branch_root,
            pre_state_root=pre_state_root,
            pre_phase=pre_phase,
        )
        return {
            "schema": M6_MIGRATION_AUTHORITY_REQUEST_SCHEMA_V1,
            "receipt_schema": expected["schema"],
            **{key: value for key, value in expected.items() if key != "schema"},
            "proof": step.to_canonical(),
        }

    def _fetch_receipt(
        self,
        plan: M6MigrationPlanV1,
        step: M6MigrationStepV1,
        branch_root: str,
        *,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> M6MigrationAuthorityReceiptV1:
        if self.backend is None:
            raise M6MigrationAuthorityVerifierUnavailableV1(
                "M6 migration authority backend is not configured"
            )
        expected = expected_m6_migration_receipt_body_v1(
            step,
            plan,
            branch_root,
            pre_state_root=pre_state_root,
            pre_phase=pre_phase,
        )
        request = self._request(
            plan,
            step,
            branch_root,
            pre_state_root=pre_state_root,
            pre_phase=pre_phase,
        )
        try:
            receipt = self.backend.verify_m6_migration_step(request)
        except M6MigrationAuthorityVerificationError:
            raise
        except Exception as exc:
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration authority backend failed: {exc}"
            ) from exc
        if not isinstance(receipt, Mapping):
            raise M6MigrationAuthorityProofRejectedV1(
                "migration authority backend returned a non-object receipt"
            )
        _validated_receipt_root(receipt, expected, self.signer_registry)
        return M6MigrationAuthorityReceiptV1.from_mapping(receipt)

    def verify_step(
        self,
        plan: M6MigrationPlanV1,
        step: M6MigrationStepV1,
        branch_root: str,
        *,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> VerifiedM6MigrationStepV1 | M6MigrationStructuralReplayV1:
        if not isinstance(plan, M6MigrationPlanV1):
            raise TypeError("migration verification plan is invalid")
        if not isinstance(step, M6MigrationStepV1):
            raise TypeError("migration verification step is invalid")
        if not isinstance(branch_root, str):
            raise TypeError("migration verification branch root is invalid")
        receipt = self._fetch_receipt(
            plan,
            step,
            branch_root,
            pre_state_root=pre_state_root,
            pre_phase=pre_phase,
        )
        if not self.authenticated:
            return M6MigrationStructuralReplayV1(
                _M6_MIGRATION_REPLAY_TOKEN,
                step,
                receipt.receipt_root,
                branch_root,
                pre_state_root,
                pre_phase,
            )
        return VerifiedM6MigrationStepV1(
            _M6_MIGRATION_VERIFIED_TOKEN,
            step,
            receipt.receipt_root,
            branch_root,
            pre_state_root,
            pre_phase,
        )

    def verify_step_with_receipt(
        self,
        plan: M6MigrationPlanV1,
        step: M6MigrationStepV1,
        branch_root: str,
        *,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> M6MigrationVerifiedAdmissionV1:
        if not self.authenticated:
            raise M6MigrationAuthorityVerifierUnavailableV1(
                "migration admission requires an authenticated migration verifier"
            )
        receipt = self._fetch_receipt(
            plan,
            step,
            branch_root,
            pre_state_root=pre_state_root,
            pre_phase=pre_phase,
        )
        verified = VerifiedM6MigrationStepV1(
            _M6_MIGRATION_VERIFIED_TOKEN,
            step,
            receipt.receipt_root,
            branch_root,
            pre_state_root,
            pre_phase,
        )
        return M6MigrationVerifiedAdmissionV1(verified_step=verified, receipt=receipt)

    def reverify_step(
        self,
        plan: M6MigrationPlanV1,
        step: M6MigrationStepV1,
        branch_root: str,
        receipt: M6MigrationAuthorityReceiptV1,
        *,
        pre_state_root: str,
        pre_phase: M6MigrationPhaseV1,
    ) -> VerifiedM6MigrationStepV1:
        if not self.authenticated:
            raise M6MigrationAuthorityVerifierUnavailableV1(
                "migration durable history requires an authenticated migration verifier"
            )
        if not isinstance(receipt, M6MigrationAuthorityReceiptV1):
            raise M6MigrationAuthorityProofRejectedV1(
                "migration durable history receipt is not typed"
            )
        expected = expected_m6_migration_receipt_body_v1(
            step,
            plan,
            branch_root,
            pre_state_root=pre_state_root,
            pre_phase=pre_phase,
        )
        receipt_root = _validated_receipt_root(
            receipt.to_mapping(),
            expected,
            self.signer_registry,
        )
        if receipt_root != receipt.receipt_root:
            raise M6MigrationAuthorityProofRejectedV1(
                "migration durable receipt root changed during re-verification"
            )
        return VerifiedM6MigrationStepV1(
            _M6_MIGRATION_VERIFIED_TOKEN,
            step,
            receipt.receipt_root,
            branch_root,
            pre_state_root,
            pre_phase,
        )


@dataclass(frozen=True, slots=True)
class M6MigrationWriterMembershipVerifierV1:
    """Authenticated port for writer-set membership evidence."""

    backend: M6MigrationWriterMembershipBackendV1 | None
    signer_registry: Mapping[str, object] | None = None

    @property
    def authenticated(self) -> bool:
        return self.signer_registry is not None

    def verify_writer_membership(
        self,
        state: M6MigrationStateV1,
        *,
        writer_subject_root: str,
        writer_epoch: int,
        membership_proof: M6MigrationWriterMembershipProofV1 | Mapping[str, object],
    ) -> M6MigrationAuthorityReceiptV1:
        if not self.authenticated:
            raise M6MigrationAuthorityVerifierUnavailableV1(
                "authenticated writer membership verifier is not configured"
            )
        if self.backend is None:
            raise M6MigrationAuthorityVerifierUnavailableV1(
                "writer membership backend is not configured"
            )
        proof = M6MigrationWriterMembershipProofV1.from_value(membership_proof)
        expected = expected_m6_migration_writer_membership_receipt_body_v1(
            state,
            writer_subject_root=writer_subject_root,
            writer_epoch=writer_epoch,
            membership_proof=proof,
        )
        request = {
            "schema": M6_MIGRATION_WRITER_MEMBERSHIP_REQUEST_SCHEMA_V1,
            "receipt_schema": expected["schema"],
            **{key: value for key, value in expected.items() if key != "schema"},
            "proof": proof.to_mapping(),
        }
        try:
            receipt = self.backend.verify_m6_migration_writer_membership(request)
        except M6MigrationAuthorityVerificationError:
            raise
        except Exception as exc:
            raise M6MigrationAuthorityProofRejectedV1(
                f"migration writer membership backend failed: {exc}"
            ) from exc
        if not isinstance(receipt, Mapping):
            raise M6MigrationAuthorityProofRejectedV1(
                "migration writer membership backend returned a non-object receipt"
            )
        _validated_receipt_root(receipt, expected, self.signer_registry)
        return M6MigrationAuthorityReceiptV1.from_mapping(receipt)


__all__ = [
    "M6_MIGRATION_AUTHORITY_REQUEST_SCHEMA_V1",
    "M6_MIGRATION_AUTHORITY_PROOF_SCHEMA_V1",
    "M6_MIGRATION_AUTHORITY_PAYLOAD_DOMAIN_V1",
    "M6_MIGRATION_AUTHORITY_PAYLOAD_KIND_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_REQUEST_SCHEMA_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_RECEIPT_SCHEMA_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_DOMAIN_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_BYTES_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_DEPTH_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_NODES_V1",
    "M6_MIGRATION_WRITER_MEMBERSHIP_PROOF_MAX_ITEMS_V1",
    "M6MigrationAuthorityVerificationError",
    "M6MigrationAuthorityVerifierUnavailableV1",
    "M6MigrationAuthorityProofRejectedV1",
    "M6MigrationAuthorityBackendV1",
    "M6MigrationWriterMembershipBackendV1",
    "M6MigrationWriterMembershipProofV1",
    "M6MigrationAuthorityReceiptV1",
    "M6MigrationVerifiedAdmissionV1",
    "M6MigrationAuthorityVerifierV1",
    "M6MigrationWriterMembershipVerifierV1",
    "expected_m6_migration_receipt_body_v1",
    "expected_m6_migration_writer_membership_receipt_body_v1",
    "migration_authority_payload_hash_v1",
]
