"""Private post-verification capability for state-bound ZRPF settlement.

The pinned settlement verifier is the only production adapter allowed to mint
this value.  The capability binds the exact receipt-derived certificate and
effect-plan bytes to the normalized rows consumed by the existing atomic
SQLite kernel.  It deliberately carries no settlement or release authority
while the final settlement image and governed release policy are pending.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn, final

from ._zrpf_settlement_effect_common import (
    MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1,
    _require_nonzero_hash,
)
from .recursive_stark_admission import (
    RecursiveStarkRootFacts,
    _AuthenticatedRecursiveStarkRootFacts,
)
from .zrpf_settlement_effect_plan import SettlementEffectPlanV1

SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1 = (
    "final_settlement_image_release_and_ledger_authority_pending"
)

MAX_CANONICAL_SETTLEMENT_CERTIFICATE_BYTES_V1 = 1024 * 1024
MAX_EXACT_SETTLEMENT_EFFECT_PLAN_BYTES_V1 = 128 * 1024 * 1024

_AUTHENTICATED_SETTLEMENT_CERTIFICATE_SEAL_V1 = object()
_TOKEN_CHARS = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-")


@dataclass(frozen=True, slots=True)
class _SettlementCertificateVerificationProvenanceV1:
    """Pinned verifier inputs retained with the durable certificate."""

    authority_manifest_sha256: str
    verifier_executable_sha256: str
    verification_request_sha256: str
    admission_policy_binding_sha256: str

    def __post_init__(self) -> None:
        for name in (
            "authority_manifest_sha256",
            "verifier_executable_sha256",
            "verification_request_sha256",
            "admission_policy_binding_sha256",
        ):
            _require_bare_sha256(getattr(self, name), name=f"provenance.{name}")


@dataclass(frozen=True, slots=True)
class _VerifiedSettlementEpochCertificateV1:
    """Strict verifier output retained behind the private capability seal."""

    certificate_version: int
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    public_policy_hash: str
    semantic_root_journal_hash: str
    semantic_claim_hash: str
    certificate_journal_hash: str
    settlement_claim_hash: str
    settlement_receipt_id: str
    settlement_image_id: str
    settlement_profile_id: str
    settlement_manifest_sha256: str
    pre_state_root: str
    post_state_root: str
    economic_action_ids_root: str
    ledger_cell_writes_root: str
    asset_effects_root: str
    action_authorization_bindings_root: str
    authorization_grant_spend_nullifiers_root: str
    consumed_object_ids_root: str
    message_effects_root: str
    carry_effects_root: str
    reward_effects_root: str
    effect_plan_commitment: str
    canonical_certificate: bytes
    canonical_certificate_sha256: str
    exact_effect_plan: bytes
    exact_effect_plan_sha256: str
    action_nullifiers: tuple[str, ...]
    consumed_object_ids: tuple[str, ...]
    authorization_grant_spend_nullifiers: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.certificate_version) is not int or self.certificate_version not in (1, 2):
            raise ValueError("certificate_version must be exactly 1 or 2")
        if type(self.epoch_id) is not int or isinstance(self.epoch_id, bool):
            raise TypeError("certificate epoch_id must be an int")
        if not 0 <= self.epoch_id <= (1 << 64) - 1:
            raise ValueError("certificate epoch_id must be in the unsigned 64-bit range")
        _require_token(
            self.settlement_profile_id,
            name="certificate.settlement_profile_id",
            max_bytes=128,
        )
        _require_bare_sha256(
            self.settlement_manifest_sha256,
            name="certificate.settlement_manifest_sha256",
        )
        for name in (
            "application_id",
            "chain_or_domain_id",
            "public_policy_hash",
            "semantic_root_journal_hash",
            "semantic_claim_hash",
            "certificate_journal_hash",
            "settlement_claim_hash",
            "settlement_receipt_id",
            "settlement_image_id",
            "pre_state_root",
            "post_state_root",
            "economic_action_ids_root",
            "ledger_cell_writes_root",
            "asset_effects_root",
            "action_authorization_bindings_root",
            "authorization_grant_spend_nullifiers_root",
            "consumed_object_ids_root",
            "message_effects_root",
            "carry_effects_root",
            "reward_effects_root",
            "effect_plan_commitment",
        ):
            _require_nonzero_hash(getattr(self, name), name=f"certificate.{name}")
        _require_exact_bytes(
            self.canonical_certificate,
            self.canonical_certificate_sha256,
            name="canonical certificate",
            maximum=MAX_CANONICAL_SETTLEMENT_CERTIFICATE_BYTES_V1,
        )
        _require_exact_bytes(
            self.exact_effect_plan,
            self.exact_effect_plan_sha256,
            name="exact effect plan",
            maximum=MAX_EXACT_SETTLEMENT_EFFECT_PLAN_BYTES_V1,
        )
        _require_unique_hashes(self.action_nullifiers, name="action_nullifiers")
        _require_unique_hashes(self.consumed_object_ids, name="consumed_object_ids")
        _require_unique_hashes(
            self.authorization_grant_spend_nullifiers,
            name="authorization_grant_spend_nullifiers",
        )


@final
class _AuthenticatedSettlementCertificateV1:
    """Immutable private capability consumed by the atomic settlement store."""

    __slots__ = ("_authenticated_root", "_certificate", "_plan", "_provenance", "_seal")
    _authenticated_root: _AuthenticatedRecursiveStarkRootFacts
    _certificate: _VerifiedSettlementEpochCertificateV1
    _plan: SettlementEffectPlanV1
    _provenance: _SettlementCertificateVerificationProvenanceV1
    _seal: object

    def __init__(
        self,
        authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
        certificate: _VerifiedSettlementEpochCertificateV1,
        plan: SettlementEffectPlanV1,
        provenance: _SettlementCertificateVerificationProvenanceV1,
        *,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_SETTLEMENT_CERTIFICATE_SEAL_V1:
            raise TypeError("authenticated settlement certificate requires the private seal")
        _validate_authenticated_certificate_binding(
            authenticated_root,
            certificate,
            plan,
            provenance,
        )
        object.__setattr__(self, "_authenticated_root", authenticated_root)
        object.__setattr__(self, "_certificate", certificate)
        object.__setattr__(self, "_plan", plan)
        object.__setattr__(self, "_provenance", provenance)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated settlement certificate cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise AttributeError("authenticated settlement certificate is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated settlement certificate cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated settlement certificate cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated settlement certificate cannot be serialized")

    @property
    def authenticated_root(self) -> _AuthenticatedRecursiveStarkRootFacts:
        return self._authenticated_root

    @property
    def certificate(self) -> _VerifiedSettlementEpochCertificateV1:
        return self._certificate

    @property
    def plan(self) -> SettlementEffectPlanV1:
        return self._plan

    @property
    def provenance(self) -> _SettlementCertificateVerificationProvenanceV1:
        return self._provenance

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1

    def _has_private_seal(self) -> bool:
        try:
            return (
                object.__getattribute__(self, "_seal")
                is _AUTHENTICATED_SETTLEMENT_CERTIFICATE_SEAL_V1
            )
        except AttributeError:
            return False


def _mint_authenticated_settlement_certificate_after_verification(
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    certificate: _VerifiedSettlementEpochCertificateV1,
    plan: SettlementEffectPlanV1,
    provenance: _SettlementCertificateVerificationProvenanceV1,
) -> _AuthenticatedSettlementCertificateV1:
    """Mint one sealed capability after the pinned verifier has accepted."""

    return _AuthenticatedSettlementCertificateV1(
        authenticated_root,
        certificate,
        plan,
        provenance,
        seal=_AUTHENTICATED_SETTLEMENT_CERTIFICATE_SEAL_V1,
    )


def _validate_authenticated_certificate_binding(
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    certificate: _VerifiedSettlementEpochCertificateV1,
    plan: SettlementEffectPlanV1,
    provenance: _SettlementCertificateVerificationProvenanceV1,
) -> None:
    if type(authenticated_root) is not _AuthenticatedRecursiveStarkRootFacts:
        raise TypeError("authenticated_root must be _AuthenticatedRecursiveStarkRootFacts")
    if not authenticated_root._has_private_seal():
        raise TypeError("authenticated_root lacks the private seal")
    if type(certificate) is not _VerifiedSettlementEpochCertificateV1:
        raise TypeError("certificate must be exact verified settlement certificate facts")
    if type(plan) is not SettlementEffectPlanV1:
        raise TypeError("plan must be exactly SettlementEffectPlanV1")
    if type(provenance) is not _SettlementCertificateVerificationProvenanceV1:
        raise TypeError("provenance must be exact settlement verification provenance")

    facts = authenticated_root.facts
    _require_certificate_plan_equalities(certificate, facts, plan)
    if certificate.settlement_receipt_id not in facts.accepted_receipt_ids:
        raise ValueError("settlement receipt identity is absent from authenticated root facts")
    for claim in (certificate.semantic_claim_hash, certificate.settlement_claim_hash):
        if claim not in facts.child_verification_claim_hashes:
            raise ValueError("settlement claim identity is absent from authenticated root facts")
    plan_messages = tuple(row.message_id for row in plan.message_effects)
    if plan_messages != facts.cross_shard_message_ids:
        raise ValueError("plan message identities do not match authenticated root facts")
    if len(certificate.action_nullifiers) != len(plan.economic_action_ids):
        raise ValueError("certificate requires exactly one nullifier per economic action")
    grant_spends = tuple(
        row.authorization_grant_spend_nullifier for row in plan.authorization_consumptions
    )
    if certificate.authorization_grant_spend_nullifiers != grant_spends:
        raise ValueError("certificate authorization grant spends do not match normalized plan")


def _require_certificate_plan_equalities(
    certificate: _VerifiedSettlementEpochCertificateV1,
    facts: RecursiveStarkRootFacts,
    plan: SettlementEffectPlanV1,
) -> None:
    equalities = (
        (certificate.semantic_root_journal_hash, facts.root_journal_hash, "semantic root"),
        (certificate.semantic_root_journal_hash, plan.source_root_journal_hash, "plan source root"),
        (certificate.epoch_id, facts.epoch_id, "recursive epoch"),
        (certificate.epoch_id, plan.epoch_id, "plan epoch"),
        (certificate.public_policy_hash, facts.public_policy_hash, "recursive public policy"),
        (certificate.public_policy_hash, plan.public_policy_hash, "plan public policy"),
        (certificate.application_id, plan.application_id, "application"),
        (certificate.chain_or_domain_id, plan.chain_or_domain_id, "chain or domain"),
        (certificate.pre_state_root, plan.pre_state_root, "pre-state root"),
        (certificate.post_state_root, plan.post_state_root, "post-state root"),
        (
            certificate.economic_action_ids_root,
            plan.economic_action_ids_root,
            "economic action IDs root",
        ),
        (
            certificate.ledger_cell_writes_root,
            plan.ledger_cell_writes_root,
            "ledger cell writes root",
        ),
        (certificate.asset_effects_root, plan.asset_effects_root, "asset effects root"),
        (certificate.message_effects_root, plan.message_effects_root, "message effects root"),
        (certificate.carry_effects_root, plan.carry_effects_root, "carry effects root"),
        (certificate.reward_effects_root, plan.reward_effects_root, "reward effects root"),
    )
    for observed, expected, name in equalities:
        if observed != expected:
            raise ValueError(f"verified settlement certificate {name} mismatch")


def _require_exact_bytes(value: object, expected_sha256: str, *, name: str, maximum: int) -> None:
    if type(value) is not bytes:
        raise TypeError(f"{name} must be bytes")
    if not value or len(value) > maximum:
        raise ValueError(f"{name} byte length is out of bounds")
    _require_bare_sha256(expected_sha256, name=f"{name} sha256")
    if hashlib.sha256(value).hexdigest() != expected_sha256:
        raise ValueError(f"{name} sha256 mismatch")


def _require_unique_hashes(values: object, *, name: str) -> None:
    if type(values) is not tuple:
        raise TypeError(f"{name} must be a tuple")
    if len(values) > MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1:
        raise ValueError(f"{name} exceeds the settlement row bound")
    seen: set[str] = set()
    for index, value in enumerate(values):
        checked = _require_nonzero_hash(value, name=f"{name}[{index}]")
        if checked in seen:
            raise ValueError(f"{name} must be unique")
        seen.add(checked)


def _require_bare_sha256(value: object, *, name: str) -> None:
    if type(value) is not str or len(value) != 64:
        raise ValueError(f"{name} must be lowercase 64-character hex")
    if any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be lowercase 64-character hex")


def _require_token(value: object, *, name: str, max_bytes: int) -> None:
    if type(value) is not str or not value:
        raise ValueError(f"{name} must be a non-empty string")
    if len(value.encode("ascii", errors="strict")) > max_bytes:
        raise ValueError(f"{name} exceeds {max_bytes} bytes")
    if any(character not in _TOKEN_CHARS for character in value):
        raise ValueError(f"{name} must use canonical token characters")
