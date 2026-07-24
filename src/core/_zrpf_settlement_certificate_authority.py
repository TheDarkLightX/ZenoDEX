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

MAX_CANONICAL_SETTLEMENT_CERTIFICATE_BYTES_V1 = 1024
MAX_EXACT_SETTLEMENT_EFFECT_PLAN_BYTES_V1 = 8 * 1024 * 1024
MAX_SOURCE_OPENED_SETTLEMENT_REPLAY_BYTES_V1 = 8 * 1024 * 1024
MAX_DATA_AVAILABILITY_CERTIFICATE_BYTES_V1 = 512
MAX_SOURCE_OPENED_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 = 8_390_603
MAX_SOURCE_OPENED_SETTLEMENT_RECEIPT_BYTES_V1 = 16 * 1024 * 1024
MAX_SOURCE_OPENED_SETTLEMENT_GUEST_INPUT_BYTES_V1 = 1_131_478
MAX_SOURCE_OPENED_SETTLEMENT_PROJECTION_BYTES_V1 = 64 * 1024

SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6 = (
    "zrpf_source_opened_spot_settlement_v6"
)

_AUTHENTICATED_SETTLEMENT_CERTIFICATE_SEAL_V1 = object()
_AUTHENTICATED_SOURCE_OPENED_SPOT_V6_SEAL_V1 = object()
_SOURCE_OPENED_SPOT_V6_PROJECTION_BINDING_DOMAIN_V1 = (
    b"zenodex.zrpf.source_opened_spot_v6_projection_binding.v1"
)
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
    proof_tree_root: str
    dependency_manifest_root: str
    data_availability_certificate_root: str
    schedule_certificate_root: str
    carry_continuity_certificate_root: str
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
    source_opened_replay: bytes
    source_opened_replay_sha256: str
    data_availability_certificate: bytes
    data_availability_certificate_sha256: str
    action_nullifiers: tuple[str, ...]
    consumed_object_ids: tuple[str, ...]
    authorization_grant_spend_nullifiers: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.certificate_version) is not int or self.certificate_version != 1:
            raise ValueError("certificate_version must be exactly 1")
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
            "proof_tree_root",
            "dependency_manifest_root",
            "data_availability_certificate_root",
            "schedule_certificate_root",
            "carry_continuity_certificate_root",
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
        _require_exact_bytes(
            self.source_opened_replay,
            self.source_opened_replay_sha256,
            name="source-opened settlement replay",
            maximum=MAX_SOURCE_OPENED_SETTLEMENT_REPLAY_BYTES_V1,
        )
        _require_exact_bytes(
            self.data_availability_certificate,
            self.data_availability_certificate_sha256,
            name="data-availability certificate",
            maximum=MAX_DATA_AVAILABILITY_CERTIFICATE_BYTES_V1,
        )
        _require_unique_hashes(self.action_nullifiers, name="action_nullifiers")
        _require_unique_hashes(self.consumed_object_ids, name="consumed_object_ids")
        _require_unique_hashes(
            self.authorization_grant_spend_nullifiers,
            name="authorization_grant_spend_nullifiers",
        )


@dataclass(frozen=True, slots=True)
class _VerifiedSourceOpenedSpotV6AssociationV1:
    """Exact verifier artifacts associated with one Python V1 projection."""

    admission_journal: bytes
    admission_journal_sha256: str
    settlement_receipt: bytes
    settlement_receipt_sha256: str
    guest_input: bytes
    guest_input_sha256: str
    source_opened_replay_sha256: str
    settlement_certificate_id: str
    certificate_commitment: str
    governed_program_id: str
    governed_profile_id: str
    governed_manifest_root: str
    authorization_grant_spend_nullifier: str
    canonical_projection: bytes
    canonical_projection_sha256: str
    normalized_plan_commitment: str
    canonical_projection_binding_sha256: str

    def __post_init__(self) -> None:
        _require_exact_bytes(
            self.admission_journal,
            self.admission_journal_sha256,
            name="source-opened admission journal",
            maximum=MAX_SOURCE_OPENED_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
        )
        _require_exact_bytes(
            self.settlement_receipt,
            self.settlement_receipt_sha256,
            name="source-opened settlement receipt",
            maximum=MAX_SOURCE_OPENED_SETTLEMENT_RECEIPT_BYTES_V1,
        )
        _require_exact_bytes(
            self.guest_input,
            self.guest_input_sha256,
            name="source-opened guest input",
            maximum=MAX_SOURCE_OPENED_SETTLEMENT_GUEST_INPUT_BYTES_V1,
        )
        _require_exact_bytes(
            self.canonical_projection,
            self.canonical_projection_sha256,
            name="source-opened canonical projection",
            maximum=MAX_SOURCE_OPENED_SETTLEMENT_PROJECTION_BYTES_V1,
        )
        _require_bare_sha256(
            self.source_opened_replay_sha256,
            name="association.source_opened_replay_sha256",
        )
        for name in (
            "settlement_certificate_id",
            "certificate_commitment",
            "governed_program_id",
            "governed_profile_id",
            "governed_manifest_root",
            "authorization_grant_spend_nullifier",
            "normalized_plan_commitment",
        ):
            _require_nonzero_hash(getattr(self, name), name=f"association.{name}")
        _require_bare_sha256(
            self.canonical_projection_binding_sha256,
            name="association.canonical_projection_binding_sha256",
        )
        expected = _source_opened_spot_v6_projection_binding_v1(
            admission_journal_sha256=self.admission_journal_sha256,
            settlement_receipt_sha256=self.settlement_receipt_sha256,
            guest_input_sha256=self.guest_input_sha256,
            source_opened_replay_sha256=self.source_opened_replay_sha256,
            settlement_certificate_id=self.settlement_certificate_id,
            certificate_commitment=self.certificate_commitment,
            governed_program_id=self.governed_program_id,
            governed_profile_id=self.governed_profile_id,
            governed_manifest_root=self.governed_manifest_root,
            authorization_grant_spend_nullifier=self.authorization_grant_spend_nullifier,
            canonical_projection_sha256=self.canonical_projection_sha256,
            normalized_plan_commitment=self.normalized_plan_commitment,
        )
        if self.canonical_projection_binding_sha256 != expected:
            raise ValueError("source-opened canonical projection binding mismatch")


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


@final
class _AuthenticatedSourceOpenedSpotV6SettlementV1:
    """Sealed production bridge value carrying the exact V6 association."""

    __slots__ = ("_association", "_certificate", "_seal")
    _certificate: _AuthenticatedSettlementCertificateV1
    _association: _VerifiedSourceOpenedSpotV6AssociationV1
    _seal: object

    def __init__(
        self,
        certificate: _AuthenticatedSettlementCertificateV1,
        association: _VerifiedSourceOpenedSpotV6AssociationV1,
        *,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_SOURCE_OPENED_SPOT_V6_SEAL_V1:
            raise TypeError("authenticated source-opened V6 settlement requires the private seal")
        if type(certificate) is not _AuthenticatedSettlementCertificateV1:
            raise TypeError("source-opened V6 certificate capability has the wrong type")
        if not certificate._has_private_seal():
            raise TypeError("source-opened V6 certificate capability lacks the private seal")
        if type(association) is not _VerifiedSourceOpenedSpotV6AssociationV1:
            raise TypeError("source-opened V6 association has the wrong type")
        _validate_source_opened_spot_v6_association(certificate, association)
        object.__setattr__(self, "_certificate", certificate)
        object.__setattr__(self, "_association", association)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated source-opened V6 settlement cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise AttributeError("authenticated source-opened V6 settlement is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated source-opened V6 settlement cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated source-opened V6 settlement cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated source-opened V6 settlement cannot be serialized")

    @property
    def certificate(self) -> _AuthenticatedSettlementCertificateV1:
        return self._certificate

    @property
    def association(self) -> _VerifiedSourceOpenedSpotV6AssociationV1:
        return self._association

    def _has_private_seal(self) -> bool:
        try:
            return (
                object.__getattribute__(self, "_seal")
                is _AUTHENTICATED_SOURCE_OPENED_SPOT_V6_SEAL_V1
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


def _mint_authenticated_source_opened_spot_v6_after_verification(
    certificate: _AuthenticatedSettlementCertificateV1,
    association: _VerifiedSourceOpenedSpotV6AssociationV1,
) -> _AuthenticatedSourceOpenedSpotV6SettlementV1:
    """Seal an exact V6 verifier association after all bridge checks pass."""

    return _AuthenticatedSourceOpenedSpotV6SettlementV1(
        certificate,
        association,
        seal=_AUTHENTICATED_SOURCE_OPENED_SPOT_V6_SEAL_V1,
    )


def _validate_source_opened_spot_v6_association(
    authenticated: _AuthenticatedSettlementCertificateV1,
    association: _VerifiedSourceOpenedSpotV6AssociationV1,
) -> None:
    certificate = authenticated.certificate
    if certificate.settlement_profile_id != SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6:
        raise ValueError("source-opened V6 association requires the exact V6 profile")
    equalities = (
        (association.certificate_commitment, certificate.certificate_journal_hash, "certificate"),
        (association.governed_program_id, certificate.settlement_image_id, "program"),
        (
            association.governed_manifest_root[2:],
            certificate.settlement_manifest_sha256,
            "manifest",
        ),
        (
            association.settlement_receipt_sha256,
            certificate.settlement_receipt_id[2:],
            "receipt",
        ),
        (
            association.source_opened_replay_sha256,
            certificate.source_opened_replay_sha256,
            "source-opened replay hash",
        ),
        (association.normalized_plan_commitment, authenticated.plan.commitment, "projection plan"),
    )
    for observed, expected, name in equalities:
        if observed != expected:
            raise ValueError(f"source-opened V6 {name} association mismatch")
    if certificate.authorization_grant_spend_nullifiers != (
        association.authorization_grant_spend_nullifier,
    ):
        raise ValueError("source-opened V6 grant-spend association mismatch")


def _source_opened_spot_v6_projection_binding_v1(
    *,
    admission_journal_sha256: str,
    settlement_receipt_sha256: str,
    guest_input_sha256: str,
    source_opened_replay_sha256: str,
    settlement_certificate_id: str,
    certificate_commitment: str,
    governed_program_id: str,
    governed_profile_id: str,
    governed_manifest_root: str,
    authorization_grant_spend_nullifier: str,
    canonical_projection_sha256: str,
    normalized_plan_commitment: str,
) -> str:
    """Bind the Rust admission objects to one canonical Python projection."""

    bare_digests = (
        admission_journal_sha256,
        settlement_receipt_sha256,
        guest_input_sha256,
        source_opened_replay_sha256,
        canonical_projection_sha256,
    )
    for index, value in enumerate(bare_digests):
        _require_bare_sha256(value, name=f"projection binding digest {index}")
    prefixed = (
        settlement_certificate_id,
        certificate_commitment,
        governed_program_id,
        governed_profile_id,
        governed_manifest_root,
        authorization_grant_spend_nullifier,
        normalized_plan_commitment,
    )
    checked_prefixed = tuple(
        bytes.fromhex(_require_nonzero_hash(value, name="projection binding field")[2:])
        for value in prefixed
    )
    digest = hashlib.sha256()
    digest.update(len(_SOURCE_OPENED_SPOT_V6_PROJECTION_BINDING_DOMAIN_V1).to_bytes(2, "big"))
    digest.update(_SOURCE_OPENED_SPOT_V6_PROJECTION_BINDING_DOMAIN_V1)
    digest.update((1).to_bytes(2, "big"))
    for value in bare_digests:
        digest.update(bytes.fromhex(value))
    for digest_value in checked_prefixed:
        digest.update(digest_value)
    return digest.hexdigest()


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
    if certificate.settlement_profile_id == SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6:
        if len(plan.economic_action_ids) != 1:
            raise ValueError("source-opened V6 settlement requires exactly one economic action")
        if (
            len(certificate.action_nullifiers) != 1
            or certificate.action_nullifiers != certificate.consumed_object_ids
        ):
            raise ValueError(
                "source-opened V6 action nullifier must equal the sole consumed object"
            )
    if certificate.settlement_profile_id != SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6:
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
    equalities = [
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
    ]
    if certificate.settlement_profile_id != SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6:
        equalities.extend(
            (
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
