"""Pinned bridge for the real source-opened ordinary-Spot V6 verifier CLI.

The Rust verifier authenticates the receipt and reconstructs the exact
``SettlementAdmissionJournalV1``.  This adapter checks the complete CLI
projection, builds the shared singleton Python settlement plan, seals the
cross-domain association, and submits it to the atomic SQLite store.

Rust V2 roots and Python V1 roots use different canonical hash domains.  Their
association is recorded through an explicit projection binding; this module
does not compare those incompatible roots or grant settlement authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, NoReturn, final

from src.core._zrpf_settlement_certificate_authority import (
    SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6,
    _AuthenticatedSourceOpenedSpotV6SettlementV1,
    _mint_authenticated_settlement_certificate_after_verification,
    _mint_authenticated_source_opened_spot_v6_after_verification,
    _SettlementCertificateVerificationProvenanceV1,
    _source_opened_spot_v6_projection_binding_v1,
    _VerifiedSettlementEpochCertificateV1,
    _VerifiedSourceOpenedSpotV6AssociationV1,
)
from src.core.recursive_stark_admission import (
    RecursiveStarkRootFacts,
    TrustedRecursiveStarkAdmissionPolicy,
    _mint_recursive_stark_root_facts_after_verification,
    _RecursiveStarkVerificationProvenance,
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)
from src.core.zrpf_settlement_effect_plan import (
    AssetEffectKindV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    LedgerCellWriteV1,
    ProposedSettlementEffectPlanV1,
    SettlementEffectPlanV1,
    authorization_consumption_nullifier_v1,
    build_settlement_effect_plan_v1,
)
from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    PinnedVerifierProcessError,
    PinnedVerifierProcessFailure,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration._zrpf_settlement_admission_journal_codec import (
    DecodedSettlementAdmissionJournalV1,
    SettlementAdmissionJournalDecodeErrorV1,
    SettlementSemanticRootKindV1,
    decode_exact_settlement_admission_journal_v1,
)
from src.integration.recursive_stark_verifier_adapter import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    MAX_AUTHORITY_MANIFEST_BYTES,
    RecursiveVerifierExecutableFormat,
    _reject_duplicate_object_keys,
    _reject_json_constant,
)
from src.integration.zrpf_source_opened_spot_v6_live_ledger_gate import (
    SourceOpenedSpotV6LiveLedgerBlockedV1,
    _reject_authenticated_source_opened_spot_v6_live_ledger_value_movement,
)
from src.state.canonical import canonical_json_bytes

if TYPE_CHECKING:
    from src.integration.recursive_stark_admission_store_types import (
        DurableRecursiveStarkAdmissionCursor,
    )
    from src.integration.zrpf_atomic_settlement_store import (
        SQLiteZrpfAtomicSettlementStoreV1,
    )
    from src.integration.zrpf_atomic_settlement_store_types import (
        DurableZrpfSettlementCursorV1,
        DurableZrpfStateBoundSettlementResultV1,
    )

SOURCE_OPENED_SPOT_V6_REQUEST_SCHEMA = (
    "zenodex.source_opened_spot_settlement_verifier_v6.request.v1"
)
SOURCE_OPENED_SPOT_V6_RESPONSE_SCHEMA = (
    "zenodex.source_opened_spot_settlement_verifier_v6.response.v1"
)
SOURCE_OPENED_SPOT_V6_AUTHORITY_MANIFEST_SCHEMA = (
    "zenodex.source_opened_spot_settlement_verifier_authority.v1"
)
SOURCE_OPENED_SPOT_V6_PROJECTION_SCHEMA = (
    "zenodex.source_opened_spot_settlement_python_projection.v1"
)

MAX_SOURCE_OPENED_SPOT_V6_RECEIPT_BYTES = 16 * 1024 * 1024
MAX_SOURCE_OPENED_SPOT_V6_GUEST_INPUT_BYTES = 1_131_478
MAX_SOURCE_OPENED_SPOT_V6_RESPONSE_BYTES = 16 * 1024 * 1024
MAX_SOURCE_OPENED_SPOT_V6_STDERR_BYTES = 1024 * 1024
MAX_SOURCE_OPENED_SPOT_V6_REQUEST_BYTES = 40 * 1024 * 1024

_NON_RELEASE_POLICY_BINDING_DOMAIN = b"zenodex.zrpf.source_opened_spot_v6_non_release_policy.v1"

_AUTHORITY_KEYS = frozenset(
    {
        "schema",
        "executable_sha256",
        "executable_format",
        "application_id",
        "chain_id",
        "chain_or_domain_id",
        "epoch_id",
        "proof_profile",
        "public_policy_hash",
        "verifier_set_root",
        "governed_settlement_program_id",
        "governed_settlement_profile_id",
        "governed_settlement_manifest_root",
        "receipt_security_profile",
    }
)
_RECEIPT_PROFILE_KEYS = frozenset(
    {"profile_id", "receipt_kind", "verifier_parameters", "hashfn", "control_id"}
)
_VERIFIED_ADMISSION_KEYS = frozenset(
    {
        "receipt_bytes",
        "receipt_sha256",
        "guest_input_bytes",
        "guest_input_sha256",
        "admission_journal_bytes",
        "admission_journal_hex",
        "admission_journal_sha256",
        "certificate_bytes",
        "certificate_hex",
        "certificate_sha256",
        "effect_plan_bytes",
        "effect_plan_hex",
        "effect_plan_sha256",
        "governed_settlement_program_id",
        "governed_settlement_profile_id",
        "governed_settlement_manifest_root",
        "settlement_claim_binding",
        "receipt_security_profile",
        "admission_projection",
        "execution_projection",
    }
)
_ADMISSION_PROJECTION_KEYS = frozenset(
    {
        "journal_version",
        "certificate_version",
        "effect_plan_version",
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "semantic_profile_id",
        "semantic_journal_hash",
        "semantic_claim_binding",
        "proof_tree_root",
        "semantic_root_kind",
        "semantic_root",
        "dependency_manifest_root",
        "public_policy_hash",
        "economic_action_batch_commitment",
        "settlement_effect_plan_commitment",
        "economic_action_ids_root",
        "action_authorization_bindings_root",
        "authorization_grant_spends_root",
        "consumed_object_ids_root",
        "action_count",
        "consumed_object_count",
        "pre_state_root",
        "post_state_root",
        "cell_writes_root",
        "asset_effects_root",
        "messages_root",
        "carries_root",
        "rewards_root",
        "data_availability_certificate_root",
        "schedule_certificate_root",
        "carry_continuity_certificate_root",
        "settlement_certificate_id",
        "certificate_commitment",
    }
)
_EXECUTION_PROJECTION_KEYS = frozenset(
    {
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "pre_state_root",
        "post_state_root",
        "action",
        "cell_write",
        "ordinary_asset_rows",
    }
)
_ACTION_KEYS = frozenset(
    {
        "action_id",
        "action_type_id",
        "authorization_subject_id",
        "authorization_scope_id",
        "authorization_nonce",
        "authorization_grant_id",
        "action_authorization_binding",
        "authorization_grant_spend_nullifier",
        "valid_from_epoch",
        "valid_through_epoch",
        "pre_state_root",
        "action_semantics_hash",
        "effect_commitment",
        "consumed_object_ids",
    }
)
_CELL_KEYS = frozenset(
    {"economic_action_id", "cell_key", "pre_value_hash", "post_value_hash"}
)
_ASSET_KEYS = frozenset(
    {"economic_action_id", "asset_id", "debit_atoms", "credit_atoms"}
)


class SourceOpenedSpotV6VerificationError(ValueError):
    """Stable fail-closed bridge error."""


@dataclass(frozen=True, slots=True)
class _ParsedSourceOpenedSpotV6:
    certificate: _VerifiedSettlementEpochCertificateV1
    plan: SettlementEffectPlanV1
    association: _VerifiedSourceOpenedSpotV6AssociationV1


@final
@dataclass(frozen=True)
class PinnedSourceOpenedSpotSettlementVerifierV6:
    """Pinned executable and governed identities for the real V6 CLI."""

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)
    executable_format: RecursiveVerifierExecutableFormat = field(init=False)
    policy: Mapping[str, Any] = field(init=False)
    _policy_json: bytes = field(init=False, repr=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedSourceOpenedSpotSettlementVerifierV6 cannot be subclassed")

    def __post_init__(self) -> None:
        if not isinstance(self.executable, Path) or not self.executable.is_absolute():
            raise ValueError("source-opened verifier executable must be an absolute pathlib.Path")
        _require_bare_hash(self.authority_manifest_sha256, "authority manifest sha256")
        if type(self.timeout_seconds) is not int or not 1 <= self.timeout_seconds <= 300:
            raise ValueError("source-opened verifier timeout must be in 1..300")
        if self.max_address_space_bytes < 256 * 1024 * 1024:
            raise ValueError("source-opened verifier address-space limit is too small")
        if self.max_stack_bytes < 1024 * 1024:
            raise ValueError("source-opened verifier stack limit is too small")
        executable_sha256, executable_format, policy_json = _parse_authority_manifest(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        object.__setattr__(self, "sha256", executable_sha256)
        object.__setattr__(self, "executable_format", executable_format)
        object.__setattr__(self, "policy", json.loads(policy_json))
        object.__setattr__(self, "_policy_json", policy_json)

    def verify_and_commit(
        self,
        *,
        store: SQLiteZrpfAtomicSettlementStoreV1,
        expected_admission_cursor: DurableRecursiveStarkAdmissionCursor,
        expected_settlement_cursor: DurableZrpfSettlementCursorV1,
        settlement_receipt: bytes,
        guest_input: bytes,
    ) -> DurableZrpfStateBoundSettlementResultV1:
        """Verify exact bytes once and atomically persist the V6 association."""

        from src.integration.recursive_stark_admission_store_types import (
            DurableRecursiveStarkAdmissionCursor,
        )
        from src.integration.zrpf_atomic_settlement_store import (
            SQLiteZrpfAtomicSettlementStoreV1,
        )
        from src.integration.zrpf_atomic_settlement_store_types import (
            DurableZrpfSettlementCursorV1,
        )

        if type(store) is not SQLiteZrpfAtomicSettlementStoreV1:
            raise TypeError("store must be exactly SQLiteZrpfAtomicSettlementStoreV1")
        if type(expected_admission_cursor) is not DurableRecursiveStarkAdmissionCursor:
            raise TypeError("expected_admission_cursor has the wrong type")
        if type(expected_settlement_cursor) is not DurableZrpfSettlementCursorV1:
            raise TypeError("expected_settlement_cursor has the wrong type")
        authenticated = self._verify_and_seal(settlement_receipt, guest_input)
        return store._commit_authenticated_source_opened_spot_v6(
            expected_admission_cursor=expected_admission_cursor,
            expected_settlement_cursor=expected_settlement_cursor,
            authenticated_source_opened=authenticated,
        )

    def verify_live_ledger_value_movement(
        self,
        *,
        settlement_receipt: bytes,
        guest_input: bytes,
    ) -> SourceOpenedSpotV6LiveLedgerBlockedV1:
        """Authenticate V6 evidence and return the required value-movement no-op.

        The authenticated plan has commitment-only cell writes and aggregate
        asset totals.  Until it carries governed raw ledger values and a live
        state transition authority, this path cannot open or mutate a store.
        """

        authenticated = self._verify_and_seal(settlement_receipt, guest_input)
        return _reject_authenticated_source_opened_spot_v6_live_ledger_value_movement(authenticated)

    def _verify_and_seal(
        self,
        settlement_receipt: bytes,
        guest_input: bytes,
    ) -> _AuthenticatedSourceOpenedSpotV6SettlementV1:
        if self.executable_format is not RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64:
            raise SourceOpenedSpotV6VerificationError(
                "source-opened V6 durable admission requires a static ELF verifier"
            )
        request = source_opened_spot_v6_request_bytes(settlement_receipt, guest_input)
        stdout = self._execute_verifier_once(request)
        parsed = _parse_source_opened_spot_v6_response(
            stdout,
            settlement_receipt=settlement_receipt,
            guest_input=guest_input,
            policy=self.policy,
        )
        return self._seal_verified_result(parsed, request)

    def _seal_verified_result(
        self,
        parsed: _ParsedSourceOpenedSpotV6,
        request: bytes,
    ) -> _AuthenticatedSourceOpenedSpotV6SettlementV1:
        policy_binding = hashlib.sha256(
            _NON_RELEASE_POLICY_BINDING_DOMAIN + bytes.fromhex(self.authority_manifest_sha256)
        ).hexdigest()
        policy = TrustedRecursiveStarkAdmissionPolicy(
            expected_chain_id=_policy_str(self.policy, "chain_id"),
            expected_epoch_id=_policy_int(self.policy, "epoch_id"),
            expected_proof_profile=_policy_str(self.policy, "proof_profile"),
            expected_verifier_set_root=_prefixed_hash(
                _policy_str(self.policy, "verifier_set_root")
            ),
            expected_public_policy_hash=parsed.certificate.public_policy_hash,
        )
        provenance = _RecursiveStarkVerificationProvenance(
            authority_manifest_sha256=self.authority_manifest_sha256,
            verifier_executable_sha256=self.sha256,
            verification_request_sha256=hashlib.sha256(request).hexdigest(),
            release_binding_config_digest="0x" + policy_binding,
            replay_manifest_sha256="sha256:" + parsed.certificate.settlement_manifest_sha256,
        )
        root = _root_facts(parsed.certificate, parsed.plan, self.policy)
        try:
            authenticated_root = _mint_recursive_stark_root_facts_after_verification(
                root,
                policy,
                provenance,
            )
            certificate_provenance = _SettlementCertificateVerificationProvenanceV1(
                authority_manifest_sha256=self.authority_manifest_sha256,
                verifier_executable_sha256=self.sha256,
                verification_request_sha256=hashlib.sha256(request).hexdigest(),
                admission_policy_binding_sha256=policy_binding,
            )
            authenticated_certificate = (
                _mint_authenticated_settlement_certificate_after_verification(
                    authenticated_root,
                    parsed.certificate,
                    parsed.plan,
                    certificate_provenance,
                )
            )
            return _mint_authenticated_source_opened_spot_v6_after_verification(
                authenticated_certificate,
                parsed.association,
            )
        except (TypeError, ValueError) as exc:
            raise SourceOpenedSpotV6VerificationError(
                "source-opened V6 capability binding is invalid"
            ) from exc

    def _execute_verifier_once(self, request: bytes) -> bytes:
        try:
            return execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self.sha256,
                executable_format=VerifierExecutableFormatV1(self.executable_format.value),
                request_bytes=request,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
                max_stdout_bytes=MAX_SOURCE_OPENED_SPOT_V6_RESPONSE_BYTES,
                max_stderr_bytes=MAX_SOURCE_OPENED_SPOT_V6_STDERR_BYTES,
            )
        except PinnedVerifierProcessError as exc:
            raise _source_opened_process_error(exc) from exc


def _source_opened_process_error(
    error: PinnedVerifierProcessError,
) -> SourceOpenedSpotV6VerificationError:
    if error.reason is PinnedVerifierProcessFailure.EXECUTABLE_HASH_MISMATCH:
        return SourceOpenedSpotV6VerificationError("verifier binary hash mismatch")
    if error.reason is PinnedVerifierProcessFailure.TIMEOUT:
        return SourceOpenedSpotV6VerificationError("source-opened verifier timed out")
    if error.reason is PinnedVerifierProcessFailure.OUTPUT_INVALID:
        if error.detail == "verifier stdout exceeds byte limit":
            return SourceOpenedSpotV6VerificationError(
                "source-opened verifier response too large"
            )
        return SourceOpenedSpotV6VerificationError(
            f"source-opened verifier output invalid: {error.detail}"
        )
    exit_prefix = "pinned verifier exited with status "
    if error.detail.startswith(exit_prefix):
        return SourceOpenedSpotV6VerificationError(
            "source-opened verifier exited with status "
            + error.detail.removeprefix(exit_prefix)
        )
    return SourceOpenedSpotV6VerificationError(
        f"source-opened verifier process failed: {error.detail}"
    )


def source_opened_spot_v6_request_bytes(settlement_receipt: bytes, guest_input: bytes) -> bytes:
    """Produce the exact Rust struct-field request order."""

    _require_exact_input_bytes(
        settlement_receipt,
        maximum=MAX_SOURCE_OPENED_SPOT_V6_RECEIPT_BYTES,
        name="settlement receipt",
    )
    _require_exact_input_bytes(
        guest_input,
        maximum=MAX_SOURCE_OPENED_SPOT_V6_GUEST_INPUT_BYTES,
        name="source-opened guest input",
    )
    request = {
        "schema": SOURCE_OPENED_SPOT_V6_REQUEST_SCHEMA,
        "receipt_hex": settlement_receipt.hex(),
        "guest_input_hex": guest_input.hex(),
    }
    raw = json.dumps(request, ensure_ascii=True, separators=(",", ":")).encode("ascii")
    if len(raw) > MAX_SOURCE_OPENED_SPOT_V6_REQUEST_BYTES:
        raise SourceOpenedSpotV6VerificationError("source-opened verifier request too large")
    return raw


def source_opened_spot_v6_authority_manifest_bytes(
    *,
    executable_sha256: str,
    policy: Mapping[str, Any],
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> bytes:
    """Build the canonical replaceable V6 verifier authority manifest."""

    _require_bare_hash(executable_sha256, "executable_sha256")
    if type(executable_format) is not RecursiveVerifierExecutableFormat:
        raise ValueError("source-opened verifier executable format is invalid")
    copied = _strict_policy_copy(policy)
    value = {
        "schema": SOURCE_OPENED_SPOT_V6_AUTHORITY_MANIFEST_SCHEMA,
        "executable_sha256": executable_sha256,
        "executable_format": executable_format.value,
        **copied,
    }
    raw = canonical_json_bytes(value)
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("source-opened authority manifest exceeds its byte bound")
    return raw


def _parse_authority_manifest(
    raw: bytes,
    *,
    expected_sha256: str,
) -> tuple[str, RecursiveVerifierExecutableFormat, bytes]:
    if type(raw) is not bytes or not raw or len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("source-opened authority manifest byte length is invalid")
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("source-opened authority manifest hash mismatch")
    value = _decode_canonical_json_object(raw, "source-opened authority manifest")
    if canonical_json_bytes(value) != raw:
        raise ValueError("source-opened authority manifest must be canonical JSON")
    if set(value) != _AUTHORITY_KEYS:
        raise ValueError("source-opened authority manifest schema mismatch")
    if value.get("schema") != SOURCE_OPENED_SPOT_V6_AUTHORITY_MANIFEST_SCHEMA:
        raise ValueError("source-opened authority manifest schema unsupported")
    executable_sha256 = _plain_string(value, "executable_sha256")
    _require_bare_hash(executable_sha256, "manifest executable_sha256")
    try:
        executable_format = RecursiveVerifierExecutableFormat(
            _plain_string(value, "executable_format")
        )
    except ValueError as exc:
        raise ValueError("source-opened executable format unsupported") from exc
    policy = {key: value[key] for key in value if key not in {"schema", "executable_sha256", "executable_format"}}
    copied = _strict_policy_copy(policy)
    return executable_sha256, executable_format, canonical_json_bytes(copied)


def _parse_source_opened_spot_v6_response(
    raw: bytes,
    *,
    settlement_receipt: bytes,
    guest_input: bytes,
    policy: Mapping[str, Any],
) -> _ParsedSourceOpenedSpotV6:
    if type(raw) is not bytes or not raw or len(raw) > MAX_SOURCE_OPENED_SPOT_V6_RESPONSE_BYTES:
        raise SourceOpenedSpotV6VerificationError("source-opened response byte length is invalid")
    response = _decode_canonical_json_object(raw, "source-opened verifier response")
    if json.dumps(response, ensure_ascii=True, separators=(",", ":")).encode("ascii") != raw:
        raise SourceOpenedSpotV6VerificationError(
            "source-opened verifier response must be canonical JSON"
        )
    if list(response) != ["ok", "schema", "verified_settlement_admission"]:
        raise SourceOpenedSpotV6VerificationError("source-opened response field order mismatch")
    if response.get("ok") is not True or response.get("schema") != SOURCE_OPENED_SPOT_V6_RESPONSE_SCHEMA:
        raise SourceOpenedSpotV6VerificationError("source-opened response schema mismatch")
    values = _exact_mapping(
        response.get("verified_settlement_admission"),
        _VERIFIED_ADMISSION_KEYS,
        "verified_settlement_admission",
    )
    _require_exact_artifact_echoes(values, settlement_receipt, guest_input)
    journal_bytes = _hex_bytes(values, "admission_journal_hex")
    _require_length_and_hash(
        journal_bytes,
        values,
        length_key="admission_journal_bytes",
        hash_key="admission_journal_sha256",
        name="admission journal",
    )
    try:
        journal = decode_exact_settlement_admission_journal_v1(journal_bytes)
    except (SettlementAdmissionJournalDecodeErrorV1, TypeError) as exc:
        raise SourceOpenedSpotV6VerificationError("admission journal fails exact decoding") from exc
    admission = _exact_mapping(
        values.get("admission_projection"),
        _ADMISSION_PROJECTION_KEYS,
        "admission_projection",
    )
    _require_admission_projection(admission, journal)
    _require_inner_object_echoes(values, journal)
    _require_governed_bindings(values, journal, policy)
    execution = _exact_mapping(
        values.get("execution_projection"),
        _EXECUTION_PROJECTION_KEYS,
        "execution_projection",
    )
    plan, consumed_ids, grant_spends = _build_singleton_spot_projection(execution, journal)
    projection = canonical_json_bytes(
        {
            "schema": SOURCE_OPENED_SPOT_V6_PROJECTION_SCHEMA,
            "admission_projection": dict(admission),
            "execution_projection": dict(execution),
            "normalized_effect_plan": plan.to_commitment_obj(),
        }
    )
    projection_sha256 = hashlib.sha256(projection).hexdigest()
    receipt_sha256 = hashlib.sha256(settlement_receipt).hexdigest()
    guest_sha256 = hashlib.sha256(guest_input).hexdigest()
    program_id = _prefixed_hash(_plain_string(values, "governed_settlement_program_id"))
    profile_id = _prefixed_hash(_plain_string(values, "governed_settlement_profile_id"))
    manifest_root = _prefixed_hash(
        _plain_string(values, "governed_settlement_manifest_root")
    )
    certificate_id = _prefixed_hash(_plain_string(admission, "settlement_certificate_id"))
    certificate_commitment = _prefixed_hash(
        _plain_string(admission, "certificate_commitment")
    )
    # These bytes are retained for deterministic replay and content-integrity
    # checking. They do not establish storage availability or external finality.
    source_opened_replay, da_certificate = _extract_replay_and_da_certificate(
        guest_input,
        journal.effect_plan_bytes,
    )
    replay_sha256 = hashlib.sha256(source_opened_replay).hexdigest()
    binding = _source_opened_spot_v6_projection_binding_v1(
        admission_journal_sha256=hashlib.sha256(journal_bytes).hexdigest(),
        settlement_receipt_sha256=receipt_sha256,
        guest_input_sha256=guest_sha256,
        source_opened_replay_sha256=replay_sha256,
        settlement_certificate_id=certificate_id,
        certificate_commitment=certificate_commitment,
        governed_program_id=program_id,
        governed_profile_id=profile_id,
        governed_manifest_root=manifest_root,
        authorization_grant_spend_nullifier=grant_spends[0],
        canonical_projection_sha256=projection_sha256,
        normalized_plan_commitment=plan.commitment,
    )
    certificate = _VerifiedSettlementEpochCertificateV1(
        certificate_version=journal.certificate_version,
        application_id=_prefixed(journal.application_id),
        chain_or_domain_id=_prefixed(journal.chain_or_domain_id),
        epoch_id=journal.epoch_id,
        public_policy_hash=_prefixed(journal.public_policy_hash),
        semantic_root_journal_hash=_prefixed(journal.semantic_journal_hash),
        semantic_claim_hash=_prefixed(journal.semantic_claim_binding),
        certificate_journal_hash=certificate_commitment,
        settlement_claim_hash=_prefixed_hash(_plain_string(values, "settlement_claim_binding")),
        settlement_receipt_id="0x" + receipt_sha256,
        settlement_image_id=program_id,
        settlement_profile_id=SOURCE_OPENED_SINGLETON_SPOT_SETTLEMENT_PROFILE_V6,
        settlement_manifest_sha256=manifest_root[2:],
        pre_state_root=_prefixed(journal.pre_state_root),
        post_state_root=_prefixed(journal.post_state_root),
        economic_action_ids_root=_prefixed(journal.economic_action_ids_root),
        ledger_cell_writes_root=_prefixed(journal.cell_writes_root),
        asset_effects_root=_prefixed(journal.asset_effects_root),
        proof_tree_root=_prefixed(journal.proof_tree_root),
        dependency_manifest_root=_prefixed(journal.dependency_manifest_root),
        data_availability_certificate_root=_prefixed(
            journal.data_availability_certificate_root
        ),
        schedule_certificate_root=_prefixed(journal.schedule_certificate_root),
        carry_continuity_certificate_root=_prefixed(
            journal.carry_continuity_certificate_root
        ),
        action_authorization_bindings_root=_prefixed(
            journal.action_authorization_bindings_root
        ),
        authorization_grant_spend_nullifiers_root=_prefixed(
            journal.authorization_grant_spends_root
        ),
        consumed_object_ids_root=_prefixed(journal.consumed_object_ids_root),
        message_effects_root=_prefixed(journal.messages_root),
        carry_effects_root=_prefixed(journal.carries_root),
        reward_effects_root=_prefixed(journal.rewards_root),
        effect_plan_commitment=_prefixed(journal.settlement_effect_plan_commitment),
        canonical_certificate=journal.certificate_bytes,
        canonical_certificate_sha256=journal.certificate_sha256.hex(),
        exact_effect_plan=journal.effect_plan_bytes,
        exact_effect_plan_sha256=journal.effect_plan_sha256.hex(),
        source_opened_replay=source_opened_replay,
        source_opened_replay_sha256=replay_sha256,
        data_availability_certificate=da_certificate,
        data_availability_certificate_sha256=hashlib.sha256(da_certificate).hexdigest(),
        action_nullifiers=consumed_ids,
        consumed_object_ids=consumed_ids,
        authorization_grant_spend_nullifiers=grant_spends,
    )
    association = _VerifiedSourceOpenedSpotV6AssociationV1(
        admission_journal=journal_bytes,
        admission_journal_sha256=journal.journal_sha256.hex(),
        settlement_receipt=settlement_receipt,
        settlement_receipt_sha256=receipt_sha256,
        guest_input=guest_input,
        guest_input_sha256=guest_sha256,
        source_opened_replay_sha256=replay_sha256,
        settlement_certificate_id=certificate_id,
        certificate_commitment=certificate_commitment,
        governed_program_id=program_id,
        governed_profile_id=profile_id,
        governed_manifest_root=manifest_root,
        authorization_grant_spend_nullifier=grant_spends[0],
        canonical_projection=projection,
        canonical_projection_sha256=projection_sha256,
        normalized_plan_commitment=plan.commitment,
        canonical_projection_binding_sha256=binding,
    )
    return _ParsedSourceOpenedSpotV6(certificate, plan, association)


def _require_exact_artifact_echoes(
    values: Mapping[str, Any],
    settlement_receipt: bytes,
    guest_input: bytes,
) -> None:
    for name, source in (("receipt", settlement_receipt), ("guest_input", guest_input)):
        if _strict_int(values, f"{name}_bytes") != len(source):
            raise SourceOpenedSpotV6VerificationError(f"{name} byte count mismatch")
        if _bare_hash(values, f"{name}_sha256") != hashlib.sha256(source).hexdigest():
            raise SourceOpenedSpotV6VerificationError(f"{name} SHA-256 mismatch")


def _require_inner_object_echoes(
    values: Mapping[str, Any],
    journal: DecodedSettlementAdmissionJournalV1,
) -> None:
    cases = (
        ("certificate", journal.certificate_bytes, journal.certificate_sha256.hex()),
        ("effect_plan", journal.effect_plan_bytes, journal.effect_plan_sha256.hex()),
    )
    for name, expected_bytes, expected_hash in cases:
        observed = _hex_bytes(values, f"{name}_hex")
        if observed != expected_bytes:
            raise SourceOpenedSpotV6VerificationError(f"{name} exact bytes mismatch")
        if _strict_int(values, f"{name}_bytes") != len(expected_bytes):
            raise SourceOpenedSpotV6VerificationError(f"{name} byte count mismatch")
        if _bare_hash(values, f"{name}_sha256") != expected_hash:
            raise SourceOpenedSpotV6VerificationError(f"{name} SHA-256 mismatch")


def _require_admission_projection(
    values: Mapping[str, Any],
    journal: DecodedSettlementAdmissionJournalV1,
) -> None:
    integer_fields = {
        "journal_version": journal.journal_version,
        "certificate_version": journal.certificate_version,
        "effect_plan_version": journal.effect_plan_version,
        "epoch_id": journal.epoch_id,
        "action_count": journal.action_count,
        "consumed_object_count": journal.consumed_object_count,
    }
    for name, expected in integer_fields.items():
        if _strict_int(values, name) != expected:
            raise SourceOpenedSpotV6VerificationError(f"admission {name} mismatch")
    hash_fields = {
        "application_id": journal.application_id,
        "chain_or_domain_id": journal.chain_or_domain_id,
        "semantic_profile_id": journal.semantic_profile_id,
        "semantic_journal_hash": journal.semantic_journal_hash,
        "semantic_claim_binding": journal.semantic_claim_binding,
        "proof_tree_root": journal.proof_tree_root,
        "semantic_root": journal.semantic_root,
        "dependency_manifest_root": journal.dependency_manifest_root,
        "public_policy_hash": journal.public_policy_hash,
        "economic_action_batch_commitment": journal.economic_action_batch_commitment,
        "settlement_effect_plan_commitment": journal.settlement_effect_plan_commitment,
        "economic_action_ids_root": journal.economic_action_ids_root,
        "action_authorization_bindings_root": journal.action_authorization_bindings_root,
        "authorization_grant_spends_root": journal.authorization_grant_spends_root,
        "consumed_object_ids_root": journal.consumed_object_ids_root,
        "pre_state_root": journal.pre_state_root,
        "post_state_root": journal.post_state_root,
        "cell_writes_root": journal.cell_writes_root,
        "asset_effects_root": journal.asset_effects_root,
        "messages_root": journal.messages_root,
        "carries_root": journal.carries_root,
        "rewards_root": journal.rewards_root,
        "data_availability_certificate_root": journal.data_availability_certificate_root,
        "schedule_certificate_root": journal.schedule_certificate_root,
        "carry_continuity_certificate_root": journal.carry_continuity_certificate_root,
        "settlement_certificate_id": journal.settlement_certificate_id,
        "certificate_commitment": journal.certificate_commitment,
    }
    for name, expected_hash in hash_fields.items():
        if _bare_hash(values, name) != expected_hash.hex():
            raise SourceOpenedSpotV6VerificationError(f"admission {name} mismatch")
    expected_kind = {
        SettlementSemanticRootKindV1.SEMANTIC_EPOCH: "semantic_epoch",
        SettlementSemanticRootKindV1.VALUE_SUBTREE: "value_subtree",
    }[journal.semantic_root_kind]
    if _plain_string(values, "semantic_root_kind") != expected_kind:
        raise SourceOpenedSpotV6VerificationError("admission semantic root kind mismatch")


def _require_governed_bindings(
    values: Mapping[str, Any],
    journal: DecodedSettlementAdmissionJournalV1,
    policy: Mapping[str, Any],
) -> None:
    cases = (
        ("governed_settlement_program_id", "governed_settlement_program_id"),
        ("governed_settlement_profile_id", "governed_settlement_profile_id"),
        ("governed_settlement_manifest_root", "governed_settlement_manifest_root"),
    )
    for observed_key, policy_key in cases:
        if _bare_hash(values, observed_key) != _bare_hash(policy, policy_key):
            raise SourceOpenedSpotV6VerificationError(f"{observed_key} policy mismatch")
    if _bare_hash(values, "governed_settlement_profile_id") != journal.semantic_profile_id.hex():
        raise SourceOpenedSpotV6VerificationError("journal semantic profile is not governed")
    for key, observed in (
        ("application_id", journal.application_id.hex()),
        ("chain_or_domain_id", journal.chain_or_domain_id.hex()),
        ("public_policy_hash", journal.public_policy_hash.hex()),
    ):
        if _bare_hash(policy, key) != observed:
            raise SourceOpenedSpotV6VerificationError(f"journal {key} policy mismatch")
    if _policy_int(policy, "epoch_id") != journal.epoch_id:
        raise SourceOpenedSpotV6VerificationError("journal epoch policy mismatch")
    profile = _exact_mapping(
        values.get("receipt_security_profile"),
        _RECEIPT_PROFILE_KEYS,
        "receipt_security_profile",
    )
    expected_profile = _exact_mapping(
        policy.get("receipt_security_profile"),
        _RECEIPT_PROFILE_KEYS,
        "governed receipt_security_profile",
    )
    if profile != expected_profile:
        raise SourceOpenedSpotV6VerificationError("receipt security profile policy mismatch")


def _build_singleton_spot_projection(
    execution: Mapping[str, Any],
    journal: DecodedSettlementAdmissionJournalV1,
) -> tuple[SettlementEffectPlanV1, tuple[str, ...], tuple[str, ...]]:
    scope = {
        "application_id": _prefixed_hash(_plain_string(execution, "application_id")),
        "chain_or_domain_id": _prefixed_hash(_plain_string(execution, "chain_or_domain_id")),
        "pre_state_root": _prefixed_hash(_plain_string(execution, "pre_state_root")),
        "post_state_root": _prefixed_hash(_plain_string(execution, "post_state_root")),
    }
    expected_scope = {
        "application_id": _prefixed(journal.application_id),
        "chain_or_domain_id": _prefixed(journal.chain_or_domain_id),
        "pre_state_root": _prefixed(journal.pre_state_root),
        "post_state_root": _prefixed(journal.post_state_root),
    }
    if scope != expected_scope or _strict_int(execution, "epoch_id") != journal.epoch_id:
        raise SourceOpenedSpotV6VerificationError("execution projection scope mismatch")
    action = _exact_mapping(execution.get("action"), _ACTION_KEYS, "execution action")
    action_id = _prefixed_hash(_plain_string(action, "action_id"))
    action_pre_state = _prefixed_hash(_plain_string(action, "pre_state_root"))
    if action_pre_state != scope["pre_state_root"]:
        raise SourceOpenedSpotV6VerificationError("action pre-state mismatch")
    valid_from = _strict_int(action, "valid_from_epoch")
    valid_through = _strict_int(action, "valid_through_epoch")
    if not valid_from <= journal.epoch_id <= valid_through:
        raise SourceOpenedSpotV6VerificationError("action validity window excludes the epoch")
    consumed = _hash_list(action, "consumed_object_ids", expected_length=1)
    subject = _prefixed_hash(_plain_string(action, "authorization_subject_id"))
    grant = _prefixed_hash(_plain_string(action, "authorization_grant_id"))
    auth_scope = _prefixed_hash(_plain_string(action, "authorization_scope_id"))
    auth_nonce = _strict_int(action, "authorization_nonce")
    nullifier = authorization_consumption_nullifier_v1(
        application_id=scope["application_id"],
        chain_or_domain_id=scope["chain_or_domain_id"],
        economic_action_id=action_id,
        authorization_subject_id=subject,
        authorization_grant_id=grant,
        authorization_scope_id=auth_scope,
        authorization_nonce=auth_nonce,
        action_pre_state_root=action_pre_state,
    )
    authorization = AuthorizationConsumptionV1(
        application_id=scope["application_id"],
        chain_or_domain_id=scope["chain_or_domain_id"],
        economic_action_id=action_id,
        authorization_subject_id=subject,
        authorization_grant_id=grant,
        authorization_scope_id=auth_scope,
        authorization_nonce=auth_nonce,
        action_pre_state_root=action_pre_state,
        authorization_nullifier=nullifier,
    )
    observed_spend = _prefixed_hash(
        _plain_string(action, "authorization_grant_spend_nullifier")
    )
    if authorization.authorization_grant_spend_nullifier != observed_spend:
        raise SourceOpenedSpotV6VerificationError("authorization grant spend mismatch")
    for key in ("action_type_id", "action_authorization_binding", "action_semantics_hash", "effect_commitment"):
        _prefixed_hash(_plain_string(action, key))

    cell = _exact_mapping(execution.get("cell_write"), _CELL_KEYS, "execution cell write")
    if _prefixed_hash(_plain_string(cell, "economic_action_id")) != action_id:
        raise SourceOpenedSpotV6VerificationError("cell write action mismatch")
    cell_write = LedgerCellWriteV1(
        economic_action_id=action_id,
        cell_key=_prefixed_hash(_plain_string(cell, "cell_key")),
        pre_value_hash=_prefixed_hash_allow_zero(_plain_string(cell, "pre_value_hash")),
        post_value_hash=_prefixed_hash_allow_zero(_plain_string(cell, "post_value_hash")),
    )
    rows_value = execution.get("ordinary_asset_rows")
    if type(rows_value) is not list or len(rows_value) != 2:
        raise SourceOpenedSpotV6VerificationError("ordinary asset rows must contain exactly two rows")
    asset_rows: list[AssetEffectV1] = []
    asset_ids: set[str] = set()
    for index, item in enumerate(rows_value):
        row = _exact_mapping(item, _ASSET_KEYS, f"ordinary asset row {index}")
        if _prefixed_hash(_plain_string(row, "economic_action_id")) != action_id:
            raise SourceOpenedSpotV6VerificationError("ordinary asset row action mismatch")
        asset_id = _prefixed_hash(_plain_string(row, "asset_id"))
        debit = _decimal_u128(row, "debit_atoms")
        credit = _decimal_u128(row, "credit_atoms")
        if debit == 0 or debit != credit:
            raise SourceOpenedSpotV6VerificationError("ordinary asset row is not conserved")
        if asset_id in asset_ids:
            raise SourceOpenedSpotV6VerificationError("ordinary asset IDs must be distinct")
        asset_ids.add(asset_id)
        asset_rows.append(
            AssetEffectV1(
                kind=AssetEffectKindV1.ORDINARY_TRANSFER,
                economic_action_id=action_id,
                asset_id=asset_id,
                debit_atoms=debit,
                credit_atoms=credit,
                authorized_mint_atoms=0,
                authorized_burn_atoms=0,
            )
        )
    try:
        plan = build_settlement_effect_plan_v1(
            ProposedSettlementEffectPlanV1(
                application_id=scope["application_id"],
                chain_or_domain_id=scope["chain_or_domain_id"],
                epoch_id=journal.epoch_id,
                source_root_journal_hash=_prefixed(journal.semantic_journal_hash),
                public_policy_hash=_prefixed(journal.public_policy_hash),
                pre_state_root=scope["pre_state_root"],
                post_state_root=scope["post_state_root"],
                economic_action_ids=(action_id,),
                ledger_cell_writes=(cell_write,),
                asset_effects=tuple(asset_rows),
                authorization_consumptions=(),
                message_effects=(),
                carry_effects=(),
                reward_effects=(),
            )
        )
    except (TypeError, ValueError) as exc:
        raise SourceOpenedSpotV6VerificationError(
            "execution projection fails Python V1 plan validation"
        ) from exc
    return plan, consumed, (observed_spend,)


def _root_facts(
    certificate: _VerifiedSettlementEpochCertificateV1,
    plan: SettlementEffectPlanV1,
    policy: Mapping[str, Any],
) -> RecursiveStarkRootFacts:
    claims = (certificate.semantic_claim_hash, certificate.settlement_claim_hash)
    receipts = (certificate.settlement_receipt_id,)
    messages = tuple(row.message_id for row in plan.message_effects)
    return RecursiveStarkRootFacts(
        chain_id=_policy_str(policy, "chain_id"),
        epoch_id=certificate.epoch_id,
        proof_profile=_policy_str(policy, "proof_profile"),
        root_journal_hash=certificate.semantic_root_journal_hash,
        verifier_set_root=_prefixed_hash(_policy_str(policy, "verifier_set_root")),
        public_policy_hash=certificate.public_policy_hash,
        child_verification_claim_hashes=claims,
        child_verification_claims_root=recursive_child_verification_claims_root_v1(claims),
        accepted_receipt_ids=receipts,
        accepted_receipts_root=recursive_receipt_ids_root_v1(receipts),
        cross_shard_message_ids=messages,
        cross_shard_message_ids_root=recursive_message_ids_root_v1(messages),
    )


def _extract_replay_and_da_certificate(
    guest_input: bytes,
    effect_plan: bytes,
) -> tuple[bytes, bytes]:
    reader = _ByteReader(guest_input)
    if reader.u16() != 3:
        raise SourceOpenedSpotV6VerificationError("source-opened guest input version mismatch")
    base = reader.component(MAX_SOURCE_OPENED_SPOT_V6_GUEST_INPUT_BYTES)
    source = reader.component(MAX_SOURCE_OPENED_SPOT_V6_GUEST_INPUT_BYTES)
    reader.finished()
    base_reader = _ByteReader(base)
    if base_reader.u16() != 2:
        raise SourceOpenedSpotV6VerificationError("base settlement input version mismatch")
    proposal = base_reader.component(65_536)
    authorization = base_reader.read(104)
    witness = base_reader.component(8_192)
    certificate = base_reader.component(512)
    base_reader.finished()
    base_replay = b"".join(
        (
            (2).to_bytes(2, "big"),
            len(proposal).to_bytes(4, "big"),
            proposal,
            authorization,
            len(witness).to_bytes(4, "big"),
            witness,
            len(effect_plan).to_bytes(4, "big"),
            effect_plan,
        )
    )
    replay = b"".join(
        (
            (3).to_bytes(2, "big"),
            len(base_replay).to_bytes(4, "big"),
            base_replay,
            len(source).to_bytes(4, "big"),
            source,
        )
    )
    if len(replay) > 8 * 1024 * 1024:
        raise SourceOpenedSpotV6VerificationError("source-opened replay exceeds its bound")
    return replay, certificate


class _ByteReader:
    __slots__ = ("_offset", "_raw")

    def __init__(self, raw: bytes) -> None:
        self._raw = raw
        self._offset = 0

    def read(self, length: int) -> bytes:
        end = self._offset + length
        value = self._raw[self._offset : end]
        if len(value) != length:
            raise SourceOpenedSpotV6VerificationError("source-opened guest input is truncated")
        self._offset = end
        return value

    def u16(self) -> int:
        return int.from_bytes(self.read(2), "big")

    def u32(self) -> int:
        return int.from_bytes(self.read(4), "big")

    def component(self, maximum: int) -> bytes:
        length = self.u32()
        if not 1 <= length <= maximum:
            raise SourceOpenedSpotV6VerificationError("guest input component length is invalid")
        return self.read(length)

    def finished(self) -> None:
        if self._offset != len(self._raw):
            raise SourceOpenedSpotV6VerificationError("source-opened guest input has trailing bytes")


def _strict_policy_copy(policy: Mapping[str, Any]) -> dict[str, Any]:
    if not isinstance(policy, Mapping):
        raise TypeError("source-opened policy must be a mapping")
    required = _AUTHORITY_KEYS - {"schema", "executable_sha256", "executable_format"}
    if set(policy) != required:
        raise ValueError("source-opened policy schema mismatch")
    copied = json.loads(canonical_json_bytes(policy))
    if type(copied) is not dict:
        raise ValueError("source-opened policy must be an object")
    for key in (
        "application_id",
        "chain_or_domain_id",
        "public_policy_hash",
        "verifier_set_root",
        "governed_settlement_program_id",
        "governed_settlement_profile_id",
        "governed_settlement_manifest_root",
    ):
        _bare_hash(copied, key)
    for key in ("chain_id", "proof_profile"):
        _require_token(_policy_str(copied, key), f"policy.{key}")
    epoch = _policy_int(copied, "epoch_id")
    if not 0 <= epoch <= (1 << 64) - 1:
        raise ValueError("source-opened policy epoch is out of bounds")
    profile = _exact_mapping(
        copied.get("receipt_security_profile"),
        _RECEIPT_PROFILE_KEYS,
        "policy receipt_security_profile",
    )
    for key in _RECEIPT_PROFILE_KEYS:
        value = _plain_string(profile, key)
        if key in {"verifier_parameters", "control_id"}:
            _prefixed_hash(value)
        else:
            _require_token(value, f"receipt_security_profile.{key}")
    return copied


def _decode_canonical_json_object(raw: bytes, name: str) -> dict[str, Any]:
    try:
        value = json.loads(
            raw,
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise SourceOpenedSpotV6VerificationError(f"{name} must be strict JSON") from exc
    if type(value) is not dict:
        raise SourceOpenedSpotV6VerificationError(f"{name} must be one object")
    return value


def _exact_mapping(value: object, keys: frozenset[str], name: str) -> Mapping[str, Any]:
    if type(value) is not dict or set(value) != keys:
        raise SourceOpenedSpotV6VerificationError(f"{name} schema mismatch")
    return value


def _require_length_and_hash(
    value: bytes,
    fields: Mapping[str, Any],
    *,
    length_key: str,
    hash_key: str,
    name: str,
) -> None:
    if _strict_int(fields, length_key) != len(value):
        raise SourceOpenedSpotV6VerificationError(f"{name} byte count mismatch")
    if _bare_hash(fields, hash_key) != hashlib.sha256(value).hexdigest():
        raise SourceOpenedSpotV6VerificationError(f"{name} SHA-256 mismatch")


def _require_exact_input_bytes(value: bytes, *, maximum: int, name: str) -> None:
    if type(value) is not bytes:
        raise TypeError(f"{name} must be exactly bytes")
    if not value or len(value) > maximum:
        raise SourceOpenedSpotV6VerificationError(f"{name} byte length is out of bounds")


def _plain_string(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if type(value) is not str:
        raise SourceOpenedSpotV6VerificationError(f"{key} must be a string")
    return value


def _strict_int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if type(value) is not int:
        raise SourceOpenedSpotV6VerificationError(f"{key} must be an integer")
    if value < 0:
        raise SourceOpenedSpotV6VerificationError(f"{key} must be nonnegative")
    return value


def _decimal_u128(values: Mapping[str, Any], key: str) -> int:
    value = _plain_string(values, key)
    if not value or (len(value) > 1 and value.startswith("0")) or not value.isascii():
        raise SourceOpenedSpotV6VerificationError(f"{key} must be canonical decimal")
    if any(character not in "0123456789" for character in value):
        raise SourceOpenedSpotV6VerificationError(f"{key} must be canonical decimal")
    parsed = int(value)
    if parsed > (1 << 128) - 1:
        raise SourceOpenedSpotV6VerificationError(f"{key} exceeds u128")
    return parsed


def _hash_list(
    values: Mapping[str, Any],
    key: str,
    *,
    expected_length: int,
) -> tuple[str, ...]:
    value = values.get(key)
    if type(value) is not list or len(value) != expected_length:
        raise SourceOpenedSpotV6VerificationError(f"{key} length mismatch")
    result = tuple(_prefixed_hash(item) for item in value)
    if len(set(result)) != len(result):
        raise SourceOpenedSpotV6VerificationError(f"{key} must be unique")
    return result


def _bare_hash(values: Mapping[str, Any], key: str) -> str:
    value = _plain_string(values, key)
    _require_bare_hash(value, key)
    if value == "00" * 32:
        raise SourceOpenedSpotV6VerificationError(f"{key} must be nonzero")
    return value


def _require_bare_hash(value: object, name: str) -> None:
    if type(value) is not str or len(value) != 64:
        raise ValueError(f"{name} must be lowercase 32-byte hex")
    if any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be lowercase 32-byte hex")


def _prefixed(value: bytes) -> str:
    if type(value) is not bytes or len(value) != 32 or value == bytes(32):
        raise SourceOpenedSpotV6VerificationError("commitment must be nonzero 32 bytes")
    return "0x" + value.hex()


def _prefixed_hash(value: object) -> str:
    if type(value) is not str:
        raise SourceOpenedSpotV6VerificationError("hash must be a string")
    bare = value.removeprefix("0x")
    _require_bare_hash(bare, "hash")
    if bare == "00" * 32:
        raise SourceOpenedSpotV6VerificationError("hash must be nonzero")
    return "0x" + bare


def _prefixed_hash_allow_zero(value: object) -> str:
    if type(value) is not str:
        raise SourceOpenedSpotV6VerificationError("hash must be a string")
    bare = value.removeprefix("0x")
    _require_bare_hash(bare, "hash")
    return "0x" + bare


def _hex_bytes(values: Mapping[str, Any], key: str) -> bytes:
    value = _plain_string(values, key)
    if not value or len(value) % 2 or any(character not in "0123456789abcdef" for character in value):
        raise SourceOpenedSpotV6VerificationError(f"{key} must be exact lowercase hex")
    return bytes.fromhex(value)


def _policy_str(policy: Mapping[str, Any], key: str) -> str:
    value = policy.get(key)
    if type(value) is not str:
        raise SourceOpenedSpotV6VerificationError(f"policy {key} must be a string")
    return value


def _policy_int(policy: Mapping[str, Any], key: str) -> int:
    value = policy.get(key)
    if type(value) is not int or value < 0:
        raise SourceOpenedSpotV6VerificationError(f"policy {key} must be a nonnegative integer")
    return value


def _require_token(value: str, name: str) -> None:
    allowed = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-")
    if not value or len(value.encode("ascii", errors="strict")) > 128:
        raise ValueError(f"{name} token length is invalid")
    if any(character not in allowed for character in value):
        raise ValueError(f"{name} token characters are invalid")


def _reject_json_float(value: str) -> NoReturn:
    raise ValueError(f"floating-point JSON is forbidden: {value}")
