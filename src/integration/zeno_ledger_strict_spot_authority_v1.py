"""Private one-shot adapter for strict ZenoLedger Spot proof facts.

The verifier JSON is untrusted transport data. This adapter independently
recomposes the governed config, policy, manifest, registry, proof metadata,
header, and exact request expectations before executing one pinned process.
Only a fully matching result reaches the consumer-private mint.
"""

from __future__ import annotations

import base64
import binascii
import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Mapping, NoReturn, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    MAX_VERIFIER_STDOUT_BYTES,
    PinnedVerifierProcessError,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration.zeno_ledger_profile import (
    validate_zeno_ledger_profile_v0,
    zeno_ledger_profile_requires_proof_authority_v0,
)
from src.integration.zeno_ledger_proof_authority_consumer_v1 import (
    SPOT_AUTHORITY_RESULT_SCHEMA_V1,
    SPOT_PROOF_PROFILE_V1,
    GovernedProofAuthorityBindingV1,
    ProofAuthorityDecisionV1,
    ProofAuthorityRequirementV1,
    _mint_authenticated_strict_spot_observation_v1,
    make_proof_authority_requirement_v1,
    resolve_proof_authority_v1,
)
from src.integration.zeno_ledger_replay import (
    parse_replay_engine_config_v1,
    replay_engine_config_digest_v1,
)
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
)
from src.integration.zeno_ledger_verifier_registry_v0 import (
    VERIFIER_STATUS_ACTIVE_V0,
    validate_proof_metadata_against_verifier_registry_v0,
    validate_verifier_registry_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes

STRICT_SPOT_AUTHORITY_REQUEST_SCHEMA_V1 = "zenodex.zeno_ledger.risc0_spot_authority_verify.v1"
STRICT_SPOT_AUTHORITY_EXPECTATIONS_SCHEMA_V1 = (
    "zenodex.zeno_ledger.risc0_spot_authority_expectations.v1"
)
STRICT_SPOT_AUTHORITY_MANIFEST_SCHEMA_V1 = "zenodex.zeno_ledger.strict_spot_verifier_authority.v1"
STRICT_SPOT_AUTHORITY_SCOPE_V1 = "source_receipt_and_exact_outer_binding_v1"
STRICT_SPOT_RECEIPT_CODEC_V1 = "risc0_receipt_canonical_serde_json_depth128_v1"
STRICT_SPOT_TRANSACTION_BRIDGE_SCHEMA_V1 = "zenodex.zeno_ledger.spot_transaction_domain_bridge.v1"

MAX_STRICT_MANIFEST_BYTES = 1024 * 1024
MAX_STRICT_REQUEST_BYTES = 24 * 1024 * 1024
MAX_STRICT_JOURNAL_BYTES = 1024 * 1024
_MAX_U64 = (1 << 64) - 1

_TOKEN_CHARS = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:/-")
_MAX_AUTHORITY_TOKEN_UTF8_BYTES = 256
_BASE_REQUEST_KEYS = frozenset(
    {
        "state_hash",
        "proof",
        "block",
        "tau_state",
        "context",
        "trusted_route_price_interval_authority_policy_root",
    }
)
_MANIFEST_KEYS = frozenset(
    {
        "schema",
        "executable_sha256",
        "executable_format",
        "verifier_registry_id",
        "verifier_registry_entry_id",
        "program_id",
        "verifier_id",
        "expected_image_id",
        "receipt_codec",
        "receipt_kind",
        "receipt_verifier_parameters",
        "receipt_hashfn",
        "receipt_control_id",
        "public_policy_hash",
    }
)
_FACT_KEYS = frozenset(
    {
        "schema",
        "authority_scope",
        "authority_manifest_sha256",
        "verifier_registry_id",
        "verifier_registry_entry_id",
        "policy_id",
        "chain_id",
        "height",
        "valid_from_height",
        "valid_until_height",
        "proof_profile",
        "actual_image_id",
        "receipt_codec",
        "receipt_kind",
        "receipt_verifier_parameters",
        "receipt_hashfn",
        "receipt_control_id",
        "canonical_receipt_sha256",
        "canonical_journal_sha256",
        "canonical_journal_base64",
        "state_hash",
        "spot_pre_app_hash",
        "spot_post_app_hash",
        "spot_pre_nonce_root",
        "spot_post_nonce_root",
        "spot_ingress_commitment",
        "spot_accepted_receipts_root",
        "spot_tx_execution_order_commitment",
        "spot_route_price_intervals_root",
        "spot_route_price_interval_authority_root",
        "spot_route_price_interval_authority_policy_root",
        "spot_shared_pool_frontier_signature_certificates_root",
        "block_timestamp",
        "ledger_header_time_ms",
        "canonical_header_hash",
        "proof_metadata_hash",
        "proof_commitment",
        "ledger_pre_state_root",
        "ledger_post_state_root",
        "ledger_app_hash",
        "ledger_evidence_root",
        "ledger_body_root",
        "ledger_data_availability_root",
        "ledger_proof_journal_hash",
        "config_digest",
        "module_versions_digest",
        "public_policy_hash",
        "feature_suite_hash",
        "dependency_lock_hash",
        "toolchain_lock_hash",
        "transaction_domain_bridge",
        "block_timestamp_directly_committed_in_spot_journal",
        "chain_and_height_directly_committed_in_spot_journal",
        "spot_app_hash_equals_zeno_ledger_state_root_verified",
        "data_availability_verified",
        "proof_metadata_object_verified",
        "serialized_facts_are_opaque_capability",
        "governed_policy_registry_join_verified",
        "settlement_authority",
        "production_authority",
    }
)
_SPOT_ROOT_FIELDS = (
    "state_hash",
    "spot_pre_app_hash",
    "spot_post_app_hash",
    "spot_pre_nonce_root",
    "spot_post_nonce_root",
    "spot_ingress_commitment",
    "spot_accepted_receipts_root",
    "spot_tx_execution_order_commitment",
    "spot_route_price_intervals_root",
    "spot_route_price_interval_authority_root",
    "spot_route_price_interval_authority_policy_root",
    "spot_shared_pool_frontier_signature_certificates_root",
)
_STRICT_FALSE_FIELDS = (
    "block_timestamp_directly_committed_in_spot_journal",
    "chain_and_height_directly_committed_in_spot_journal",
    "spot_app_hash_equals_zeno_ledger_state_root_verified",
    "data_availability_verified",
    "proof_metadata_object_verified",
    "serialized_facts_are_opaque_capability",
    "governed_policy_registry_join_verified",
    "settlement_authority",
    "production_authority",
)


class StrictSpotAuthorityRejectReasonV1(str, Enum):
    MANIFEST_INVALID = "strict_spot_authority.manifest_invalid"
    CONFIG_INVALID = "strict_spot_authority.config_invalid"
    PROFILE_MISMATCH = "strict_spot_authority.profile_mismatch"
    HEADER_MISMATCH = "strict_spot_authority.header_mismatch"
    METADATA_MISMATCH = "strict_spot_authority.metadata_mismatch"
    REGISTRY_MISMATCH = "strict_spot_authority.registry_mismatch"
    REQUEST_INVALID = "strict_spot_authority.request_invalid"
    PROCESS_FAILED = "strict_spot_authority.process_failed"
    RESPONSE_INVALID = "strict_spot_authority.response_invalid"
    RESPONSE_MISMATCH = "strict_spot_authority.response_mismatch"
    EXECUTABLE_POLICY_MISMATCH = "strict_spot_authority.executable_policy_mismatch"


class StrictSpotAuthorityError(ValueError):
    def __init__(self, reason: StrictSpotAuthorityRejectReasonV1, detail: str) -> None:
        self.reason = reason
        super().__init__(f"{reason.value}: {detail}")


@dataclass(frozen=True, slots=True)
class StrictSpotAuthorityManifestV1:
    schema: str
    executable_sha256: str
    executable_format: VerifierExecutableFormatV1
    verifier_registry_id: str
    verifier_registry_entry_id: str
    program_id: str
    verifier_id: str
    expected_image_id: str
    receipt_codec: str
    receipt_kind: str
    receipt_verifier_parameters: str
    receipt_hashfn: str | None
    receipt_control_id: str | None
    public_policy_hash: str


def strict_spot_authority_manifest_bytes_v1(
    *,
    executable_sha256: str,
    executable_format: VerifierExecutableFormatV1,
    verifier_registry_id: str,
    verifier_registry_entry_id: str,
    program_id: str,
    verifier_id: str,
    expected_image_id: str,
    receipt_kind: str,
    receipt_verifier_parameters: str,
    receipt_hashfn: str | None,
    receipt_control_id: str | None,
    public_policy_hash: str,
) -> bytes:
    """Build the exact manifest whose SHA-256 is committed by config V1."""

    document = {
        "schema": STRICT_SPOT_AUTHORITY_MANIFEST_SCHEMA_V1,
        "executable_sha256": executable_sha256,
        "executable_format": executable_format.value,
        "verifier_registry_id": verifier_registry_id,
        "verifier_registry_entry_id": verifier_registry_entry_id,
        "program_id": program_id,
        "verifier_id": verifier_id,
        "expected_image_id": expected_image_id,
        "receipt_codec": STRICT_SPOT_RECEIPT_CODEC_V1,
        "receipt_kind": receipt_kind,
        "receipt_verifier_parameters": receipt_verifier_parameters,
        "receipt_hashfn": receipt_hashfn,
        "receipt_control_id": receipt_control_id,
        "public_policy_hash": public_policy_hash,
    }
    raw = canonical_json_bytes(document)
    if len(raw) > MAX_STRICT_MANIFEST_BYTES:
        raise ValueError("strict Spot authority manifest exceeds byte limit")
    _parse_manifest(raw, expected_sha256=hashlib.sha256(raw).hexdigest())
    return raw


@final
@dataclass(frozen=True)
class PinnedStrictSpotAuthorityVerifierV1:
    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    _manifest: StrictSpotAuthorityManifestV1 = field(init=False, repr=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedStrictSpotAuthorityVerifierV1 cannot be subclassed")

    def __post_init__(self) -> None:
        if not self.executable.is_absolute():
            raise ValueError("strict Spot verifier executable must be an absolute path")
        _require_bare_sha256(
            self.authority_manifest_sha256,
            name="authority_manifest_sha256",
        )
        if not isinstance(self.timeout_seconds, int) or isinstance(self.timeout_seconds, bool):
            raise TypeError("timeout_seconds must be an int")
        if self.timeout_seconds <= 0 or self.timeout_seconds > 300:
            raise ValueError("timeout_seconds must be in 1..300")
        if (
            not isinstance(self.max_address_space_bytes, int)
            or isinstance(self.max_address_space_bytes, bool)
            or self.max_address_space_bytes < 256 * 1024 * 1024
        ):
            raise ValueError("max_address_space_bytes is too small")
        if (
            not isinstance(self.max_stack_bytes, int)
            or isinstance(self.max_stack_bytes, bool)
            or self.max_stack_bytes < 1024 * 1024
        ):
            raise ValueError("max_stack_bytes is too small")
        manifest = _parse_manifest(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        object.__setattr__(self, "_manifest", manifest)

    def verify_and_resolve(
        self,
        *,
        spot_request_payload: Mapping[str, Any],
        proof_metadata: Mapping[str, Any],
        header: Mapping[str, Any],
        checkpoint: Mapping[str, Any],
        replay_config: Mapping[str, Any],
        profile: Mapping[str, Any],
        verifier_registry: Mapping[str, Any],
    ) -> ProofAuthorityDecisionV1:
        """Execute one pinned verifier and resolve one exact governed height."""

        if self._manifest.executable_format is not VerifierExecutableFormatV1.STATIC_ELF_X86_64:
            raise StrictSpotAuthorityError(
                StrictSpotAuthorityRejectReasonV1.EXECUTABLE_POLICY_MISMATCH,
                "authority-bearing strict Spot verification requires a static ELF",
            )
        prepared = _prepare_request(
            manifest=self._manifest,
            authority_manifest_sha256=self.authority_manifest_sha256,
            spot_request_payload=spot_request_payload,
            proof_metadata=proof_metadata,
            header=header,
            checkpoint=checkpoint,
            replay_config=replay_config,
            profile=profile,
            verifier_registry=verifier_registry,
        )
        try:
            stdout = execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self._manifest.executable_sha256,
                executable_format=self._manifest.executable_format,
                request_bytes=prepared.request_bytes,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
            )
        except PinnedVerifierProcessError as exc:
            raise StrictSpotAuthorityError(
                StrictSpotAuthorityRejectReasonV1.PROCESS_FAILED,
                "pinned strict Spot verifier process rejected execution",
            ) from exc
        facts = _parse_and_bind_response(stdout, prepared=prepared, manifest=self._manifest)
        # The strict result explicitly says that Spot app hashes have not been
        # proven equal to ZenoLedger state roots.  Verification therefore
        # advances evidence while authority remains pending.
        observation = _mint_authenticated_strict_spot_observation_v1(
            policy_id=prepared.policy.policy_id,
            chain_id=prepared.policy.chain_id,
            height=prepared.height,
            replay_config_digest=prepared.config_digest,
            authority_manifest_sha256=self.authority_manifest_sha256,
            verifier_registry_id=prepared.policy.verifier_registry_id,
            verifier_registry_entry_id=prepared.policy.verifier_registry_entry_id,
            strict_result_schema=str(facts["schema"]),
        )
        return resolve_proof_authority_v1(
            requirement=prepared.requirement,
            governed_binding=prepared.policy,
            authenticated_result=observation,
        )


@dataclass(frozen=True, slots=True)
class _PreparedRequestV1:
    request_bytes: bytes
    request: dict[str, Any]
    proof_metadata: dict[str, Any]
    header: dict[str, Any]
    policy: GovernedProofAuthorityBindingV1
    requirement: ProofAuthorityRequirementV1
    config_digest: str
    height: int
    transaction_batch_sha256: str


@dataclass(frozen=True, slots=True)
class _GovernedRequestContextV1:
    metadata: dict[str, Any]
    header: dict[str, Any]
    canonical_config: dict[str, Any]
    policy: GovernedProofAuthorityBindingV1
    requirement: ProofAuthorityRequirementV1
    config_digest: str
    height: int
    header_time_ms: int


@dataclass(frozen=True, slots=True)
class _SpotPayloadContextV1:
    payload: dict[str, Any]
    state_hash: str
    proof_commitment: str
    block_timestamp: int
    transaction_batch_sha256: str


def _prepare_request(
    *,
    manifest: StrictSpotAuthorityManifestV1,
    authority_manifest_sha256: str,
    spot_request_payload: Mapping[str, Any],
    proof_metadata: Mapping[str, Any],
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    replay_config: Mapping[str, Any],
    profile: Mapping[str, Any],
    verifier_registry: Mapping[str, Any],
) -> _PreparedRequestV1:
    try:
        governed = _validate_governed_request_context(
            manifest=manifest,
            authority_manifest_sha256=authority_manifest_sha256,
            proof_metadata=proof_metadata,
            header=header,
            checkpoint=checkpoint,
            replay_config=replay_config,
            profile=profile,
            verifier_registry=verifier_registry,
        )
        spot = _validate_spot_payload(
            spot_request_payload,
            metadata=governed.metadata,
            header=governed.header,
            header_time_ms=governed.header_time_ms,
        )
        expectations = _authority_expectations(
            manifest=manifest,
            authority_manifest_sha256=authority_manifest_sha256,
            governed=governed,
            spot=spot,
        )
        request = {
            "schema": STRICT_SPOT_AUTHORITY_REQUEST_SCHEMA_V1,
            "schema_version": 1,
            **spot.payload,
            "state_hash": spot.state_hash,
            "ledger_header": governed.header,
            "replay_config": governed.canonical_config,
            "authority_expectations": expectations,
        }
        request_bytes = canonical_json_bytes(request)
        if len(request_bytes) > MAX_STRICT_REQUEST_BYTES:
            raise ValueError("strict Spot authority request exceeds byte limit")
        return _PreparedRequestV1(
            request_bytes=request_bytes,
            request=request,
            proof_metadata=governed.metadata,
            header=governed.header,
            policy=governed.policy,
            requirement=governed.requirement,
            config_digest=governed.config_digest,
            height=governed.height,
            transaction_batch_sha256=spot.transaction_batch_sha256,
        )
    except StrictSpotAuthorityError:
        raise
    except (KeyError, TypeError, ValueError) as exc:
        raise StrictSpotAuthorityError(
            _preparation_reason(exc),
            "strict Spot authority inputs do not form one governed request",
        ) from exc


def _validate_governed_request_context(
    *,
    manifest: StrictSpotAuthorityManifestV1,
    authority_manifest_sha256: str,
    proof_metadata: Mapping[str, Any],
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    replay_config: Mapping[str, Any],
    profile: Mapping[str, Any],
    verifier_registry: Mapping[str, Any],
) -> _GovernedRequestContextV1:
    metadata = dict(proof_metadata)
    header_obj = dict(header)
    profile_obj = dict(profile)
    registry_obj = dict(verifier_registry)
    config, policy, canonical_config = parse_replay_engine_config_v1(replay_config)
    config_digest = replay_engine_config_digest_v1(canonical_config)
    validate_header_v0(header_obj)
    validate_checkpoint_header_binding_v0(dict(checkpoint), header_obj)
    validate_proof_metadata_header_binding_v0(metadata, header_obj)
    validate_zeno_ledger_profile_v0(profile_obj)
    if not zeno_ledger_profile_requires_proof_authority_v0(profile_obj):
        raise ValueError("profile does not require proof authority")
    if profile_obj["chain_id"] != config.chain_id or header_obj["chain_id"] != config.chain_id:
        raise ValueError("profile/header/config chain mismatch")
    if config_digest not in profile_obj["accepted_config_digests"]:
        raise ValueError("profile does not admit config V1 digest")
    if header_obj["config_digest"] != config_digest:
        raise ValueError("header does not bind config V1 digest")
    if policy.authority_manifest_sha256 != authority_manifest_sha256:
        raise ValueError("policy authority manifest mismatch")
    _bind_manifest_policy(manifest=manifest, policy=policy)
    validate_verifier_registry_v0(registry_obj)
    validate_proof_metadata_against_verifier_registry_v0(
        proof_metadata=metadata,
        registry=registry_obj,
    )
    _bind_registry(manifest=manifest, policy=policy, metadata=metadata, registry=registry_obj)
    height = _require_height(header_obj["height"], name="header.height")
    if height < policy.valid_from_height or height > policy.valid_until_height:
        raise ValueError("header height is outside proof-authority policy validity")
    requirement = make_proof_authority_requirement_v1(
        profile=profile_obj,
        replay_config_digest=config_digest,
        expected_policy_id=policy.policy_id,
        from_height=height,
        to_height=height,
    )
    return _GovernedRequestContextV1(
        metadata=metadata,
        header=header_obj,
        canonical_config=canonical_config,
        policy=policy,
        requirement=requirement,
        config_digest=config_digest,
        height=height,
        header_time_ms=_require_height(header_obj["time_ms"], name="header.time_ms"),
    )


def _validate_spot_payload(
    spot_request_payload: Mapping[str, Any],
    *,
    metadata: Mapping[str, Any],
    header: Mapping[str, Any],
    header_time_ms: int,
) -> _SpotPayloadContextV1:
    payload = dict(spot_request_payload)
    if set(payload) != _BASE_REQUEST_KEYS:
        raise ValueError("strict Spot request payload keys mismatch")
    proof = _require_mapping(payload["proof"], name="spot_request_payload.proof")
    proof_commitment = hash_v0("risc0_tau_state_proof_envelope_v0", dict(proof))
    if metadata["proof_commitment"] != proof_commitment:
        raise ValueError("proof metadata commitment does not match strict proof envelope")
    block = _require_mapping(payload["block"], name="spot_request_payload.block")
    if set(block) != {"header", "transactions"}:
        raise ValueError("spot request block keys mismatch")
    block_header = _require_mapping(block["header"], name="spot_request_payload.block.header")
    if set(block_header) != {"timestamp"}:
        raise ValueError("spot request block header keys mismatch")
    block_timestamp = _require_height(
        block_header["timestamp"],
        name="spot_request_payload.block.header.timestamp",
    )
    if block_timestamp != header_time_ms // 1_000:
        raise ValueError("Spot block timestamp does not match ledger header")
    transactions = block["transactions"]
    if not isinstance(transactions, list):
        raise TypeError("spot request transactions must be a list")
    if compute_tx_root_v0(transactions) != header["tx_root"]:
        raise ValueError("Spot transaction array does not match ledger tx_root")
    return _SpotPayloadContextV1(
        payload=payload,
        state_hash=_require_root(payload["state_hash"], name="spot_request_payload.state_hash"),
        proof_commitment=proof_commitment,
        block_timestamp=block_timestamp,
        transaction_batch_sha256=hashlib.sha256(canonical_json_bytes(transactions)).hexdigest(),
    )


def _authority_expectations(
    *,
    manifest: StrictSpotAuthorityManifestV1,
    authority_manifest_sha256: str,
    governed: _GovernedRequestContextV1,
    spot: _SpotPayloadContextV1,
) -> dict[str, Any]:
    return {
        "schema": STRICT_SPOT_AUTHORITY_EXPECTATIONS_SCHEMA_V1,
        "authority_manifest_sha256": authority_manifest_sha256,
        "verifier_registry_id": governed.policy.verifier_registry_id,
        "verifier_registry_entry_id": governed.policy.verifier_registry_entry_id,
        "strict_result_schema": governed.policy.strict_result_schema,
        "policy_id": governed.policy.policy_id,
        "chain_id": governed.policy.chain_id,
        "height": governed.height,
        "valid_from_height": governed.policy.valid_from_height,
        "valid_until_height": governed.policy.valid_until_height,
        "proof_profile": governed.policy.proof_profile,
        "expected_image_id": manifest.expected_image_id,
        "receipt_codec": manifest.receipt_codec,
        "receipt_kind": manifest.receipt_kind,
        "receipt_verifier_parameters": manifest.receipt_verifier_parameters,
        "receipt_hashfn": manifest.receipt_hashfn,
        "receipt_control_id": manifest.receipt_control_id,
        "canonical_header_hash": canonical_header_hash_v0(governed.header),
        "proof_metadata_hash": proof_metadata_hash_v0(governed.metadata),
        "proof_commitment": spot.proof_commitment,
        "config_digest": governed.config_digest,
        "module_versions_digest": governed.header["module_versions_digest"],
        "data_availability_root": governed.header["data_availability_root"],
        "public_policy_hash": manifest.public_policy_hash,
        "feature_suite_hash": governed.metadata["feature_suite_hash"],
        "dependency_lock_hash": governed.metadata["dependency_lock_hash"],
        "toolchain_lock_hash": governed.metadata["toolchain_lock_hash"],
        "block_timestamp": spot.block_timestamp,
    }


def _parse_and_bind_response(
    raw: bytes,
    *,
    prepared: _PreparedRequestV1,
    manifest: StrictSpotAuthorityManifestV1,
) -> dict[str, Any]:
    try:
        response = _parse_canonical_json_object(
            raw,
            max_bytes=MAX_VERIFIER_STDOUT_BYTES,
            name="strict Spot verifier response",
        )
        if set(response) != {
            "schema",
            "schema_version",
            "ok",
            "authenticated_spot_proof_facts",
        }:
            raise ValueError("strict Spot verifier response keys mismatch")
        if response["schema"] != SPOT_AUTHORITY_RESULT_SCHEMA_V1:
            raise ValueError("strict Spot verifier response schema mismatch")
        if response["schema_version"] != 1 or response["ok"] is not True:
            raise ValueError("strict Spot verifier did not return accepted V1 facts")
        facts = dict(
            _require_mapping(
                response["authenticated_spot_proof_facts"],
                name="authenticated_spot_proof_facts",
            )
        )
        if set(facts) != _FACT_KEYS:
            raise ValueError("strict Spot fact keys mismatch")
        _bind_fact_identities(facts=facts, prepared=prepared, manifest=manifest)
        _validate_journal_and_transaction_bridge(facts=facts, prepared=prepared)
        for field_name in _SPOT_ROOT_FIELDS:
            _require_root(facts[field_name], name=f"facts.{field_name}")
        for field_name in _STRICT_FALSE_FIELDS:
            if facts[field_name] is not False:
                raise ValueError(f"strict Spot non-claim {field_name} must remain false")
        return facts
    except (KeyError, TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StrictSpotAuthorityError(
            StrictSpotAuthorityRejectReasonV1.RESPONSE_MISMATCH,
            "strict Spot verifier response does not match host-recomposed authority",
        ) from exc


def _bind_fact_identities(
    *,
    facts: Mapping[str, Any],
    prepared: _PreparedRequestV1,
    manifest: StrictSpotAuthorityManifestV1,
) -> None:
    expectations = prepared.request["authority_expectations"]
    expected = {
        "schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
        "authority_scope": STRICT_SPOT_AUTHORITY_SCOPE_V1,
        "authority_manifest_sha256": expectations["authority_manifest_sha256"],
        "verifier_registry_id": expectations["verifier_registry_id"],
        "verifier_registry_entry_id": expectations["verifier_registry_entry_id"],
        "policy_id": expectations["policy_id"],
        "chain_id": expectations["chain_id"],
        "height": expectations["height"],
        "valid_from_height": expectations["valid_from_height"],
        "valid_until_height": expectations["valid_until_height"],
        "proof_profile": expectations["proof_profile"],
        "actual_image_id": manifest.expected_image_id,
        "receipt_codec": manifest.receipt_codec,
        "receipt_kind": manifest.receipt_kind,
        "receipt_verifier_parameters": manifest.receipt_verifier_parameters,
        "receipt_hashfn": manifest.receipt_hashfn,
        "receipt_control_id": manifest.receipt_control_id,
        "state_hash": prepared.request["state_hash"],
        "block_timestamp": expectations["block_timestamp"],
        "ledger_header_time_ms": prepared.header["time_ms"],
        "canonical_header_hash": expectations["canonical_header_hash"],
        "proof_metadata_hash": expectations["proof_metadata_hash"],
        "proof_commitment": expectations["proof_commitment"],
        "ledger_pre_state_root": prepared.header["pre_state_root"],
        "ledger_post_state_root": prepared.header["post_state_root"],
        "ledger_app_hash": prepared.header["app_hash"],
        "ledger_evidence_root": prepared.header["evidence_root"],
        "ledger_body_root": prepared.header["body_root"],
        "ledger_data_availability_root": prepared.header["data_availability_root"],
        "ledger_proof_journal_hash": prepared.header["proof_journal_hash"],
        "config_digest": prepared.config_digest,
        "module_versions_digest": prepared.header["module_versions_digest"],
        "public_policy_hash": manifest.public_policy_hash,
        "feature_suite_hash": prepared.proof_metadata["feature_suite_hash"],
        "dependency_lock_hash": prepared.proof_metadata["dependency_lock_hash"],
        "toolchain_lock_hash": prepared.proof_metadata["toolchain_lock_hash"],
    }
    for key, value in expected.items():
        if facts[key] != value:
            raise ValueError(f"strict Spot fact {key} mismatch")


def _validate_journal_and_transaction_bridge(
    *,
    facts: Mapping[str, Any],
    prepared: _PreparedRequestV1,
) -> None:
    _require_bare_sha256(facts["canonical_receipt_sha256"], name="canonical_receipt_sha256")
    journal_sha256 = _require_bare_sha256(
        facts["canonical_journal_sha256"],
        name="canonical_journal_sha256",
    )
    journal_b64 = facts["canonical_journal_base64"]
    if not isinstance(journal_b64, str) or not journal_b64:
        raise ValueError("canonical_journal_base64 must be a non-empty string")
    try:
        journal = base64.b64decode(journal_b64, validate=True)
    except (ValueError, binascii.Error) as exc:
        raise ValueError("canonical journal is not valid base64") from exc
    if base64.b64encode(journal).decode("ascii") != journal_b64:
        raise ValueError("canonical journal base64 is not canonical")
    if not journal or len(journal) > MAX_STRICT_JOURNAL_BYTES:
        raise ValueError("canonical journal byte length is invalid")
    if hashlib.sha256(journal).hexdigest() != journal_sha256:
        raise ValueError("canonical journal SHA-256 mismatch")
    if prepared.proof_metadata["journal_hash"] != "0x" + journal_sha256:
        raise ValueError("proof metadata does not bind canonical journal SHA-256")
    bridge = dict(_require_mapping(facts["transaction_domain_bridge"], name="transaction bridge"))
    if set(bridge) != {
        "schema",
        "tx_count",
        "canonical_transaction_batch_sha256",
        "spot_txs_commitment",
        "zeno_ledger_tx_root",
        "roots_are_domain_distinct",
    }:
        raise ValueError("transaction bridge keys mismatch")
    transactions = prepared.request["block"]["transactions"]
    if bridge["schema"] != STRICT_SPOT_TRANSACTION_BRIDGE_SCHEMA_V1:
        raise ValueError("transaction bridge schema mismatch")
    if bridge["tx_count"] != len(transactions):
        raise ValueError("transaction bridge count mismatch")
    if bridge["canonical_transaction_batch_sha256"] != prepared.transaction_batch_sha256:
        raise ValueError("transaction batch SHA-256 mismatch")
    if bridge["zeno_ledger_tx_root"] != prepared.header["tx_root"]:
        raise ValueError("transaction bridge ledger root mismatch")
    _require_root(bridge["spot_txs_commitment"], name="spot_txs_commitment")
    if bridge["roots_are_domain_distinct"] is not True:
        raise ValueError("transaction bridge domain distinction must be true")


def _bind_manifest_policy(
    *,
    manifest: StrictSpotAuthorityManifestV1,
    policy: GovernedProofAuthorityBindingV1,
) -> None:
    if (
        manifest.verifier_registry_id != policy.verifier_registry_id
        or manifest.verifier_registry_entry_id != policy.verifier_registry_entry_id
    ):
        raise ValueError("manifest registry identity does not match governed policy")
    if policy.strict_result_schema != SPOT_AUTHORITY_RESULT_SCHEMA_V1:
        raise ValueError("governed strict result schema mismatch")
    if policy.proof_profile != SPOT_PROOF_PROFILE_V1:
        raise ValueError("governed strict proof profile mismatch")


def _bind_registry(
    *,
    manifest: StrictSpotAuthorityManifestV1,
    policy: GovernedProofAuthorityBindingV1,
    metadata: Mapping[str, Any],
    registry: Mapping[str, Any],
) -> None:
    if registry.get("registry_id") != policy.verifier_registry_id:
        raise ValueError("verifier registry ID does not match governed policy")
    matching = [
        entry
        for entry in registry["entries"]
        if entry["entry_id"] == policy.verifier_registry_entry_id
    ]
    if len(matching) != 1:
        raise ValueError("governed verifier registry entry is not unique")
    entry = matching[0]
    if (
        entry["status"] != VERIFIER_STATUS_ACTIVE_V0
        or entry["program_id"] != manifest.program_id
        or entry["verifier_id"] != manifest.verifier_id
        or metadata["program_id"] != manifest.program_id
        or metadata["verifier_id"] != manifest.verifier_id
    ):
        raise ValueError("manifest, registry, and proof metadata identity mismatch")


def _parse_manifest(raw: bytes, *, expected_sha256: str) -> StrictSpotAuthorityManifestV1:
    try:
        _require_bare_sha256(expected_sha256, name="expected manifest SHA-256")
        document = _parse_canonical_json_object(
            raw,
            max_bytes=MAX_STRICT_MANIFEST_BYTES,
            name="strict Spot authority manifest",
        )
        if hashlib.sha256(raw).hexdigest() != expected_sha256:
            raise ValueError("strict Spot authority manifest SHA-256 mismatch")
        if set(document) != _MANIFEST_KEYS:
            raise ValueError("strict Spot authority manifest keys mismatch")
        if document["schema"] != STRICT_SPOT_AUTHORITY_MANIFEST_SCHEMA_V1:
            raise ValueError("strict Spot authority manifest schema mismatch")
        if document["receipt_codec"] != STRICT_SPOT_RECEIPT_CODEC_V1:
            raise ValueError("strict Spot receipt codec mismatch")
        return StrictSpotAuthorityManifestV1(
            schema=str(document["schema"]),
            executable_sha256=_require_bare_sha256(
                document["executable_sha256"],
                name="executable_sha256",
            ),
            executable_format=VerifierExecutableFormatV1(document["executable_format"]),
            verifier_registry_id=_require_root(
                document["verifier_registry_id"],
                name="verifier_registry_id",
            ),
            verifier_registry_entry_id=_require_root(
                document["verifier_registry_entry_id"],
                name="verifier_registry_entry_id",
            ),
            program_id=_require_token(document["program_id"], name="program_id"),
            verifier_id=_require_token(document["verifier_id"], name="verifier_id"),
            expected_image_id=_require_root(
                document["expected_image_id"],
                name="expected_image_id",
            ),
            receipt_codec=str(document["receipt_codec"]),
            receipt_kind=_require_token(document["receipt_kind"], name="receipt_kind"),
            receipt_verifier_parameters=_require_bounded_string(
                document["receipt_verifier_parameters"],
                name="receipt_verifier_parameters",
            ),
            receipt_hashfn=_require_optional_bounded_string(
                document["receipt_hashfn"],
                name="receipt_hashfn",
            ),
            receipt_control_id=_require_optional_bounded_string(
                document["receipt_control_id"],
                name="receipt_control_id",
            ),
            public_policy_hash=_require_root(
                document["public_policy_hash"],
                name="public_policy_hash",
            ),
        )
    except (KeyError, TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StrictSpotAuthorityError(
            StrictSpotAuthorityRejectReasonV1.MANIFEST_INVALID,
            "strict Spot authority manifest is invalid",
        ) from exc


def _parse_canonical_json_object(raw: bytes, *, max_bytes: int, name: str) -> dict[str, Any]:
    if not isinstance(raw, bytes) or not raw or len(raw) > max_bytes:
        raise ValueError(f"{name} byte length is invalid")
    value = json.loads(
        raw.decode("utf-8"),
        object_pairs_hook=_reject_duplicate_keys,
        parse_float=_reject_float,
        parse_constant=_reject_constant,
    )
    if not isinstance(value, dict):
        raise ValueError(f"{name} must decode to an object")
    if canonical_json_bytes(value) != raw:
        raise ValueError(f"{name} must use canonical JSON bytes")
    return value


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(_value: str) -> NoReturn:
    raise ValueError("floating-point JSON numbers are forbidden")


def _reject_constant(_value: str) -> NoReturn:
    raise ValueError("non-finite JSON numbers are forbidden")


def _preparation_reason(exc: Exception) -> StrictSpotAuthorityRejectReasonV1:
    message = str(exc)
    if "manifest" in message:
        return StrictSpotAuthorityRejectReasonV1.MANIFEST_INVALID
    if "config" in message or "policy" in message:
        return StrictSpotAuthorityRejectReasonV1.CONFIG_INVALID
    if "profile" in message:
        return StrictSpotAuthorityRejectReasonV1.PROFILE_MISMATCH
    if "metadata" in message or "proof commitment" in message:
        return StrictSpotAuthorityRejectReasonV1.METADATA_MISMATCH
    if "header" in message or "checkpoint" in message:
        return StrictSpotAuthorityRejectReasonV1.HEADER_MISMATCH
    if "registry" in message:
        return StrictSpotAuthorityRejectReasonV1.REGISTRY_MISMATCH
    return StrictSpotAuthorityRejectReasonV1.REQUEST_INVALID


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_token(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    if len(value.encode("utf-8")) > _MAX_AUTHORITY_TOKEN_UTF8_BYTES:
        raise ValueError(
            f"{name} must be at most {_MAX_AUTHORITY_TOKEN_UTF8_BYTES} UTF-8 bytes"
        )
    text = value
    if any(char not in _TOKEN_CHARS for char in text):
        raise ValueError(f"{name} contains unsupported characters")
    return text


def _require_bounded_string(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value or len(value.encode("utf-8")) > 512:
        raise ValueError(f"{name} must be a non-empty bounded string")
    return value


def _require_optional_bounded_string(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_bounded_string(value, name=name)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_bare_sha256(value: object, *, name: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(char not in "0123456789abcdef" for char in value)
    ):
        raise ValueError(f"{name} must be lowercase 64-character SHA-256 hex")
    return value


def _require_height(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > _MAX_U64:
        raise ValueError(f"{name} must be a u64")
    return value
