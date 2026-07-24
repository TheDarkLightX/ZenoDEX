"""Canonical authority-neutral execution manifest for bounded Spot V7.

The manifest binds the exact schema/profile identifiers and byte identities
needed by the proof verifier, checkpoint-finality checker, Firecracker runtime,
and root supervisor.  One release candidate inventories the exact manifest
bytes.  This module checks that inventory relationship and all mirrored
candidate fields without selecting the candidate, opening component artifacts,
executing code, or minting release/runtime/settlement authority.
"""

from __future__ import annotations

import hashlib
import json
from types import MappingProxyType
from typing import Any, Final, NoReturn, SupportsIndex, cast, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    VerifierExecutableFormatV1,
)
from src.integration._zrpf_spot_v7_checkpoint_finality_checker_codec import (
    CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1,
    CHECKPOINT_FINALITY_CHECKER_REQUEST_SCHEMA_V1,
    CHECKPOINT_FINALITY_CHECKER_RESPONSE_SCHEMA_V1,
)
from src.integration.zrpf_settlement_verifier_adapter import (
    SETTLEMENT_AUTHORITY_MANIFEST_SCHEMA_V1,
)
from src.integration.zrpf_spot_v7_checkpoint_finality_checker_adapter import (
    CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1,
)
from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1 as _AUTHORITY_INPUT_PROFILE_BYTES_V1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 import (
    ROOT_SUPERVISOR_CANDIDATE_CONTRACT_SCHEMA_V1,
    ROOT_SUPERVISOR_CANDIDATE_CONTRACT_STATUS_V1,
)
from tools.zrpf_spot_v7_firecracker_runtime_manifest import (
    SPOT_V7_RUNTIME_MANIFEST_SCHEMA_V1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1 as _RUNTIME_PROFILE_BYTES_V1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1,
    SPOT_V7_RELEASE_PROFILE_V1,
    SpotV7ReleaseCandidateRejectV1,
    parse_exact_spot_v7_release_candidate_manifest_v1,
)

EXECUTION_AUTHORITY_MANIFEST_SCHEMA_V1: Final = (
    "zenodex/zrpf_spot_v7_execution_authority_manifest/v1"
)
EXECUTION_AUTHORITY_MANIFEST_STATUS_V1: Final = "candidate_bound_execution_identity_authority_false"
SPOT_V7_AUTHORITY_INPUT_PROFILE_SHA256_V1: Final = _AUTHORITY_INPUT_PROFILE_BYTES_V1.hex()

MAX_EXECUTION_AUTHORITY_MANIFEST_BYTES_V1: Final = 64 * 1_024
MAX_EXECUTION_AUTHORITY_MANIFEST_JSON_DEPTH_V1: Final = 3
MAX_SCOPE_TEXT_CHARS_V1: Final = 96

FIRECRACKER_REPLAY_PROFILE_SCHEMA_V1: Final = "zenodex/zrpf_v3_firecracker_replay_profile/v1"
RUNTIME_ARTIFACT_MANIFEST_SCHEMA_V2: Final = "zenodex/zrpf_firecracker_runtime_artifact_manifest/v2"
SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_SCHEMA_V1: Final = (
    "zenodex/zrpf_spot_settlement_v7_verified_output/v1"
)
SPOT_SETTLEMENT_V7_RECEIPT_PROFILE_ID_V1: Final = "risc0_succinct_poseidon2_resolve_3_0_5_v1"

EXPECTED_INTERFACE_IDENTITIES_V1: Final = MappingProxyType(
    {
        "checkpoint_finality_checker_authority_manifest_schema": (
            CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1
        ),
        "checkpoint_finality_checker_protocol_version": (
            CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1
        ),
        "checkpoint_finality_checker_request_schema": (
            CHECKPOINT_FINALITY_CHECKER_REQUEST_SCHEMA_V1
        ),
        "checkpoint_finality_checker_response_schema": (
            CHECKPOINT_FINALITY_CHECKER_RESPONSE_SCHEMA_V1
        ),
        "firecracker_authority_input_profile_sha256": (_AUTHORITY_INPUT_PROFILE_BYTES_V1.hex()),
        "firecracker_replay_profile_schema": FIRECRACKER_REPLAY_PROFILE_SCHEMA_V1,
        "firecracker_runtime_manifest_schema": SPOT_V7_RUNTIME_MANIFEST_SCHEMA_V1,
        "firecracker_runtime_profile_sha256": _RUNTIME_PROFILE_BYTES_V1.hex(),
        "proof_verifier_authority_manifest_schema": (SETTLEMENT_AUTHORITY_MANIFEST_SCHEMA_V1),
        "proof_verifier_output_schema": SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_SCHEMA_V1,
        "proof_verifier_receipt_profile_id": (SPOT_SETTLEMENT_V7_RECEIPT_PROFILE_ID_V1),
        "root_supervisor_contract_schema": (ROOT_SUPERVISOR_CANDIDATE_CONTRACT_SCHEMA_V1),
        "root_supervisor_contract_status": (ROOT_SUPERVISOR_CANDIDATE_CONTRACT_STATUS_V1),
        "runtime_artifact_manifest_schema": RUNTIME_ARTIFACT_MANIFEST_SCHEMA_V2,
    }
)

EXPECTED_COMPONENT_CODECS_V1: Final = MappingProxyType(
    {
        "authority_input_profile": "canonical_binary_profile_record_v1",
        "checkpoint_finality_checker_executable": (
            VerifierExecutableFormatV1.STATIC_ELF_X86_64.value
        ),
        "checkpoint_finality_checker_manifest": "canonical_json_line_v1",
        "firecracker_profile": "canonical_json_line_v1",
        "machine_config": "canonical_firecracker_json_line_v1",
        "proof_verifier_executable": (VerifierExecutableFormatV1.STATIC_ELF_X86_64.value),
        "proof_verifier_manifest": "canonical_json_line_v1",
        "root_supervisor_contract": "canonical_json_line_v1",
        "root_supervisor_executable": "static_executable_v1",
        "runtime_artifact_manifest": "canonical_json_line_v1",
        "runtime_manifest": "canonical_json_line_v1",
    }
)

AUTHORITY_FIELDS_V1: Final = (
    "candidate_current",
    "candidate_selected",
    "component_artifacts_verified",
    "finality_verified",
    "live_execution_verified",
    "production_authority",
    "release_authority",
    "runtime_authority",
    "settlement_authority",
)

NON_CLAIMS_V1: Final = (
    "manifest parsing establishes canonical proposed identities only",
    "component artifact bytes are not opened or independently verified",
    "the release candidate is bound but not selected, current, or activated",
    "no proof receipt, finality certificate, Firecracker, Jailer, or supervisor execution",
    "no data availability, retrievability, state transition, or atomic commit",
    "manifest identity alone does not uniquely identify one release candidate",
    "same-interpreter code can forge nominal Python descriptors; authority consumers must revalidate exact bytes",
    "no release, runtime, settlement, production, privacy, or side-channel authority",
)

_ROOT_FIELDS_V1: Final = {
    "artifacts",
    "authority",
    "codecs",
    "format_flags",
    "interfaces",
    "non_claims",
    "policies",
    "release_revision",
    "reserved_u32",
    "schema",
    "scope",
    "status",
}
_SCOPE_FIELDS_V1: Final = {
    "application_id",
    "chain_id",
    "domain_id",
    "release_profile",
}
_ARTIFACT_FIELDS_V1: Final = {
    "authority_input_profile_sha256",
    "checkpoint_finality_checker_executable_sha256",
    "checkpoint_finality_checker_manifest_sha256",
    "firecracker_profile_sha256",
    "machine_config_sha256",
    "proof_verifier_executable_sha256",
    "proof_verifier_manifest_sha256",
    "root_supervisor_contract_sha256",
    "root_supervisor_executable_sha256",
    "runtime_artifact_manifest_sha256",
    "runtime_artifact_set_id",
    "runtime_manifest_sha256",
}
_POLICY_FIELDS_V1: Final = {
    "data_availability_policy_root",
    "finality_policy_root",
    "operational_policy_root",
    "proof_profile_sha256",
    "receipt_security_profile_sha256",
}


class SpotV7ExecutionAuthorityManifestRejectV1(ValueError):
    """Stable fail-closed rejection at the execution-manifest boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


class _ManifestConstructionSealV1:
    __slots__ = ()


_MANIFEST_CONSTRUCTION_SEAL_V1 = _ManifestConstructionSealV1()


@final
class SpotV7ExecutionAuthorityManifestV1:
    """Immutable canonical proposal; none of its identities carries authority."""

    __slots__ = (
        "_artifacts",
        "_canonical_bytes",
        "_manifest_sha256",
        "_policies",
        "_release_revision",
        "_scope",
    )

    _artifacts: MappingProxyType[str, bytes]
    _canonical_bytes: bytes
    _manifest_sha256: bytes
    _policies: MappingProxyType[str, bytes]
    _release_revision: int
    _scope: MappingProxyType[str, str]

    def __init__(
        self,
        *,
        canonical_bytes: bytes,
        scope: dict[str, str],
        release_revision: int,
        artifacts: dict[str, bytes],
        policies: dict[str, bytes],
        seal: _ManifestConstructionSealV1,
    ) -> None:
        if seal is not _MANIFEST_CONSTRUCTION_SEAL_V1:
            raise TypeError("execution authority manifest requires validated construction")
        object.__setattr__(self, "_canonical_bytes", canonical_bytes)
        object.__setattr__(self, "_manifest_sha256", hashlib.sha256(canonical_bytes).digest())
        object.__setattr__(self, "_scope", MappingProxyType(dict(scope)))
        object.__setattr__(self, "_release_revision", release_revision)
        object.__setattr__(self, "_artifacts", MappingProxyType(dict(artifacts)))
        object.__setattr__(self, "_policies", MappingProxyType(dict(policies)))

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("execution authority manifest cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("execution authority manifest cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("execution authority manifest cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("execution authority manifest cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("execution authority manifest cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("execution authority manifest cannot be serialized")

    @property
    def canonical_bytes(self) -> bytes:
        return self._canonical_bytes

    @property
    def manifest_sha256(self) -> bytes:
        return self._manifest_sha256

    @property
    def release_revision(self) -> int:
        return self._release_revision

    @property
    def component_artifacts_verified(self) -> bool:
        return False

    @property
    def finality_verified(self) -> bool:
        return False

    @property
    def live_execution_verified(self) -> bool:
        return False

    @property
    def candidate_identity_uniquely_determined(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


class _CheckedConstructionSealV1:
    __slots__ = ()


_CHECKED_CONSTRUCTION_SEAL_V1 = _CheckedConstructionSealV1()


@final
class CheckedSpotV7ExecutionAuthorityManifestV1:
    """Candidate-bound immutable descriptor with every authority fixed false."""

    __slots__ = (
        "_authority_manifest_sha256",
        "_candidate_id",
        "_candidate_manifest_sha256",
        "_execution_manifest",
        "_release_revision",
    )

    _authority_manifest_sha256: bytes
    _candidate_id: bytes
    _candidate_manifest_sha256: bytes
    _execution_manifest: SpotV7ExecutionAuthorityManifestV1
    _release_revision: int

    def __init__(
        self,
        *,
        candidate_id: bytes,
        candidate_manifest_sha256: bytes,
        execution_manifest: SpotV7ExecutionAuthorityManifestV1,
        seal: _CheckedConstructionSealV1,
    ) -> None:
        if seal is not _CHECKED_CONSTRUCTION_SEAL_V1:
            raise TypeError("checked execution authority manifest requires validated construction")
        object.__setattr__(self, "_candidate_id", candidate_id)
        object.__setattr__(self, "_candidate_manifest_sha256", candidate_manifest_sha256)
        object.__setattr__(
            self,
            "_authority_manifest_sha256",
            execution_manifest.manifest_sha256,
        )
        object.__setattr__(self, "_execution_manifest", execution_manifest)
        object.__setattr__(self, "_release_revision", execution_manifest.release_revision)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("checked execution authority manifest cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("checked execution authority manifest cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("checked execution authority manifest cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("checked execution authority manifest cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("checked execution authority manifest cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("checked execution authority manifest cannot be serialized")

    @property
    def candidate_id(self) -> bytes:
        return self._candidate_id

    @property
    def candidate_manifest_sha256(self) -> bytes:
        return self._candidate_manifest_sha256

    @property
    def authority_manifest_sha256(self) -> bytes:
        return self._authority_manifest_sha256

    @property
    def execution_manifest(self) -> SpotV7ExecutionAuthorityManifestV1:
        return self._execution_manifest

    @property
    def release_revision(self) -> int:
        return self._release_revision

    @property
    def candidate_selected(self) -> bool:
        return False

    @property
    def candidate_current(self) -> bool:
        return False

    @property
    def component_artifacts_verified(self) -> bool:
        return False

    @property
    def finality_verified(self) -> bool:
        return False

    @property
    def live_execution_verified(self) -> bool:
        return False

    @property
    def candidate_identity_uniquely_determined(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def recompose_spot_v7_execution_authority_manifest_v1(body: object) -> bytes:
    """Validate and emit the sole canonical byte representation."""

    _validate_body(body)
    raw = canonical_document_bytes_v1(body)
    return parse_exact_spot_v7_execution_authority_manifest_v1(raw).canonical_bytes


def parse_exact_spot_v7_execution_authority_manifest_v1(
    raw: bytes,
) -> SpotV7ExecutionAuthorityManifestV1:
    """Strictly parse one authority-neutral execution manifest."""

    document = _decode_exact_document(raw)
    scope, release_revision, artifacts, policies = _validate_body(document)
    return SpotV7ExecutionAuthorityManifestV1(
        canonical_bytes=raw,
        scope=scope,
        release_revision=release_revision,
        artifacts=artifacts,
        policies=policies,
        seal=_MANIFEST_CONSTRUCTION_SEAL_V1,
    )


def check_exact_spot_v7_execution_authority_manifest_v1(
    *,
    exact_release_candidate_bytes: bytes,
    exact_authority_manifest_bytes: bytes,
) -> CheckedSpotV7ExecutionAuthorityManifestV1:
    """Bind exact manifest bytes to one self-consistent authority-false candidate."""

    try:
        candidate = parse_exact_spot_v7_release_candidate_manifest_v1(exact_release_candidate_bytes)
    except (SpotV7ReleaseCandidateRejectV1, TypeError, ValueError) as exc:
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_release_candidate"
        ) from exc
    manifest = parse_exact_spot_v7_execution_authority_manifest_v1(exact_authority_manifest_bytes)
    candidate_document = _decode_validated_candidate(candidate.canonical_bytes)
    _bind_candidate_inventory(
        candidate_document=candidate_document,
        exact_authority_manifest_bytes=exact_authority_manifest_bytes,
        manifest=manifest,
    )
    return CheckedSpotV7ExecutionAuthorityManifestV1(
        candidate_id=candidate.candidate_id,
        candidate_manifest_sha256=hashlib.sha256(candidate.canonical_bytes).digest(),
        execution_manifest=manifest,
        seal=_CHECKED_CONSTRUCTION_SEAL_V1,
    )


def canonical_document_bytes_v1(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _validate_body(
    value: object,
) -> tuple[dict[str, str], int, dict[str, bytes], dict[str, bytes]]:
    _exact_fields(value, _ROOT_FIELDS_V1, "execution_authority_fields")
    document = cast(dict[str, Any], value)
    if document["schema"] != EXECUTION_AUTHORITY_MANIFEST_SCHEMA_V1:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_schema")
    if document["status"] != EXECUTION_AUTHORITY_MANIFEST_STATUS_V1:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_status")
    if type(document["format_flags"]) is not int or document["format_flags"] != 1:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_format_flags")
    if type(document["reserved_u32"]) is not int or document["reserved_u32"] != 0:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_reserved_u32")
    scope = _validate_scope(document["scope"])
    release_revision = _require_positive_u64(
        document["release_revision"], "execution_authority_release_revision"
    )
    _validate_exact_mapping(
        document["interfaces"],
        EXPECTED_INTERFACE_IDENTITIES_V1,
        "execution_authority_interfaces",
    )
    _validate_exact_mapping(
        document["codecs"],
        EXPECTED_COMPONENT_CODECS_V1,
        "execution_authority_codecs",
    )
    artifacts = _validate_digests(
        document["artifacts"],
        _ARTIFACT_FIELDS_V1,
        "execution_authority_artifacts",
    )
    if artifacts["authority_input_profile_sha256"] != (_AUTHORITY_INPUT_PROFILE_BYTES_V1):
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_artifacts")
    policies = _validate_digests(
        document["policies"],
        _POLICY_FIELDS_V1,
        "execution_authority_policies",
    )
    _validate_authority(document["authority"])
    if type(document["non_claims"]) is not list or document["non_claims"] != list(NON_CLAIMS_V1):
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_non_claims")
    return scope, release_revision, artifacts, policies


def _validate_scope(value: object) -> dict[str, str]:
    _exact_fields(value, _SCOPE_FIELDS_V1, "execution_authority_scope")
    scope = cast(dict[str, object], value)
    application_id = _scope_token(scope["application_id"])
    chain_id = _scope_token(scope["chain_id"])
    domain_id = _scope_token(scope["domain_id"])
    release_profile = _scope_token(scope["release_profile"])
    if (
        application_id != "zenodex"
        or release_profile != SPOT_V7_RELEASE_PROFILE_V1
        or chain_id == domain_id
    ):
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_scope")
    return {
        "application_id": application_id,
        "chain_id": chain_id,
        "domain_id": domain_id,
        "release_profile": release_profile,
    }


def _validate_exact_mapping(
    value: object,
    expected: MappingProxyType[str, object],
    code: str,
) -> None:
    if type(value) is not dict or set(value) != set(expected):
        raise SpotV7ExecutionAuthorityManifestRejectV1(code)
    mapping = cast(dict[str, object], value)
    for name, expected_value in expected.items():
        observed = mapping[name]
        if type(observed) is not type(expected_value) or observed != expected_value:
            raise SpotV7ExecutionAuthorityManifestRejectV1(code)


def _validate_digests(
    value: object,
    fields: set[str],
    code: str,
) -> dict[str, bytes]:
    _exact_fields(value, fields, code)
    mapping = cast(dict[str, object], value)
    output = {name: _digest_hex(mapping[name], code) for name in sorted(fields)}
    if len(set(output.values())) != len(output):
        raise SpotV7ExecutionAuthorityManifestRejectV1(code)
    return output


def _validate_authority(value: object) -> None:
    if type(value) is not dict or set(value) != set(AUTHORITY_FIELDS_V1):
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_authority")
    mapping = cast(dict[str, object], value)
    if any(type(mapping[name]) is not bool or mapping[name] is not False for name in mapping):
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_authority")


def _bind_candidate_inventory(
    *,
    candidate_document: dict[str, Any],
    exact_authority_manifest_bytes: bytes,
    manifest: SpotV7ExecutionAuthorityManifestV1,
) -> None:
    inventory = cast(list[dict[str, object]], candidate_document["evidence_inventory"])
    rows = [row for row in inventory if row.get("role") == "authority_manifest"]
    if len(rows) != 1:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_candidate_inventory")
    row = rows[0]
    digest = hashlib.sha256(exact_authority_manifest_bytes).digest()
    if row.get("codec") != EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1["authority_manifest"]:
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_inventory_codec"
        )
    if (
        _digest_hex(
            row.get("artifact_sha256"),
            "execution_authority_candidate_inventory_digest",
        )
        != digest
        or _digest_hex(
            row.get("bound_identity"),
            "execution_authority_candidate_inventory_digest",
        )
        != digest
    ):
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_inventory_digest"
        )
    if type(row.get("size_bytes")) is not int or row["size_bytes"] != len(
        exact_authority_manifest_bytes
    ):
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_inventory_size"
        )
    manifests = cast(dict[str, object], candidate_document["manifests"])
    if (
        _digest_hex(
            manifests["authority_manifest_sha256"],
            "execution_authority_candidate_manifest_binding",
        )
        != digest
    ):
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_manifest_binding"
        )
    _bind_candidate_fields(candidate_document, manifest)


def _bind_candidate_fields(
    candidate_document: dict[str, Any],
    manifest: SpotV7ExecutionAuthorityManifestV1,
) -> None:
    scope = cast(dict[str, object], candidate_document["scope"])
    lineage = cast(dict[str, object], candidate_document["lineage"])
    manifests = cast(dict[str, object], candidate_document["manifests"])
    policies = cast(dict[str, object], candidate_document["policies"])
    runtime = cast(dict[str, object], candidate_document["runtime"])
    candidate_scope = {
        "application_id": scope["application_id"],
        "chain_id": scope["chain_id"],
        "domain_id": scope["domain_id"],
        "release_profile": scope["release_profile"],
    }
    if candidate_scope != dict(manifest._scope):
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_scope_binding"
        )
    if lineage["release_revision"] != manifest.release_revision:
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_revision_binding"
        )
    expected_policy_sources = {
        "proof_profile_sha256": scope["proof_profile_sha256"],
        "receipt_security_profile_sha256": scope["receipt_security_profile_sha256"],
        "operational_policy_root": policies["operational_policy_root"],
        "data_availability_policy_root": policies["data_availability_policy_root"],
        "finality_policy_root": policies["finality_policy_root"],
    }
    for name, source in expected_policy_sources.items():
        if (
            _digest_hex(source, "execution_authority_candidate_policy_binding")
            != (manifest._policies[name])
        ):
            raise SpotV7ExecutionAuthorityManifestRejectV1(
                "execution_authority_candidate_policy_binding"
            )
    expected_artifact_sources = {
        "proof_verifier_manifest_sha256": manifests["verifier_manifest_sha256"],
        "runtime_artifact_set_id": runtime["artifact_set_id"],
        "runtime_manifest_sha256": runtime["runtime_manifest_sha256"],
        "machine_config_sha256": runtime["machine_config_sha256"],
        "firecracker_profile_sha256": runtime["firecracker_profile_sha256"],
        "authority_input_profile_sha256": runtime["authority_input_profile_sha256"],
        "root_supervisor_contract_sha256": runtime["root_supervisor_contract_sha256"],
        "root_supervisor_executable_sha256": runtime["root_supervisor_executable_sha256"],
    }
    for name, source in expected_artifact_sources.items():
        if (
            _digest_hex(source, "execution_authority_candidate_runtime_binding")
            != (manifest._artifacts[name])
        ):
            raise SpotV7ExecutionAuthorityManifestRejectV1(
                "execution_authority_candidate_runtime_binding"
            )
    inventory = cast(list[dict[str, object]], candidate_document["evidence_inventory"])
    runtime_rows = [row for row in inventory if row.get("role") == "runtime_artifact_manifest"]
    if (
        len(runtime_rows) != 1
        or _digest_hex(
            runtime_rows[0].get("artifact_sha256"),
            "execution_authority_candidate_runtime_artifact_binding",
        )
        != manifest._artifacts["runtime_artifact_manifest_sha256"]
    ):
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_candidate_runtime_artifact_binding"
        )


def _decode_exact_document(raw: bytes) -> dict[str, Any]:
    if type(raw) is not bytes or not 0 < len(raw) <= MAX_EXECUTION_AUTHORITY_MANIFEST_BYTES_V1:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_json")
    _require_bounded_json_depth(raw)
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_json_number,
            parse_constant=_reject_json_number,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_json") from exc
    if type(value) is not dict or canonical_document_bytes_v1(value) != raw:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_json")
    return value


def _decode_validated_candidate(raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(raw.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        raise SpotV7ExecutionAuthorityManifestRejectV1(
            "execution_authority_release_candidate"
        ) from exc
    if type(value) is not dict:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_release_candidate")
    return value


def _require_bounded_json_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in {0x5B, 0x7B}:
            depth += 1
            if depth > MAX_EXECUTION_AUTHORITY_MANIFEST_JSON_DEPTH_V1:
                raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_depth")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_json")
    if depth != 0 or in_string or escaped:
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_json")


def _exact_fields(value: object, expected: set[str], code: str) -> None:
    if type(value) is not dict or set(value) != expected:
        raise SpotV7ExecutionAuthorityManifestRejectV1(code)


def _scope_token(value: object) -> str:
    if (
        type(value) is not str
        or not value
        or len(value) > MAX_SCOPE_TEXT_CHARS_V1
        or value in {".", ".."}
        or ".." in value
        or any(
            not (character.isascii() and (character.isalnum() or character in "._:-"))
            for character in value
        )
    ):
        raise SpotV7ExecutionAuthorityManifestRejectV1("execution_authority_scope")
    return value


def _digest_hex(value: object, code: str) -> bytes:
    if type(value) is not str or len(value) != 64 or value != value.lower():
        raise SpotV7ExecutionAuthorityManifestRejectV1(code)
    try:
        decoded = bytes.fromhex(value)
    except ValueError as exc:
        raise SpotV7ExecutionAuthorityManifestRejectV1(code) from exc
    if len(decoded) != 32 or not any(decoded):
        raise SpotV7ExecutionAuthorityManifestRejectV1(code)
    return decoded


def _require_positive_u64(value: object, code: str) -> int:
    if type(value) is not int or not 0 < value <= 0xFFFF_FFFF_FFFF_FFFF:
        raise SpotV7ExecutionAuthorityManifestRejectV1(code)
    return value


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate JSON key")
        output[key] = value
    return output


def _reject_json_number(_value: str) -> NoReturn:
    raise ValueError("non-integer JSON number")
