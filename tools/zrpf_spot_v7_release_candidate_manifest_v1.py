"""Exact authority-neutral release candidate for the bounded Spot V7 lane.

This module is a pure format, recomposition, and checking boundary.  It binds
the complete proposed release surface without reading artifacts, selecting a
release, executing a verifier, or minting an authority capability.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Final, NoReturn, cast, final

SPOT_V7_RELEASE_CANDIDATE_MANIFEST_SCHEMA_V1: Final = (
    "zenodex/zrpf_spot_v7_release_candidate_manifest/v1"
)
SPOT_V7_RELEASE_CANDIDATE_MANIFEST_STATUS_V1: Final = (
    "authority_neutral_release_candidate"
)
SPOT_V7_RELEASE_PROFILE_V1: Final = "zenodex_spot_v7_bounded_single_action_v1"

MAX_RELEASE_CANDIDATE_BYTES_V1: Final = 256 * 1_024
MAX_RELEASE_CANDIDATE_JSON_DEPTH_V1: Final = 4
MAX_SCOPE_TEXT_CHARS_V1: Final = 96
MAX_EVIDENCE_BYTES_V1: Final = 1_024 * 1_024 * 1_024

AUTHORITY_FIELDS_V1: Final = (
    "activation_authority",
    "candidate_current",
    "candidate_selected",
    "proof_evidence_verified",
    "production_authority",
    "release_authority",
    "revocation_authority",
    "rollback_authority",
    "runtime_execution_verified",
    "settlement_authority",
    "source_to_binary_verified",
)

NON_CLAIMS_V1: Final = (
    "candidate bytes bind proposed identities only",
    "no artifact bytes, proof receipts, journals, or mutations are verified",
    "no source-to-binary or cross-host reproducible release is established",
    "no release selection, activation, current-head, revocation, or rollback authority",
    "no live verifier, Jailer, Firecracker, supervisor, or sandbox execution",
    "no data-availability, retrievability, or finality satisfaction claim",
    "no release, settlement, production, privacy, or side-channel authority",
)

REQUIRED_EVIDENCE_ROLES_V1: Final = (
    "proof_profile",
    "receipt_security_profile",
    "revocation_policy",
    "rollback_policy",
    "source_closure",
    "build_input_closure",
    "toolchain_manifest",
    "build_container_manifest",
    "v6_program_bundle",
    "v6_image_identity_manifest",
    "v6_receipt_bundle",
    "v6_journal_bundle",
    "v6_mutation_report",
    "v7_program",
    "v7_image_identity_manifest",
    "v7_receipt",
    "v7_journal",
    "v7_mutation_report",
    "verifier_manifest",
    "authority_manifest",
    "replay_manifest",
    "runtime_manifest",
    "machine_config",
    "runtime_artifact_manifest",
    "root_supervisor_contract",
    "root_supervisor_executable",
    "firecracker_profile",
    "authority_input_profile",
    "operational_policy",
    "data_availability_policy",
    "finality_policy",
)

EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1: Final = MappingProxyType(
    {
        "proof_profile": "canonical_json_line_v1",
        "receipt_security_profile": "canonical_json_line_v1",
        "revocation_policy": "canonical_json_line_v1",
        "rollback_policy": "canonical_json_line_v1",
        "source_closure": "canonical_json_line_v1",
        "build_input_closure": "canonical_json_line_v1",
        "toolchain_manifest": "canonical_json_line_v1",
        "build_container_manifest": "canonical_json_line_v1",
        "v6_program_bundle": "opaque_program_bundle_v1",
        "v6_image_identity_manifest": "canonical_json_line_v1",
        "v6_receipt_bundle": "risc0_canonical_receipt_bundle_v1",
        "v6_journal_bundle": "opaque_journal_bundle_v1",
        "v6_mutation_report": "canonical_mutation_report_v1",
        "v7_program": "risc0_program_elf_v1",
        "v7_image_identity_manifest": "canonical_json_line_v1",
        "v7_receipt": "risc0_canonical_receipt_v1",
        "v7_journal": "opaque_journal_v1",
        "v7_mutation_report": "canonical_mutation_report_v1",
        "verifier_manifest": "canonical_json_line_v1",
        "authority_manifest": "canonical_json_line_v1",
        "replay_manifest": "canonical_json_line_v1",
        "runtime_manifest": "canonical_json_line_v1",
        "machine_config": "canonical_firecracker_json_line_v1",
        "runtime_artifact_manifest": "canonical_json_line_v1",
        "root_supervisor_contract": "canonical_json_line_v1",
        "root_supervisor_executable": "static_executable_v1",
        "firecracker_profile": "canonical_json_line_v1",
        "authority_input_profile": "canonical_binary_profile_record_v1",
        "operational_policy": "canonical_json_line_v1",
        "data_availability_policy": "canonical_json_line_v1",
        "finality_policy": "canonical_json_line_v1",
    }
)

MAX_EVIDENCE_BYTES_BY_ROLE_V1: Final = MappingProxyType(
    {
        role: (
            512 * 1_024 * 1_024
            if role in {"v6_program_bundle", "v7_program"}
            else 256 * 1_024 * 1_024
            if role == "root_supervisor_executable"
            else 64 * 1_024 * 1_024
            if role in {"v6_receipt_bundle", "v6_journal_bundle", "v7_receipt"}
            else 16 * 1_024 * 1_024
        )
        for role in REQUIRED_EVIDENCE_ROLES_V1
    }
)

_CANDIDATE_ID_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.release_candidate_id.v1"
_INVENTORY_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.release_evidence_inventory.v1"

_BODY_FIELDS_V1: Final = {
    "authority",
    "evidence_inventory",
    "format_flags",
    "lineage",
    "manifests",
    "non_claims",
    "policies",
    "proofs",
    "reserved_u32",
    "runtime",
    "schema",
    "scope",
    "source_build",
    "status",
}
_DOCUMENT_FIELDS_V1: Final = _BODY_FIELDS_V1 | {
    "candidate_id",
    "evidence_inventory_root",
}
_SCOPE_FIELDS_V1: Final = {
    "application_id",
    "chain_id",
    "domain_id",
    "proof_profile_sha256",
    "receipt_security_profile_sha256",
    "release_profile",
}
_LINEAGE_FIELDS_V1: Final = {
    "minimum_rollback_revision",
    "parent_candidate_id",
    "proposed_activation_epoch",
    "proposed_expiration_epoch",
    "release_revision",
    "revocation_policy_root",
    "revocation_record_root",
    "rollback_policy_root",
}
_SOURCE_BUILD_FIELDS_V1: Final = {
    "build_container_manifest_sha256",
    "build_input_closure_root",
    "source_closure_root",
    "source_commit",
    "source_tree",
    "toolchain_manifest_sha256",
}
_PROOF_FIELDS_V1: Final = {
    "v6_image_id_root",
    "v6_journal_root",
    "v6_mutation_root",
    "v6_program_root",
    "v6_receipt_root",
    "v7_image_id_root",
    "v7_journal_root",
    "v7_mutation_root",
    "v7_program_root",
    "v7_receipt_root",
}
_MANIFEST_FIELDS_V1: Final = {
    "authority_manifest_sha256",
    "replay_manifest_sha256",
    "verifier_manifest_sha256",
}
_RUNTIME_FIELDS_V1: Final = {
    "artifact_set_id",
    "authority_input_profile_sha256",
    "firecracker_profile_sha256",
    "machine_config_sha256",
    "root_supervisor_contract_sha256",
    "root_supervisor_executable_sha256",
    "runtime_manifest_sha256",
}
_POLICY_FIELDS_V1: Final = {
    "data_availability_policy_root",
    "finality_policy_root",
    "operational_policy_root",
}
_INVENTORY_ROW_FIELDS_V1: Final = {"codec", "role", "sha256", "size_bytes"}

_EVIDENCE_BINDING_BY_ROLE_V1: Final = MappingProxyType(
    {
        "proof_profile": ("scope", "proof_profile_sha256"),
        "receipt_security_profile": ("scope", "receipt_security_profile_sha256"),
        "revocation_policy": ("lineage", "revocation_policy_root"),
        "rollback_policy": ("lineage", "rollback_policy_root"),
        "source_closure": ("source_build", "source_closure_root"),
        "build_input_closure": ("source_build", "build_input_closure_root"),
        "toolchain_manifest": ("source_build", "toolchain_manifest_sha256"),
        "build_container_manifest": (
            "source_build",
            "build_container_manifest_sha256",
        ),
        "v6_program_bundle": ("proofs", "v6_program_root"),
        "v6_image_identity_manifest": ("proofs", "v6_image_id_root"),
        "v6_receipt_bundle": ("proofs", "v6_receipt_root"),
        "v6_journal_bundle": ("proofs", "v6_journal_root"),
        "v6_mutation_report": ("proofs", "v6_mutation_root"),
        "v7_program": ("proofs", "v7_program_root"),
        "v7_image_identity_manifest": ("proofs", "v7_image_id_root"),
        "v7_receipt": ("proofs", "v7_receipt_root"),
        "v7_journal": ("proofs", "v7_journal_root"),
        "v7_mutation_report": ("proofs", "v7_mutation_root"),
        "verifier_manifest": ("manifests", "verifier_manifest_sha256"),
        "authority_manifest": ("manifests", "authority_manifest_sha256"),
        "replay_manifest": ("manifests", "replay_manifest_sha256"),
        "runtime_manifest": ("runtime", "runtime_manifest_sha256"),
        "machine_config": ("runtime", "machine_config_sha256"),
        "runtime_artifact_manifest": ("runtime", "artifact_set_id"),
        "root_supervisor_contract": ("runtime", "root_supervisor_contract_sha256"),
        "root_supervisor_executable": (
            "runtime",
            "root_supervisor_executable_sha256",
        ),
        "firecracker_profile": ("runtime", "firecracker_profile_sha256"),
        "authority_input_profile": (
            "runtime",
            "authority_input_profile_sha256",
        ),
        "operational_policy": ("policies", "operational_policy_root"),
        "data_availability_policy": (
            "policies",
            "data_availability_policy_root",
        ),
        "finality_policy": ("policies", "finality_policy_root"),
    }
)


class SpotV7ReleaseCandidateRejectV1(ValueError):
    """Stable fail-closed rejection at the release-candidate boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


class _CandidateConstructionSealV1:
    __slots__ = ()


_CANDIDATE_CONSTRUCTION_SEAL_V1 = _CandidateConstructionSealV1()


@final
@dataclass(frozen=True, slots=True, init=False)
class SpotV7ReleaseCandidateManifestV1:
    """Validated candidate identity carrying no selection or release authority."""

    canonical_bytes: bytes
    candidate_id: bytes
    evidence_inventory_root: bytes
    release_revision: int
    parent_candidate_id: bytes | None

    def __new__(cls) -> SpotV7ReleaseCandidateManifestV1:
        raise TypeError("release candidate requires validated construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        canonical_bytes: bytes,
        candidate_id: bytes,
        evidence_inventory_root: bytes,
        release_revision: int,
        parent_candidate_id: bytes | None,
        seal: _CandidateConstructionSealV1,
    ) -> SpotV7ReleaseCandidateManifestV1:
        if seal is not _CANDIDATE_CONSTRUCTION_SEAL_V1:
            raise TypeError("release candidate requires the module-private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "canonical_bytes", canonical_bytes)
        object.__setattr__(value, "candidate_id", candidate_id)
        object.__setattr__(value, "evidence_inventory_root", evidence_inventory_root)
        object.__setattr__(value, "release_revision", release_revision)
        object.__setattr__(value, "parent_candidate_id", parent_candidate_id)
        return value

    @property
    def candidate_selected(self) -> bool:
        return False

    @property
    def candidate_current(self) -> bool:
        return False

    @property
    def activation_authority(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def rollback_authority(self) -> bool:
        return False

    @property
    def source_to_binary_verified(self) -> bool:
        return False

    @property
    def proof_evidence_verified(self) -> bool:
        return False

    @property
    def runtime_execution_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def recompose_spot_v7_release_candidate_manifest_v1(body: object) -> bytes:
    """Validate all proposal fields and derive the exact inventory and candidate IDs."""

    _validate_body(body)
    body_map = cast(dict[str, Any], body)
    inventory_root = _inventory_root(body_map["evidence_inventory"])
    identity_document = {**body_map, "evidence_inventory_root": inventory_root.hex()}
    candidate_id = _candidate_id(identity_document)
    document = {**identity_document, "candidate_id": candidate_id.hex()}
    raw = canonical_document_bytes_v1(document)
    return parse_exact_spot_v7_release_candidate_manifest_v1(raw).canonical_bytes


def parse_exact_spot_v7_release_candidate_manifest_v1(
    raw: bytes,
) -> SpotV7ReleaseCandidateManifestV1:
    """Strictly decode and independently recompose one authority-neutral candidate."""

    document = _decode_exact_document(raw)
    _require_exact_fields(document, _DOCUMENT_FIELDS_V1, "release_candidate_fields")
    body = {field: document[field] for field in _BODY_FIELDS_V1}
    _validate_body(body)
    inventory_root = _inventory_root(body["evidence_inventory"])
    _require_exact_digest(
        document["evidence_inventory_root"],
        inventory_root,
        "release_candidate_inventory_root",
    )
    identity_document = {**body, "evidence_inventory_root": inventory_root.hex()}
    candidate_id = _candidate_id(identity_document)
    _require_exact_digest(document["candidate_id"], candidate_id, "release_candidate_id")
    lineage = cast(dict[str, Any], body["lineage"])
    parent = lineage["parent_candidate_id"]
    return SpotV7ReleaseCandidateManifestV1._from_validated(
        canonical_bytes=raw,
        candidate_id=candidate_id,
        evidence_inventory_root=inventory_root,
        release_revision=lineage["release_revision"],
        parent_candidate_id=None if parent is None else bytes.fromhex(parent),
        seal=_CANDIDATE_CONSTRUCTION_SEAL_V1,
    )


def check_exact_spot_v7_release_candidate_manifest_v1(
    raw: bytes,
    *,
    expected_candidate_id: bytes,
) -> SpotV7ReleaseCandidateManifestV1:
    """Check exact bytes against an independently supplied expected candidate ID."""

    expected = _require_digest_bytes(expected_candidate_id, "release_candidate_expected_id")
    candidate = parse_exact_spot_v7_release_candidate_manifest_v1(raw)
    if candidate.candidate_id != expected:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_expected_id")
    return candidate


def canonical_document_bytes_v1(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _validate_body(value: object) -> None:
    _require_exact_fields(value, _BODY_FIELDS_V1, "release_candidate_fields")
    document = cast(dict[str, Any], value)
    if document["schema"] != SPOT_V7_RELEASE_CANDIDATE_MANIFEST_SCHEMA_V1:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_schema")
    if document["status"] != SPOT_V7_RELEASE_CANDIDATE_MANIFEST_STATUS_V1:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_status")
    if type(document["format_flags"]) is not int or document["format_flags"] != 1:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_format_flags")
    if type(document["reserved_u32"]) is not int or document["reserved_u32"] != 0:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_reserved_u32")
    _validate_scope(document["scope"])
    _validate_lineage(document["lineage"])
    _validate_digest_section(
        document["source_build"], _SOURCE_BUILD_FIELDS_V1, "source_build"
    )
    _validate_digest_section(document["proofs"], _PROOF_FIELDS_V1, "proofs")
    _validate_digest_section(document["manifests"], _MANIFEST_FIELDS_V1, "manifests")
    _validate_digest_section(document["runtime"], _RUNTIME_FIELDS_V1, "runtime")
    _validate_digest_section(document["policies"], _POLICY_FIELDS_V1, "policies")
    _validate_authority(document["authority"])
    if type(document["non_claims"]) is not list or document["non_claims"] != list(
        NON_CLAIMS_V1
    ):
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_non_claims")
    inventory = _validate_inventory(document["evidence_inventory"])
    _validate_inventory_bindings(document, inventory)


def _validate_scope(value: object) -> None:
    _require_exact_fields(value, _SCOPE_FIELDS_V1, "release_candidate_scope")
    scope = cast(dict[str, Any], value)
    if scope["application_id"] != "zenodex":
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_scope")
    _require_bounded_scope_text(scope["chain_id"])
    _require_bounded_scope_text(scope["domain_id"])
    if scope["chain_id"] == scope["domain_id"]:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_scope")
    if scope["release_profile"] != SPOT_V7_RELEASE_PROFILE_V1:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_scope")
    _require_digest_hex(scope["proof_profile_sha256"], "release_candidate_scope")
    _require_digest_hex(
        scope["receipt_security_profile_sha256"],
        "release_candidate_scope",
    )


def _validate_lineage(value: object) -> None:
    _require_exact_fields(value, _LINEAGE_FIELDS_V1, "release_candidate_lineage")
    lineage = cast(dict[str, Any], value)
    revision = _require_u64(lineage["release_revision"], "release_candidate_revision")
    if revision == 0:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_revision")
    parent = lineage["parent_candidate_id"]
    if revision == 1:
        if parent is not None:
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_parent")
    elif parent is None:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_parent")
    else:
        _require_digest_hex(parent, "release_candidate_parent")
    activation = _require_u64(
        lineage["proposed_activation_epoch"],
        "release_candidate_activation",
    )
    expiration = lineage["proposed_expiration_epoch"]
    if expiration is not None:
        expiration_value = _require_u64(expiration, "release_candidate_expiration")
        if expiration_value <= activation:
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_expiration")
    minimum_rollback = _require_u64(
        lineage["minimum_rollback_revision"],
        "release_candidate_rollback_revision",
    )
    if minimum_rollback > revision:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_rollback_revision")
    _require_digest_hex(lineage["revocation_policy_root"], "release_candidate_lineage")
    _require_digest_hex(lineage["rollback_policy_root"], "release_candidate_lineage")
    if lineage["revocation_record_root"] is not None:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_revocation_state")


def _validate_digest_section(
    value: object,
    fields: set[str],
    section: str,
) -> None:
    code = f"release_candidate_{section}"
    _require_exact_fields(value, fields, code)
    section_value = cast(dict[str, Any], value)
    for field in fields:
        if section == "source_build" and field in {"source_commit", "source_tree"}:
            _require_sha1_hex(section_value[field], code)
        else:
            _require_digest_hex(section_value[field], code)
    if section == "source_build" and section_value["source_commit"] == section_value[
        "source_tree"
    ]:
        raise SpotV7ReleaseCandidateRejectV1(code)


def _validate_authority(value: object) -> None:
    if type(value) is not dict or set(value) != set(AUTHORITY_FIELDS_V1):
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_authority")
    if any(type(value[name]) is not bool or value[name] is not False for name in value):
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_authority")


def _validate_inventory(value: object) -> dict[str, dict[str, object]]:
    if type(value) is not list or len(value) != len(REQUIRED_EVIDENCE_ROLES_V1):
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_inventory_order")
    output: dict[str, dict[str, object]] = {}
    digests: set[str] = set()
    total_size_bytes = 0
    for index, expected_role in enumerate(REQUIRED_EVIDENCE_ROLES_V1):
        row = value[index]
        _require_exact_fields(row, _INVENTORY_ROW_FIELDS_V1, "release_candidate_inventory_row")
        row_value = cast(dict[str, object], row)
        if row_value["role"] != expected_role:
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_inventory_order")
        if row_value["codec"] != EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1[expected_role]:
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_inventory_codec")
        digest = _require_digest_hex(
            row_value["sha256"], "release_candidate_inventory_digest"
        )
        if digest.hex() in digests:
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_inventory_digest")
        digests.add(digest.hex())
        maximum = MAX_EVIDENCE_BYTES_BY_ROLE_V1[expected_role]
        if (
            type(row_value["size_bytes"]) is not int
            or not 0 < row_value["size_bytes"] <= maximum
        ):
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_inventory_size")
        size_bytes = row_value["size_bytes"]
        if total_size_bytes > MAX_EVIDENCE_BYTES_V1 - size_bytes:
            raise SpotV7ReleaseCandidateRejectV1(
                "release_candidate_inventory_total_size"
            )
        total_size_bytes += size_bytes
        output[expected_role] = row_value
    return output


def _validate_inventory_bindings(
    body: dict[str, Any],
    inventory: dict[str, dict[str, object]],
) -> None:
    for role in REQUIRED_EVIDENCE_ROLES_V1:
        section, field = _EVIDENCE_BINDING_BY_ROLE_V1[role]
        if body[section][field] != inventory[role]["sha256"]:
            raise SpotV7ReleaseCandidateRejectV1("release_candidate_inventory_binding")


def _inventory_root(value: object) -> bytes:
    _validate_inventory(value)
    return _domain_hash(_INVENTORY_ROOT_DOMAIN_V1, canonical_document_bytes_v1(value))


def _candidate_id(identity_document: object) -> bytes:
    return _domain_hash(_CANDIDATE_ID_DOMAIN_V1, canonical_document_bytes_v1(identity_document))


def _domain_hash(domain: bytes, payload: bytes) -> bytes:
    return hashlib.sha256(
        len(domain).to_bytes(2, "big")
        + domain
        + len(payload).to_bytes(8, "big")
        + payload
    ).digest()


def _decode_exact_document(raw: bytes) -> dict[str, Any]:
    if type(raw) is not bytes or not 0 < len(raw) <= MAX_RELEASE_CANDIDATE_BYTES_V1:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_json")
    _require_bounded_json_depth(raw)
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_json_number,
            parse_constant=_reject_json_number,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_json") from exc
    if type(document) is not dict or canonical_document_bytes_v1(document) != raw:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_json")
    return document


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
            if depth > MAX_RELEASE_CANDIDATE_JSON_DEPTH_V1:
                raise SpotV7ReleaseCandidateRejectV1("release_candidate_depth")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise SpotV7ReleaseCandidateRejectV1("release_candidate_json")
    if depth != 0 or in_string or escaped:
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_json")


def _require_exact_fields(value: object, expected: set[str], code: str) -> None:
    if type(value) is not dict or set(value) != expected:
        raise SpotV7ReleaseCandidateRejectV1(code)


def _require_bounded_scope_text(value: object) -> str:
    if (
        type(value) is not str
        or not value
        or len(value) > MAX_SCOPE_TEXT_CHARS_V1
        or any(
            not (
                character.isascii()
                and (character.isalnum() or character in "._:-")
            )
            for character in value
        )
    ):
        raise SpotV7ReleaseCandidateRejectV1("release_candidate_scope")
    return value


def _require_digest_hex(value: object, code: str) -> bytes:
    if type(value) is not str or len(value) != 64 or value != value.lower():
        raise SpotV7ReleaseCandidateRejectV1(code)
    try:
        raw = bytes.fromhex(value)
    except ValueError as exc:
        raise SpotV7ReleaseCandidateRejectV1(code) from exc
    return _require_digest_bytes(raw, code)


def _require_exact_digest(value: object, expected: bytes, code: str) -> None:
    if _require_digest_hex(value, code) != expected:
        raise SpotV7ReleaseCandidateRejectV1(code)


def _require_digest_bytes(value: object, code: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise SpotV7ReleaseCandidateRejectV1(code)
    return value


def _require_sha1_hex(value: object, code: str) -> str:
    if type(value) is not str or len(value) != 40 or value != value.lower():
        raise SpotV7ReleaseCandidateRejectV1(code)
    try:
        raw = bytes.fromhex(value)
    except ValueError as exc:
        raise SpotV7ReleaseCandidateRejectV1(code) from exc
    if len(raw) != 20 or not any(raw):
        raise SpotV7ReleaseCandidateRejectV1(code)
    return value


def _require_u64(value: object, code: str) -> int:
    if type(value) is not int or not 0 <= value <= 0xFFFF_FFFF_FFFF_FFFF:
        raise SpotV7ReleaseCandidateRejectV1(code)
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
