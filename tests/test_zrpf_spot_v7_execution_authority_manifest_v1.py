from __future__ import annotations

import copy
import hashlib
import json
import pickle
import re
import sys
from collections.abc import Callable
from pathlib import Path
from types import FrameType
from typing import Any, cast

import pytest

from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate
from tools.check_zrpf_spot_settlement_v7_local_evidence import (
    RECEIPT_SECURITY_PROFILE_ID_V1,
    SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


def _digest(position: int) -> str:
    value = bytes(
        ((position * 41) + (offset * 23) + (offset * offset * 7)) % 256 for offset in range(32)
    )
    assert any(value)
    return value.hex()


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _rust_string_constant(source: str, name: str) -> str:
    match = re.search(
        rf'pub const {re.escape(name)}: &str\s*=\s*"([^"]+)";',
        source,
        flags=re.DOTALL,
    )
    assert match is not None, name
    return match.group(1)


def _candidate_body() -> dict[str, Any]:
    inventory: list[dict[str, object]] = []
    for index, role in enumerate(candidate.REQUIRED_EVIDENCE_ROLES_V1):
        artifact_sha256 = _digest(index + 1)
        bound_identity = (
            artifact_sha256
            if role in candidate.RAW_ARTIFACT_DIGEST_ROLES_V1
            else _digest(index + 101)
        )
        inventory.append(
            {
                "artifact_sha256": artifact_sha256,
                "bound_identity": bound_identity,
                "codec": candidate.EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1[role],
                "role": role,
                "size_bytes": 1_001 + index,
            }
        )
    rows = {cast(str, row["role"]): row for row in inventory}
    authority_input = rows["authority_input_profile"]
    authority_input["artifact_sha256"] = authority.SPOT_V7_AUTHORITY_INPUT_PROFILE_SHA256_V1
    authority_input["bound_identity"] = authority.SPOT_V7_AUTHORITY_INPUT_PROFILE_SHA256_V1
    identity = {role: cast(str, row["bound_identity"]) for role, row in rows.items()}
    return {
        "authority": {name: False for name in candidate.AUTHORITY_FIELDS_V1},
        "evidence_inventory": inventory,
        "format_flags": 1,
        "lineage": {
            "minimum_rollback_revision": 1,
            "parent_candidate_id": _digest(501),
            "proposed_activation_epoch": 100,
            "proposed_expiration_epoch": 200,
            "release_revision": 7,
            "revocation_policy_root": identity["revocation_policy"],
            "revocation_record_root": None,
            "rollback_policy_root": identity["rollback_policy"],
        },
        "manifests": {
            "authority_manifest_sha256": identity["authority_manifest"],
            "replay_manifest_sha256": identity["replay_manifest"],
            "verifier_manifest_sha256": identity["verifier_manifest"],
        },
        "non_claims": list(candidate.NON_CLAIMS_V1),
        "policies": {
            "data_availability_policy_root": identity["data_availability_policy"],
            "finality_policy_root": identity["finality_policy"],
            "operational_policy_root": identity["operational_policy"],
        },
        "proofs": {
            "v6_image_id_root": identity["v6_image_identity_manifest"],
            "v6_journal_root": identity["v6_journal_bundle"],
            "v6_mutation_root": identity["v6_mutation_report"],
            "v6_program_root": identity["v6_program_bundle"],
            "v6_receipt_root": identity["v6_receipt_bundle"],
            "v7_image_id_root": identity["v7_image_identity_manifest"],
            "v7_journal_root": identity["v7_journal"],
            "v7_mutation_root": identity["v7_mutation_report"],
            "v7_program_root": identity["v7_program"],
            "v7_receipt_root": identity["v7_receipt"],
        },
        "reserved_u32": 0,
        "runtime": {
            "artifact_set_id": identity["runtime_artifact_manifest"],
            "authority_input_profile_sha256": identity["authority_input_profile"],
            "firecracker_profile_sha256": identity["firecracker_profile"],
            "machine_config_sha256": identity["machine_config"],
            "root_supervisor_contract_sha256": identity["root_supervisor_contract"],
            "root_supervisor_executable_sha256": identity["root_supervisor_executable"],
            "runtime_manifest_sha256": identity["runtime_manifest"],
        },
        "schema": candidate.SPOT_V7_RELEASE_CANDIDATE_MANIFEST_SCHEMA_V1,
        "scope": {
            "application_id": "zenodex",
            "chain_id": "tau-chain-314159",
            "domain_id": "spot-domain-271828",
            "proof_profile_sha256": identity["proof_profile"],
            "receipt_security_profile_sha256": identity["receipt_security_profile"],
            "release_profile": candidate.SPOT_V7_RELEASE_PROFILE_V1,
        },
        "source_build": {
            "build_container_manifest_sha256": identity["build_container_manifest"],
            "build_input_closure_root": identity["build_input_closure"],
            "source_closure_root": identity["source_closure"],
            "source_commit": "11" * 20,
            "source_tree": "22" * 20,
            "toolchain_manifest_sha256": identity["toolchain_manifest"],
        },
        "status": candidate.SPOT_V7_RELEASE_CANDIDATE_MANIFEST_STATUS_V1,
    }


def _inventory_row(body: dict[str, Any], role: str) -> dict[str, Any]:
    rows = cast(list[dict[str, Any]], body["evidence_inventory"])
    return next(row for row in rows if row["role"] == role)


def _candidate_body_from_bytes(raw: bytes) -> dict[str, Any]:
    body = cast(dict[str, Any], json.loads(raw))
    body.pop("candidate_id")
    body.pop("evidence_inventory_root")
    return body


def _authority_body(candidate_body: dict[str, Any]) -> dict[str, Any]:
    runtime = cast(dict[str, Any], candidate_body["runtime"])
    scope = cast(dict[str, Any], candidate_body["scope"])
    policies = cast(dict[str, Any], candidate_body["policies"])
    manifests = cast(dict[str, Any], candidate_body["manifests"])
    runtime_artifact = _inventory_row(candidate_body, "runtime_artifact_manifest")
    return {
        "artifacts": {
            "authority_input_profile_sha256": runtime["authority_input_profile_sha256"],
            "checkpoint_finality_checker_executable_sha256": _digest(601),
            "checkpoint_finality_checker_manifest_sha256": _digest(602),
            "firecracker_profile_sha256": runtime["firecracker_profile_sha256"],
            "machine_config_sha256": runtime["machine_config_sha256"],
            "proof_verifier_executable_sha256": _digest(600),
            "proof_verifier_manifest_sha256": manifests["verifier_manifest_sha256"],
            "root_supervisor_contract_sha256": runtime["root_supervisor_contract_sha256"],
            "root_supervisor_executable_sha256": runtime["root_supervisor_executable_sha256"],
            "runtime_artifact_manifest_sha256": runtime_artifact["artifact_sha256"],
            "runtime_artifact_set_id": runtime["artifact_set_id"],
            "runtime_manifest_sha256": runtime["runtime_manifest_sha256"],
        },
        "authority": {name: False for name in authority.AUTHORITY_FIELDS_V1},
        "codecs": dict(authority.EXPECTED_COMPONENT_CODECS_V1),
        "format_flags": 1,
        "interfaces": dict(authority.EXPECTED_INTERFACE_IDENTITIES_V1),
        "non_claims": list(authority.NON_CLAIMS_V1),
        "policies": {
            "data_availability_policy_root": policies["data_availability_policy_root"],
            "finality_policy_root": policies["finality_policy_root"],
            "operational_policy_root": policies["operational_policy_root"],
            "proof_profile_sha256": scope["proof_profile_sha256"],
            "receipt_security_profile_sha256": scope["receipt_security_profile_sha256"],
        },
        "release_revision": candidate_body["lineage"]["release_revision"],
        "reserved_u32": 0,
        "schema": authority.EXECUTION_AUTHORITY_MANIFEST_SCHEMA_V1,
        "scope": {
            "application_id": scope["application_id"],
            "chain_id": scope["chain_id"],
            "domain_id": scope["domain_id"],
            "release_profile": scope["release_profile"],
        },
        "status": authority.EXECUTION_AUTHORITY_MANIFEST_STATUS_V1,
    }


def _fixture() -> tuple[dict[str, Any], dict[str, Any], bytes, bytes]:
    candidate_body = _candidate_body()
    authority_body = _authority_body(candidate_body)
    authority_bytes = authority.recompose_spot_v7_execution_authority_manifest_v1(authority_body)
    authority_digest = hashlib.sha256(authority_bytes).hexdigest()
    row = _inventory_row(candidate_body, "authority_manifest")
    row["artifact_sha256"] = authority_digest
    row["bound_identity"] = authority_digest
    row["size_bytes"] = len(authority_bytes)
    candidate_body["manifests"]["authority_manifest_sha256"] = authority_digest
    candidate_bytes = candidate.recompose_spot_v7_release_candidate_manifest_v1(candidate_body)
    return candidate_body, authority_body, candidate_bytes, authority_bytes


def test_exact_manifest_recomposes_and_candidate_inventory_binding_is_authority_false() -> None:
    candidate_body, authority_body, candidate_bytes, authority_bytes = _fixture()
    parsed = authority.parse_exact_spot_v7_execution_authority_manifest_v1(authority_bytes)
    checked = authority.check_exact_spot_v7_execution_authority_manifest_v1(
        exact_release_candidate_bytes=candidate_bytes,
        exact_authority_manifest_bytes=authority_bytes,
    )

    assert parsed.canonical_bytes == authority_bytes
    assert parsed.manifest_sha256 == hashlib.sha256(authority_bytes).digest()
    assert checked.candidate_id.hex() == json.loads(candidate_bytes)["candidate_id"]
    assert checked.candidate_manifest_sha256 == hashlib.sha256(candidate_bytes).digest()
    assert checked.authority_manifest_sha256 == parsed.manifest_sha256
    assert checked.release_revision == 7
    assert checked.execution_manifest is parsed or (
        checked.execution_manifest.canonical_bytes == parsed.canonical_bytes
    )
    assert "candidate_id" not in authority_body
    assert "candidate_id" not in authority_bytes.decode("ascii")
    assert checked.candidate_selected is False
    assert checked.candidate_current is False
    assert checked.component_artifacts_verified is False
    assert checked.finality_verified is False
    assert checked.live_execution_verified is False
    assert checked.candidate_identity_uniquely_determined is False
    assert checked.hostile_same_interpreter_resistance_established is False
    assert checked.release_authority is False
    assert checked.runtime_authority is False
    assert checked.settlement_authority is False
    assert checked.production_authority is False
    assert parsed.release_authority is False
    assert parsed.component_artifacts_verified is False
    assert parsed.finality_verified is False
    assert parsed.live_execution_verified is False
    assert parsed.candidate_identity_uniquely_determined is False
    assert parsed.hostile_same_interpreter_resistance_established is False
    assert parsed.runtime_authority is False
    assert parsed.settlement_authority is False
    assert parsed.production_authority is False
    assert (
        candidate_body["runtime"]["artifact_set_id"]
        != _inventory_row(candidate_body, "runtime_artifact_manifest")["artifact_sha256"]
    )


def test_literal_profile_identifiers_match_existing_governed_surfaces() -> None:
    replay_profile = json.loads(
        (
            REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json"
        ).read_bytes()
    )
    runtime_artifacts = json.loads(
        (
            REPO_ROOT
            / "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v2.json"
        ).read_bytes()
    )
    assert replay_profile["schema"] == authority.FIRECRACKER_REPLAY_PROFILE_SCHEMA_V1
    assert runtime_artifacts["schema"] == authority.RUNTIME_ARTIFACT_MANIFEST_SCHEMA_V2
    assert (
        SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1
        == authority.SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_SCHEMA_V1
    )
    assert RECEIPT_SECURITY_PROFILE_ID_V1 == authority.SPOT_SETTLEMENT_V7_RECEIPT_PROFILE_ID_V1

    rust_source = (REPO_ROOT / "zk/spot_settlement_v7_risc0/verifier/src/lib.rs").read_text(
        encoding="utf-8"
    )
    assert (
        _rust_string_constant(
            rust_source,
            "SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1",
        )
        == authority.SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_SCHEMA_V1
    )
    assert (
        _rust_string_constant(
            rust_source,
            "ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1",
        )
        == authority.SPOT_SETTLEMENT_V7_RECEIPT_PROFILE_ID_V1
    )


def test_manifest_hash_does_not_stand_in_for_candidate_identity() -> None:
    _, _, first_candidate_bytes, authority_bytes = _fixture()
    changed = _candidate_body_from_bytes(first_candidate_bytes)
    changed["source_build"]["source_commit"] = "33" * 20
    second_candidate_bytes = candidate.recompose_spot_v7_release_candidate_manifest_v1(changed)

    first = authority.check_exact_spot_v7_execution_authority_manifest_v1(
        exact_release_candidate_bytes=first_candidate_bytes,
        exact_authority_manifest_bytes=authority_bytes,
    )
    second = authority.check_exact_spot_v7_execution_authority_manifest_v1(
        exact_release_candidate_bytes=second_candidate_bytes,
        exact_authority_manifest_bytes=authority_bytes,
    )

    assert first.authority_manifest_sha256 == second.authority_manifest_sha256
    assert first.candidate_id != second.candidate_id
    assert first.candidate_manifest_sha256 != second.candidate_manifest_sha256
    assert first.candidate_identity_uniquely_determined is False


def test_runtime_raw_manifest_digest_and_semantic_artifact_set_are_independent_bindings() -> None:
    candidate_body, _, candidate_bytes, authority_bytes = _fixture()
    runtime_row = _inventory_row(candidate_body, "runtime_artifact_manifest")
    assert runtime_row["artifact_sha256"] != runtime_row["bound_identity"]

    raw_changed = _candidate_body_from_bytes(candidate_bytes)
    raw_row = _inventory_row(raw_changed, "runtime_artifact_manifest")
    raw_row["artifact_sha256"] = _digest(901)
    raw_candidate = candidate.recompose_spot_v7_release_candidate_manifest_v1(raw_changed)
    with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1) as raw_error:
        authority.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=raw_candidate,
            exact_authority_manifest_bytes=authority_bytes,
        )
    assert raw_error.value.code == "execution_authority_candidate_runtime_artifact_binding"

    semantic_changed = _candidate_body_from_bytes(candidate_bytes)
    semantic_row = _inventory_row(semantic_changed, "runtime_artifact_manifest")
    semantic_row["bound_identity"] = _digest(902)
    semantic_changed["runtime"]["artifact_set_id"] = _digest(902)
    semantic_candidate = candidate.recompose_spot_v7_release_candidate_manifest_v1(semantic_changed)
    with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1) as semantic_error:
        authority.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=semantic_candidate,
            exact_authority_manifest_bytes=authority_bytes,
        )
    assert semantic_error.value.code == "execution_authority_candidate_runtime_binding"


def test_authority_manifest_substitution_requires_candidate_rebinding() -> None:
    _, authority_body, candidate_bytes, authority_bytes = _fixture()
    changed = copy.deepcopy(authority_body)
    changed["artifacts"]["checkpoint_finality_checker_executable_sha256"] = _digest(603)
    substituted = authority.recompose_spot_v7_execution_authority_manifest_v1(changed)
    assert hashlib.sha256(substituted).digest() != hashlib.sha256(authority_bytes).digest()

    with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1) as captured:
        authority.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=candidate_bytes,
            exact_authority_manifest_bytes=substituted,
        )
    assert captured.value.code == "execution_authority_candidate_inventory_digest"


def test_coherent_authority_digest_edit_without_candidate_id_recomposition_rejects() -> None:
    _, authority_body, candidate_bytes, _ = _fixture()
    changed = copy.deepcopy(authority_body)
    changed["artifacts"]["checkpoint_finality_checker_manifest_sha256"] = _digest(604)
    substituted = authority.recompose_spot_v7_execution_authority_manifest_v1(changed)
    digest = hashlib.sha256(substituted).hexdigest()
    stale = json.loads(candidate_bytes)
    row = next(item for item in stale["evidence_inventory"] if item["role"] == "authority_manifest")
    row["artifact_sha256"] = digest
    row["bound_identity"] = digest
    row["size_bytes"] = len(substituted)
    stale["manifests"]["authority_manifest_sha256"] = digest

    with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1) as captured:
        authority.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=_canonical(stale),
            exact_authority_manifest_bytes=substituted,
        )
    assert captured.value.code == "execution_authority_release_candidate"


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        (
            lambda body: body["interfaces"].update(proof_verifier_output_schema="zenodex/wrong"),
            "execution_authority_interfaces",
        ),
        (
            lambda body: body["interfaces"].update(firecracker_runtime_profile_sha256="00" * 32),
            "execution_authority_interfaces",
        ),
        (
            lambda body: body["codecs"].update(machine_config="generic_json_v1"),
            "execution_authority_codecs",
        ),
        (
            lambda body: body["artifacts"].update(runtime_manifest_sha256="00" * 32),
            "execution_authority_artifacts",
        ),
        (
            lambda body: body["scope"].update(chain_id="/tmp/chain"),
            "execution_authority_scope",
        ),
        (
            lambda body: body["authority"].update(production_authority=True),
            "execution_authority_authority",
        ),
        (
            lambda body: body["authority"].update(production_authority=0),
            "execution_authority_authority",
        ),
        (
            lambda body: body["artifacts"].update(verifier_path="/tmp/untrusted-verifier"),
            "execution_authority_artifacts",
        ),
        (
            lambda body: body.update(candidate_id=_digest(701)),
            "execution_authority_fields",
        ),
    ),
)
def test_schema_profile_path_root_and_boolean_substitutions_reject(
    mutation: Callable[[dict[str, Any]], None],
    code: str,
) -> None:
    candidate_body = _candidate_body()
    body = _authority_body(candidate_body)
    mutation(body)
    with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1) as captured:
        authority.recompose_spot_v7_execution_authority_manifest_v1(body)
    assert captured.value.code == code


@pytest.mark.parametrize(
    "raw",
    (
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":"a","sch\\u0065ma":"b"}\n',
        b'{"format_flags":1.0}\n',
        b'{"format_flags":NaN}\n',
        b'{"a":{"b":{"c":{"d":1}}}}\n',
        b"{}",
        b"\xff",
    ),
)
def test_ambiguous_noncanonical_float_or_deep_json_rejects(raw: bytes) -> None:
    with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1):
        authority.parse_exact_spot_v7_execution_authority_manifest_v1(raw)


def test_every_candidate_mirrored_binding_has_a_negative_witness() -> None:
    _, _, candidate_bytes, authority_bytes = _fixture()
    candidate_document = json.loads(candidate_bytes)
    cases = (
        ("scope", "chain_id", "changed-chain"),
        ("scope", "domain_id", "changed-domain"),
        ("scope", "proof_profile_sha256", _digest(710)),
        ("scope", "receipt_security_profile_sha256", _digest(711)),
        ("lineage", "release_revision", 8),
        ("manifests", "verifier_manifest_sha256", _digest(712)),
        ("policies", "operational_policy_root", _digest(713)),
        ("policies", "data_availability_policy_root", _digest(714)),
        ("policies", "finality_policy_root", _digest(715)),
        ("runtime", "artifact_set_id", _digest(716)),
        ("runtime", "runtime_manifest_sha256", _digest(717)),
        ("runtime", "machine_config_sha256", _digest(718)),
        ("runtime", "firecracker_profile_sha256", _digest(719)),
        ("runtime", "root_supervisor_contract_sha256", _digest(720)),
        ("runtime", "root_supervisor_executable_sha256", _digest(721)),
    )
    for section, field, replacement in cases:
        changed = copy.deepcopy(candidate_document)
        changed[section][field] = replacement
        with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1):
            authority.check_exact_spot_v7_execution_authority_manifest_v1(
                exact_release_candidate_bytes=_canonical(changed),
                exact_authority_manifest_bytes=authority_bytes,
            )


def test_authority_inventory_size_codec_and_raw_digest_are_all_checked() -> None:
    _, _, candidate_bytes, authority_bytes = _fixture()
    baseline = json.loads(candidate_bytes)
    cases = (
        ("size_bytes", len(authority_bytes) + 1),
        ("codec", "opaque_bytes_v1"),
        ("artifact_sha256", _digest(801)),
        ("bound_identity", _digest(802)),
    )
    for field, replacement in cases:
        changed = copy.deepcopy(baseline)
        row = next(
            item for item in changed["evidence_inventory"] if item["role"] == "authority_manifest"
        )
        row[field] = replacement
        with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1):
            authority.check_exact_spot_v7_execution_authority_manifest_v1(
                exact_release_candidate_bytes=_canonical(changed),
                exact_authority_manifest_bytes=authority_bytes,
            )


def test_bounded_structure_preserving_boundary_atlas_is_stable() -> None:
    """Offline bug-discovery atlas; this is a regression corpus, not a proof."""

    baseline = _authority_body(_candidate_body())
    mutations: tuple[Callable[[dict[str, Any]], None], ...] = (
        lambda body: body.update(status="accepted"),
        lambda body: body.update(format_flags=2),
        lambda body: body["scope"].update(chain_id="../host"),
        lambda body: body.update(release_revision=True),
        lambda body: body["interfaces"].update(checkpoint_finality_checker_protocol_version=2),
        lambda body: body["codecs"].update(runtime_manifest="opaque_bytes_v1"),
        lambda body: body["artifacts"].update(machine_config_sha256="00" * 32),
        lambda body: body["policies"].update(finality_policy_root="00" * 32),
        lambda body: body["authority"].update(runtime_authority=True),
        lambda body: body.update(non_claims=[]),
        lambda body: body.update(reserved_u32=1),
    )
    frontier: list[dict[str, Any]] = []
    for first_index, first in enumerate(mutations):
        one_hop = copy.deepcopy(baseline)
        first(one_hop)
        frontier.append(one_hop)
        for second in mutations[first_index + 1 :]:
            two_hop = copy.deepcopy(one_hop)
            second(two_hop)
            frontier.append(two_hop)

    signatures = {_traced_reject_signature(body) for body in frontier}
    reject_codes = {code for code, _path in signatures}
    assert len(frontier) == 66
    assert len(reject_codes) >= 11
    assert len(signatures) >= 11


def _traced_reject_signature(body: dict[str, Any]) -> tuple[str, str]:
    visited: list[int] = []
    target = authority.__file__

    def tracer(frame: FrameType, event: str, _argument: object) -> Any:
        if event == "line" and frame.f_code.co_filename == target:
            visited.append(frame.f_lineno)
        return tracer

    previous = sys.gettrace()
    sys.settrace(tracer)
    try:
        with pytest.raises(authority.SpotV7ExecutionAuthorityManifestRejectV1) as captured:
            authority.recompose_spot_v7_execution_authority_manifest_v1(body)
    finally:
        sys.settrace(previous)
    path = ",".join(str(line) for line in visited).encode("ascii")
    return captured.value.code, hashlib.sha256(path).hexdigest()[:16]


def test_checked_descriptor_is_sealed_immutable_and_unserializable() -> None:
    _, _, candidate_bytes, authority_bytes = _fixture()
    checked = authority.check_exact_spot_v7_execution_authority_manifest_v1(
        exact_release_candidate_bytes=candidate_bytes,
        exact_authority_manifest_bytes=authority_bytes,
    )

    with pytest.raises(TypeError):
        authority.CheckedSpotV7ExecutionAuthorityManifestV1()  # type: ignore[call-arg]
    with pytest.raises(TypeError):
        checked.release_revision = 9  # type: ignore[misc]
    with pytest.raises(TypeError):
        copy.copy(checked)
    with pytest.raises(TypeError):
        copy.deepcopy(checked)
    with pytest.raises(TypeError):
        pickle.dumps(checked)


def test_same_interpreter_nominal_descriptor_forgery_cannot_promote_authority() -> None:
    """The Python seal is an API guard, not a hostile-interpreter capability."""

    _, _, candidate_bytes, authority_bytes = _fixture()
    legitimate = authority.check_exact_spot_v7_execution_authority_manifest_v1(
        exact_release_candidate_bytes=candidate_bytes,
        exact_authority_manifest_bytes=authority_bytes,
    )
    parsed = authority.parse_exact_spot_v7_execution_authority_manifest_v1(authority_bytes)
    forged = authority.CheckedSpotV7ExecutionAuthorityManifestV1(
        candidate_id=b"\xa5" * 32,
        candidate_manifest_sha256=b"\x5a" * 32,
        execution_manifest=parsed,
        seal=authority._CHECKED_CONSTRUCTION_SEAL_V1,
    )

    assert forged.candidate_id != legitimate.candidate_id
    assert forged.candidate_manifest_sha256 != legitimate.candidate_manifest_sha256
    assert forged.candidate_selected is False
    assert forged.candidate_current is False
    assert forged.component_artifacts_verified is False
    assert forged.finality_verified is False
    assert forged.live_execution_verified is False
    assert forged.candidate_identity_uniquely_determined is False
    assert forged.hostile_same_interpreter_resistance_established is False
    assert forged.release_authority is False
    assert forged.runtime_authority is False
    assert forged.settlement_authority is False
    assert forged.production_authority is False
    assert any(
        "same-interpreter code can forge nominal Python descriptors" in claim
        for claim in authority.NON_CLAIMS_V1
    )
