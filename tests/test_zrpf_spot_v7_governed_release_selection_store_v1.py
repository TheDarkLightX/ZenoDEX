from __future__ import annotations

import hashlib
import json
import os
import sqlite3
import threading
from pathlib import Path
from typing import Any, cast

import pytest

from tools import zrpf_spot_v7_governed_release_selection_store_v1 as store_module
from tools import zrpf_spot_v7_governed_release_selector_input_v1 as selector
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_module


def _position_bytes(index: int, *, size: int = 32) -> bytes:
    raw = bytes(
        ((index * 43) + (offset * 29) + (offset * offset * 5)) % 256 for offset in range(size)
    )
    assert raw != raw[::-1]
    assert any(raw)
    return raw


def _candidate_body(
    *,
    revision: int,
    parent_candidate_id: bytes | None,
    variant: int,
    activation_epoch: int = 0x0102_0304_0506,
    expiration_epoch: int | None = 0x1122_3344_5566,
) -> dict[str, Any]:
    inventory = []
    for index, role in enumerate(candidate_module.REQUIRED_EVIDENCE_ROLES_V1):
        artifact_sha256 = _position_bytes(index + 1 + (variant * 83)).hex()
        bound_identity = (
            artifact_sha256
            if role in candidate_module.RAW_ARTIFACT_DIGEST_ROLES_V1
            else _position_bytes(index + 41 + (variant * 83)).hex()
        )
        inventory.append(
            {
                "artifact_sha256": artifact_sha256,
                "bound_identity": bound_identity,
                "codec": candidate_module.EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1[role],
                "role": role,
                "size_bytes": 2_003 + (index * 307),
            }
        )
    digest_by_role = {row["role"]: row["bound_identity"] for row in inventory}
    return {
        "authority": {name: False for name in candidate_module.AUTHORITY_FIELDS_V1},
        "evidence_inventory": inventory,
        "format_flags": 1,
        "lineage": {
            "minimum_rollback_revision": 0 if revision == 1 else revision - 1,
            "parent_candidate_id": (
                None if parent_candidate_id is None else parent_candidate_id.hex()
            ),
            "proposed_activation_epoch": activation_epoch,
            "proposed_expiration_epoch": expiration_epoch,
            "release_revision": revision,
            "revocation_policy_root": digest_by_role["revocation_policy"],
            "revocation_record_root": None,
            "rollback_policy_root": digest_by_role["rollback_policy"],
        },
        "manifests": {
            "authority_manifest_sha256": digest_by_role["authority_manifest"],
            "replay_manifest_sha256": digest_by_role["replay_manifest"],
            "verifier_manifest_sha256": digest_by_role["verifier_manifest"],
        },
        "non_claims": list(candidate_module.NON_CLAIMS_V1),
        "policies": {
            "data_availability_policy_root": digest_by_role["data_availability_policy"],
            "finality_policy_root": digest_by_role["finality_policy"],
            "operational_policy_root": digest_by_role["operational_policy"],
        },
        "proofs": {
            "v6_image_id_root": digest_by_role["v6_image_identity_manifest"],
            "v6_journal_root": digest_by_role["v6_journal_bundle"],
            "v6_mutation_root": digest_by_role["v6_mutation_report"],
            "v6_program_root": digest_by_role["v6_program_bundle"],
            "v6_receipt_root": digest_by_role["v6_receipt_bundle"],
            "v7_image_id_root": digest_by_role["v7_image_identity_manifest"],
            "v7_journal_root": digest_by_role["v7_journal"],
            "v7_mutation_root": digest_by_role["v7_mutation_report"],
            "v7_program_root": digest_by_role["v7_program"],
            "v7_receipt_root": digest_by_role["v7_receipt"],
        },
        "reserved_u32": 0,
        "runtime": {
            "artifact_set_id": digest_by_role["runtime_artifact_manifest"],
            "authority_input_profile_sha256": digest_by_role["authority_input_profile"],
            "firecracker_profile_sha256": digest_by_role["firecracker_profile"],
            "machine_config_sha256": digest_by_role["machine_config"],
            "root_supervisor_contract_sha256": digest_by_role["root_supervisor_contract"],
            "root_supervisor_executable_sha256": digest_by_role["root_supervisor_executable"],
            "runtime_manifest_sha256": digest_by_role["runtime_manifest"],
        },
        "schema": candidate_module.SPOT_V7_RELEASE_CANDIDATE_MANIFEST_SCHEMA_V1,
        "scope": {
            "application_id": "zenodex",
            "chain_id": "tau-chain-314159",
            "domain_id": "spot-domain-271828",
            "proof_profile_sha256": digest_by_role["proof_profile"],
            "receipt_security_profile_sha256": digest_by_role["receipt_security_profile"],
            "release_profile": candidate_module.SPOT_V7_RELEASE_PROFILE_V1,
        },
        "source_build": {
            "build_container_manifest_sha256": digest_by_role["build_container_manifest"],
            "build_input_closure_root": digest_by_role["build_input_closure"],
            "source_closure_root": digest_by_role["source_closure"],
            "source_commit": _position_bytes(101 + variant, size=20).hex(),
            "source_tree": _position_bytes(121 + variant, size=20).hex(),
            "toolchain_manifest_sha256": digest_by_role["toolchain_manifest"],
        },
        "status": candidate_module.SPOT_V7_RELEASE_CANDIDATE_MANIFEST_STATUS_V1,
    }


def _checked_candidate(
    *,
    revision: int,
    parent_candidate_id: bytes | None,
    variant: int,
    activation_epoch: int = 0x0102_0304_0506,
    expiration_epoch: int | None = 0x1122_3344_5566,
) -> candidate_module.SpotV7ReleaseCandidateManifestV1:
    raw = candidate_module.recompose_spot_v7_release_candidate_manifest_v1(
        _candidate_body(
            revision=revision,
            parent_candidate_id=parent_candidate_id,
            variant=variant,
            activation_epoch=activation_epoch,
            expiration_epoch=expiration_epoch,
        )
    )
    parsed = candidate_module.parse_exact_spot_v7_release_candidate_manifest_v1(raw)
    return candidate_module.check_exact_spot_v7_release_candidate_manifest_v1(
        raw,
        expected_candidate_id=parsed.candidate_id,
    )


def _candidate_lineage(
    value: candidate_module.SpotV7ReleaseCandidateManifestV1,
) -> dict[str, Any]:
    document = cast(dict[str, Any], json.loads(value.canonical_bytes))
    return cast(dict[str, Any], document["lineage"])


def _selector_bytes(
    *,
    operation: selector.SelectorOperationV1,
    candidate: candidate_module.SpotV7ReleaseCandidateManifestV1,
    cursor: store_module.SpotV7ReleaseSelectionCursorV1,
    evaluation_epoch: int,
    nonce_index: int,
    revocation_registry_root: bytes,
    revocation_record_id: bytes | None = None,
) -> tuple[bytes, bytes]:
    lineage = _candidate_lineage(candidate)
    raw = selector.recompose_governed_release_selector_input_v1(
        operation=operation,
        expected_database_revision=cursor.database_revision,
        evaluation_epoch=evaluation_epoch,
        target_release_revision=candidate.release_revision,
        expected_current_candidate_id=cursor.current_candidate_id,
        expected_current_select_input_id=cursor.current_select_input_id,
        target_candidate_id=candidate.candidate_id,
        target_candidate_sha256=hashlib.sha256(candidate.canonical_bytes).digest(),
        rollback_policy_root=bytes.fromhex(lineage["rollback_policy_root"]),
        revocation_registry_root=revocation_registry_root,
        revocation_record_id=revocation_record_id,
        selector_nonce=_position_bytes(nonce_index),
    )
    return raw, selector.derive_governed_release_selector_input_id_v1(raw)


def _revocation_bytes(
    *,
    candidate: candidate_module.SpotV7ReleaseCandidateManifestV1,
    revocation_registry_root: bytes,
    effective_epoch: int,
    record_revision: int = 1,
    nonce_index: int = 240,
) -> tuple[bytes, bytes]:
    lineage = _candidate_lineage(candidate)
    raw = selector.recompose_spot_v7_revocation_record_v1(
        candidate_id=candidate.candidate_id,
        revocation_policy_root=bytes.fromhex(lineage["revocation_policy_root"]),
        revocation_registry_root=revocation_registry_root,
        effective_epoch=effective_epoch,
        record_revision=record_revision,
        reason_code=0x0102_0304,
        issuer_set_root=_position_bytes(230),
        record_nonce=_position_bytes(nonce_index),
    )
    return raw, selector.derive_spot_v7_revocation_record_id_v1(raw)


def _store(
    tmp_path: Path, name: str = "release-selection.sqlite3"
) -> store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1:
    os.chmod(tmp_path, 0o700)
    return store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1((tmp_path / name).resolve())


def _position_distinct_wire_cursor() -> store_module.SpotV7ReleaseSelectionCursorV1:
    return store_module.SpotV7ReleaseSelectionCursorV1(
        database_revision=0x0102_0304_0506_0708,
        state_root=store_module.GENESIS_SELECTION_STATE_ROOT_V1,
        last_evaluation_epoch=0x0102_0304_0506,
        current_candidate_id=_position_bytes(171),
        current_candidate_sha256=_position_bytes(172),
        current_release_revision=0x0102_0304,
        current_select_input_id=_position_bytes(173),
        current_scope_id=_position_bytes(174),
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _commit_genesis(
    store: store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1,
    *,
    variant: int = 0,
    evaluation_epoch: int = 0x0102_0304_0506,
) -> tuple[
    candidate_module.SpotV7ReleaseCandidateManifestV1,
    bytes,
    bytes,
    store_module.SpotV7ReleaseSelectionResultV1,
]:
    candidate = _checked_candidate(
        revision=1,
        parent_candidate_id=None,
        variant=variant,
    )
    registry_root = _position_bytes(180 + variant)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=evaluation_epoch,
        nonce_index=200 + variant,
        revocation_registry_root=registry_root,
    )
    result = store.select(
        candidate=candidate,
        selector_input_bytes=raw,
        expected_selector_input_id=input_id,
    )
    return candidate, raw, input_id, result


def test_fixed_selector_and_revocation_fixtures_are_position_distinct() -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    cursor = _position_distinct_wire_cursor()
    registry_root = _position_bytes(180)
    record_raw, record_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=registry_root,
        effective_epoch=0x0102_0304_0506,
    )
    select_raw, select_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=200,
        revocation_registry_root=registry_root,
    )
    revoke_raw, revoke_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=0x1122_3344_5566,
        nonce_index=201,
        revocation_registry_root=registry_root,
        revocation_record_id=record_id,
    )

    assert len(select_raw) == 320
    assert len(revoke_raw) == 320
    assert len(record_raw) == 216
    assert hashlib.sha256(select_raw).hexdigest() == (
        "4eca7799c12b71bd1da20c85b37d46717d0dfad330a85ef41989dfbaddc989a0"
    )
    assert select_id.hex() == ("e45975bc8639b7781a066b2e45fde185821a688635546ffaa337cd2d49ad6d09")
    assert hashlib.sha256(revoke_raw).hexdigest() == (
        "7e2cbeaef02f03ed46414564586254110d5936f325af39e7c46d7c49fddbde50"
    )
    assert revoke_id.hex() == ("53a19332cbce4f2eb83c8bd79047eb4f0c9fa521778cd64e3f4a69c35eab0c47")
    assert hashlib.sha256(record_raw).hexdigest() == (
        "5ac6ef420430e06c587b2a6a41410290e52b5f769fc9767821e0f4cc19d8251c"
    )
    assert record_id.hex() == ("863d4cd5ddcdfc70cbee2431d5ffe4cdd18d33127ff3f7f99fa15cc7e168fd43")
    select_digests = [select_raw[offset : offset + 32] for offset in range(60, 316, 32)]
    revoke_digests = [revoke_raw[offset : offset + 32] for offset in range(60, 316, 32)]
    record_digests = [record_raw[offset : offset + 32] for offset in (32, 64, 96, 152, 184)]
    assert select_digests[6] == selector.ZERO_DIGEST_V1
    select_nonzero = [value for value in select_digests if value != selector.ZERO_DIGEST_V1]
    assert len(set(select_nonzero)) == len(select_nonzero)
    assert len(set(revoke_digests)) == len(revoke_digests)
    assert len(set(record_digests)) == len(record_digests)
    assert all(value != value[::-1] for value in select_nonzero)
    assert all(value != value[::-1] for value in revoke_digests)
    assert all(value != value[::-1] for value in record_digests)


@pytest.mark.parametrize(
    "operation", (selector.SelectorOperationV1.SELECT, selector.SelectorOperationV1.REVOKE)
)
def test_every_selector_byte_is_an_active_distinguishing_witness(
    operation: selector.SelectorOperationV1,
) -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    cursor = _position_distinct_wire_cursor()
    registry_root = _position_bytes(180)
    record_raw, record_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=registry_root,
        effective_epoch=0x0102_0304_0506,
    )
    del record_raw
    raw, baseline_id = _selector_bytes(
        operation=operation,
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=0x1122_3344_5566,
        nonce_index=200 + int(operation),
        revocation_registry_root=registry_root,
        revocation_record_id=(
            None if operation is selector.SelectorOperationV1.SELECT else record_id
        ),
    )
    for index in range(len(raw)):
        mutated = bytearray(raw)
        mutated[index] ^= 0x01
        mutated_raw = bytes(mutated)
        with pytest.raises(selector.SpotV7SelectorInputRejectV1) as captured:
            selector.parse_exact_governed_release_selector_input_v1(
                mutated_raw,
                expected_input_id=baseline_id,
            )
        assert captured.value.code.startswith("selector_"), index


def test_every_revocation_record_byte_is_an_active_distinguishing_witness() -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, baseline_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=_position_bytes(180),
        effective_epoch=0x0102_0304_0506,
    )
    for index in range(len(raw)):
        mutated = bytearray(raw)
        mutated[index] ^= 0x01
        mutated_raw = bytes(mutated)
        with pytest.raises(selector.SpotV7SelectorInputRejectV1) as captured:
            selector.parse_exact_spot_v7_revocation_record_v1(
                mutated_raw,
                expected_record_id=baseline_id,
            )
        assert captured.value.code.startswith("revocation_"), index


def test_zero_selector_nonce_rejects_after_identity_rebinding() -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, _input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=_position_distinct_wire_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=200,
        revocation_registry_root=_position_bytes(180),
    )
    rebound_raw = raw[:284] + selector.ZERO_DIGEST_V1 + raw[316:]
    with pytest.raises(selector.SpotV7SelectorInputRejectV1) as captured:
        selector.parse_exact_governed_release_selector_input_v1(
            rebound_raw,
            expected_input_id=selector.derive_governed_release_selector_input_id_v1(rebound_raw),
        )
    assert captured.value.code == "selector_nonce"


@pytest.mark.parametrize(
    ("start", "size", "expected_code"),
    (
        (136, 8, "revocation_record_revision"),
        (144, 4, "revocation_reason_code"),
        (152, 32, "revocation_issuer_set_root"),
        (184, 32, "revocation_record_nonce"),
    ),
)
def test_zero_revocation_semantic_fields_reject_after_identity_rebinding(
    start: int,
    size: int,
    expected_code: str,
) -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, _record_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=_position_bytes(180),
        effective_epoch=0x0102_0304_0506,
    )
    rebound_raw = raw[:start] + (b"\x00" * size) + raw[start + size :]
    with pytest.raises(selector.SpotV7SelectorInputRejectV1) as captured:
        selector.parse_exact_spot_v7_revocation_record_v1(
            rebound_raw,
            expected_record_id=selector.derive_spot_v7_revocation_record_id_v1(rebound_raw),
        )
    assert captured.value.code == expected_code


@pytest.mark.parametrize(
    ("start", "replacement", "expected_code"),
    (
        (52, (2).to_bytes(8, "big"), "CANDIDATE_RELEASE_REVISION_MISMATCH"),
        (
            124,
            _position_bytes(251),
            "CANONICAL_INPUT_REJECTED:release_candidate_expected_id",
        ),
        (156, _position_bytes(252), "CANDIDATE_CANONICAL_SHA256_MISMATCH"),
        (188, _position_bytes(253), "ROLLBACK_POLICY_ROOT_MISMATCH"),
    ),
)
def test_rebound_selector_semantic_fields_reach_distinct_reject_boundaries(
    tmp_path: Path,
    start: int,
    replacement: bytes,
    expected_code: str,
) -> None:
    store = _store(tmp_path)
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, _input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=200,
        revocation_registry_root=_position_bytes(180),
    )
    end = start + len(replacement)
    rebound_raw = raw[:start] + replacement + raw[end:]
    rebound_id = selector.derive_governed_release_selector_input_id_v1(rebound_raw)

    result = store.select(
        candidate=candidate,
        selector_input_bytes=rebound_raw,
        expected_selector_input_id=rebound_id,
    )

    assert result.code == expected_code
    assert store.read_cursor().database_revision == 0


def test_selector_flags_reserved_endian_and_swaps_are_active() -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    cursor = _position_distinct_wire_cursor()
    raw, baseline_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=200,
        revocation_registry_root=_position_bytes(180),
    )
    for offset in (28, 32, 316):
        for bit in range(32):
            mutated = bytearray(raw)
            mutated[offset + (3 - (bit // 8))] ^= 1 << (bit % 8)
            mutated_raw = bytes(mutated)
            with pytest.raises(selector.SpotV7SelectorInputRejectV1):
                selector.parse_exact_governed_release_selector_input_v1(
                    mutated_raw,
                    expected_input_id=selector.derive_governed_release_selector_input_id_v1(
                        mutated_raw
                    ),
                )
    for offset, field_name in (
        (36, "expected_database_revision"),
        (44, "evaluation_epoch"),
        (52, "target_release_revision"),
    ):
        endian_mutated = raw[:offset] + raw[offset : offset + 8][::-1] + raw[offset + 8 :]
        parsed = selector.parse_exact_governed_release_selector_input_v1(
            endian_mutated,
            expected_input_id=selector.derive_governed_release_selector_input_id_v1(endian_mutated),
        )
        assert parsed.input_id != baseline_id
        assert getattr(parsed, field_name) == int.from_bytes(
            endian_mutated[offset : offset + 8], "big"
        )
        assert getattr(parsed, field_name) != int.from_bytes(raw[offset : offset + 8], "big")
    swapped = bytearray(raw)
    swapped[156:188], swapped[188:220] = raw[188:220], raw[156:188]
    swapped_raw = bytes(swapped)
    parsed = selector.parse_exact_governed_release_selector_input_v1(
        swapped_raw,
        expected_input_id=selector.derive_governed_release_selector_input_id_v1(swapped_raw),
    )
    assert parsed.input_id != baseline_id
    assert parsed.target_candidate_sha256 == raw[188:220]
    assert parsed.rollback_policy_root == raw[156:188]


def test_revocation_flags_reserved_endian_and_swaps_are_active() -> None:
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, baseline_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=_position_bytes(180),
        effective_epoch=0x0102_0304_0506_0708,
        record_revision=0x1122_3344_5566_7788,
    )
    for offset in (24, 28, 148):
        for bit in range(32):
            mutated = bytearray(raw)
            mutated[offset + (3 - (bit // 8))] ^= 1 << (bit % 8)
            mutated_raw = bytes(mutated)
            with pytest.raises(selector.SpotV7SelectorInputRejectV1):
                selector.parse_exact_spot_v7_revocation_record_v1(
                    mutated_raw,
                    expected_record_id=selector.derive_spot_v7_revocation_record_id_v1(mutated_raw),
                )
    for offset, field_name in (
        (128, "effective_epoch"),
        (136, "record_revision"),
    ):
        endian_mutated = raw[:offset] + raw[offset : offset + 8][::-1] + raw[offset + 8 :]
        parsed = selector.parse_exact_spot_v7_revocation_record_v1(
            endian_mutated,
            expected_record_id=selector.derive_spot_v7_revocation_record_id_v1(endian_mutated),
        )
        assert parsed.record_id != baseline_id
        assert getattr(parsed, field_name) == int.from_bytes(
            endian_mutated[offset : offset + 8], "big"
        )
        assert getattr(parsed, field_name) != int.from_bytes(raw[offset : offset + 8], "big")
    swapped = bytearray(raw)
    swapped[64:96], swapped[96:128] = raw[96:128], raw[64:96]
    swapped_raw = bytes(swapped)
    parsed = selector.parse_exact_spot_v7_revocation_record_v1(
        swapped_raw,
        expected_record_id=selector.derive_spot_v7_revocation_record_id_v1(swapped_raw),
    )
    assert parsed.record_id != baseline_id
    assert parsed.revocation_policy_root == raw[96:128]
    assert parsed.revocation_registry_root == raw[64:96]


def test_genesis_selection_commits_atomically_and_remains_authority_false(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate, _raw, _input_id, result = _commit_genesis(store)

    assert result.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert result.code == "SELECT_COMMITTED"
    assert result.cursor.database_revision == 1
    assert result.cursor.current_candidate_id == candidate.candidate_id
    assert result.cursor.current_release_revision == 1
    assert result.cursor.current_revoked is False
    assert result.candidate_selected is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.runtime_authority is False
    assert result.production_authority is False
    assert result.cursor.candidate_current is False
    assert result.cursor.release_authority is False

    restarted = store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1(store.path)
    assert restarted.read_cursor() == result.cursor
    assert stat_mode(store.path) == 0o600


def stat_mode(path: Path) -> int:
    return path.stat().st_mode & 0o777


@pytest.mark.parametrize(
    "forged_field",
    (
        "candidate_id",
        "evidence_inventory_root",
        "release_revision",
        "parent_candidate_id",
    ),
)
def test_store_reparses_candidate_and_rejects_each_forged_derived_field(
    tmp_path: Path,
    forged_field: str,
) -> None:
    store = _store(tmp_path)
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=200,
        revocation_registry_root=_position_bytes(180),
    )
    forged = object.__new__(candidate_module.SpotV7ReleaseCandidateManifestV1)
    object.__setattr__(forged, "canonical_bytes", candidate.canonical_bytes)
    object.__setattr__(forged, "evidence_inventory_root", candidate.evidence_inventory_root)
    object.__setattr__(forged, "candidate_id", candidate.candidate_id)
    object.__setattr__(forged, "release_revision", candidate.release_revision)
    object.__setattr__(forged, "parent_candidate_id", candidate.parent_candidate_id)
    forged_value: object
    if forged_field == "release_revision":
        forged_value = candidate.release_revision + 1
    else:
        forged_value = _position_bytes(250)
    object.__setattr__(forged, forged_field, forged_value)

    result = store.select(
        candidate=forged,
        selector_input_bytes=raw,
        expected_selector_input_id=input_id,
    )
    assert result.disposition is store_module.ReleaseSelectionDispositionV1.REJECTED
    assert result.code == "CANDIDATE_NOMINAL_BINDING_MISMATCH"
    assert store.read_cursor().database_revision == 0


def test_forward_selection_and_exact_replays_are_idempotent(tmp_path: Path) -> None:
    store = _store(tmp_path)
    first, first_raw, first_id, first_result = _commit_genesis(store)
    replay = store.select(
        candidate=first,
        selector_input_bytes=first_raw,
        expected_selector_input_id=first_id,
    )
    assert replay.disposition is store_module.ReleaseSelectionDispositionV1.IDEMPOTENT
    assert replay.cursor == first_result.cursor

    second = _checked_candidate(
        revision=2,
        parent_candidate_id=first.candidate_id,
        variant=1,
    )
    second_raw, second_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=second,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0507,
        nonce_index=201,
        revocation_registry_root=_position_bytes(181),
    )
    committed = store.select(
        candidate=second,
        selector_input_bytes=second_raw,
        expected_selector_input_id=second_id,
    )
    assert committed.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert committed.cursor.current_release_revision == 2

    replay_after_advance = store.select(
        candidate=first,
        selector_input_bytes=first_raw,
        expected_selector_input_id=first_id,
    )
    assert replay_after_advance.disposition is store_module.ReleaseSelectionDispositionV1.IDEMPOTENT
    assert replay_after_advance.cursor == committed.cursor


@pytest.mark.parametrize(
    ("evaluation_epoch", "expected_code"),
    (
        (0x0102_0304_0505, "CANDIDATE_NOT_ACTIVE"),
        (0x1122_3344_5566, "CANDIDATE_EXPIRED"),
    ),
)
def test_activation_window_rejects_without_mutation(
    tmp_path: Path,
    evaluation_epoch: int,
    expected_code: str,
) -> None:
    store = _store(tmp_path)
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=evaluation_epoch,
        nonce_index=200,
        revocation_registry_root=_position_bytes(180),
    )
    result = store.select(
        candidate=candidate,
        selector_input_bytes=raw,
        expected_selector_input_id=input_id,
    )
    assert result.disposition is store_module.ReleaseSelectionDispositionV1.REJECTED
    assert result.code == expected_code
    assert result.cursor.database_revision == 0


def test_evaluation_epoch_is_nondecreasing_across_committed_events(tmp_path: Path) -> None:
    store = _store(tmp_path)
    first, _raw, _input_id, _result = _commit_genesis(store)
    current = store.read_cursor()
    assert current.last_evaluation_epoch == 0x0102_0304_0506
    second = _checked_candidate(
        revision=2,
        parent_candidate_id=first.candidate_id,
        variant=1,
        activation_epoch=0,
    )
    earlier_raw, earlier_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=second,
        cursor=current,
        evaluation_epoch=0x0102_0304_0505,
        nonce_index=201,
        revocation_registry_root=_position_bytes(181),
    )
    earlier = store.select(
        candidate=second,
        selector_input_bytes=earlier_raw,
        expected_selector_input_id=earlier_id,
    )
    assert earlier.code == "EVALUATION_EPOCH_ROLLBACK_REJECTED"
    assert store.read_cursor() == current

    equal_raw, equal_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=second,
        cursor=current,
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=202,
        revocation_registry_root=_position_bytes(182),
    )
    equal = store.select(
        candidate=second,
        selector_input_bytes=equal_raw,
        expected_selector_input_id=equal_id,
    )
    assert equal.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert equal.cursor.last_evaluation_epoch == current.last_evaluation_epoch


def test_fork_rollback_gap_and_stale_cas_reject_without_mutation(tmp_path: Path) -> None:
    store = _store(tmp_path)
    first, _raw, _input_id, _result = _commit_genesis(store)
    cursor_one = store.read_cursor()
    second = _checked_candidate(revision=2, parent_candidate_id=first.candidate_id, variant=1)
    second_raw, second_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=second,
        cursor=cursor_one,
        evaluation_epoch=0x0102_0304_0507,
        nonce_index=201,
        revocation_registry_root=_position_bytes(181),
    )
    committed = store.select(
        candidate=second,
        selector_input_bytes=second_raw,
        expected_selector_input_id=second_id,
    )
    assert committed.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    stable = store.read_cursor()

    rollback_raw, rollback_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=first,
        cursor=stable,
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=202,
        revocation_registry_root=_position_bytes(182),
    )
    rollback = store.select(
        candidate=first,
        selector_input_bytes=rollback_raw,
        expected_selector_input_id=rollback_id,
    )
    assert rollback.code == "RELEASE_ROLLBACK_REJECTED"

    fork = _checked_candidate(revision=2, parent_candidate_id=first.candidate_id, variant=2)
    fork_raw, fork_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=fork,
        cursor=cursor_one,
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=203,
        revocation_registry_root=_position_bytes(183),
    )
    fork_result = store.select(
        candidate=fork,
        selector_input_bytes=fork_raw,
        expected_selector_input_id=fork_id,
    )
    assert fork_result.code == "RELEASE_FORK_REJECTED"

    gap = _checked_candidate(revision=4, parent_candidate_id=second.candidate_id, variant=3)
    gap_raw, gap_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=gap,
        cursor=stable,
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=204,
        revocation_registry_root=_position_bytes(184),
    )
    gap_result = store.select(
        candidate=gap,
        selector_input_bytes=gap_raw,
        expected_selector_input_id=gap_id,
    )
    assert gap_result.code == "RELEASE_REVISION_GAP"

    third = _checked_candidate(revision=3, parent_candidate_id=second.candidate_id, variant=4)
    stale_raw, stale_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=third,
        cursor=cursor_one,
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=205,
        revocation_registry_root=_position_bytes(185),
    )
    stale = store.select(
        candidate=third,
        selector_input_bytes=stale_raw,
        expected_selector_input_id=stale_id,
    )
    assert stale.code == "DATABASE_REVISION_CAS_MISMATCH"
    assert store.read_cursor() == stable


@pytest.mark.parametrize(
    ("wrong_candidate", "wrong_selection", "expected_code"),
    (
        (True, False, "CURRENT_CANDIDATE_CAS_MISMATCH"),
        (False, True, "CURRENT_SELECTION_CAS_MISMATCH"),
    ),
)
def test_each_current_head_cas_component_is_independently_load_bearing(
    tmp_path: Path,
    wrong_candidate: bool,
    wrong_selection: bool,
    expected_code: str,
) -> None:
    store = _store(tmp_path)
    first, _raw, _input_id, _result = _commit_genesis(store)
    current = store.read_cursor()
    second = _checked_candidate(
        revision=2,
        parent_candidate_id=first.candidate_id,
        variant=1,
    )
    claimed_cursor = store_module.SpotV7ReleaseSelectionCursorV1(
        database_revision=current.database_revision,
        state_root=current.state_root,
        last_evaluation_epoch=current.last_evaluation_epoch,
        current_candidate_id=(
            _position_bytes(251) if wrong_candidate else current.current_candidate_id
        ),
        current_candidate_sha256=current.current_candidate_sha256,
        current_release_revision=current.current_release_revision,
        current_select_input_id=(
            _position_bytes(252) if wrong_selection else current.current_select_input_id
        ),
        current_scope_id=current.current_scope_id,
        current_revoked=False,
        current_revocation_record_id=None,
    )
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=second,
        cursor=claimed_cursor,
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=222,
        revocation_registry_root=_position_bytes(202),
    )
    result = store.select(
        candidate=second,
        selector_input_bytes=raw,
        expected_selector_input_id=input_id,
    )
    assert result.code == expected_code
    assert store.read_cursor() == current


def test_select_and_revoke_tags_cannot_cross_api_boundaries(tmp_path: Path) -> None:
    store = _store(tmp_path)
    current = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    registry_root = _position_bytes(190)
    record_raw, record_id = _revocation_bytes(
        candidate=current,
        revocation_registry_root=registry_root,
        effective_epoch=0x0102_0304_0506,
    )
    revoke_raw, revoke_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=210,
        revocation_registry_root=registry_root,
        revocation_record_id=record_id,
    )
    wrong_select = store.select(
        candidate=current,
        selector_input_bytes=revoke_raw,
        expected_selector_input_id=revoke_id,
    )
    assert wrong_select.code == "SELECTOR_OPERATION_MISMATCH"

    select_raw, select_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=current,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=211,
        revocation_registry_root=registry_root,
    )
    wrong_revoke = store.revoke(
        candidate=current,
        selector_input_bytes=select_raw,
        expected_selector_input_id=select_id,
        revocation_record_bytes=record_raw,
        expected_revocation_record_id=record_id,
    )
    assert wrong_revoke.code == "SELECTOR_OPERATION_MISMATCH"
    assert store.read_cursor().database_revision == 0


def test_revocation_is_terminal_precedent_and_exact_replay_is_idempotent(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    current, _raw, _input_id, _result = _commit_genesis(store)
    registry_root = _position_bytes(190)
    record_raw, record_id = _revocation_bytes(
        candidate=current,
        revocation_registry_root=registry_root,
        effective_epoch=0x0102_0304_0507,
    )
    revoke_raw, revoke_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=210,
        revocation_registry_root=registry_root,
        revocation_record_id=record_id,
    )
    revoked = store.revoke(
        candidate=current,
        selector_input_bytes=revoke_raw,
        expected_selector_input_id=revoke_id,
        revocation_record_bytes=record_raw,
        expected_revocation_record_id=record_id,
    )
    assert revoked.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert revoked.code == "REVOKE_COMMITTED"
    assert revoked.cursor.current_revoked is True
    assert revoked.cursor.current_revocation_record_id == record_id
    assert revoked.revocation_authority is False

    replay = store.revoke(
        candidate=current,
        selector_input_bytes=revoke_raw,
        expected_selector_input_id=revoke_id,
        revocation_record_bytes=record_raw,
        expected_revocation_record_id=record_id,
    )
    assert replay.disposition is store_module.ReleaseSelectionDispositionV1.IDEMPOTENT
    assert replay.cursor == revoked.cursor

    conflicting_record, conflicting_id = _revocation_bytes(
        candidate=current,
        revocation_registry_root=registry_root,
        effective_epoch=0x0102_0304_0507,
        record_revision=2,
        nonce_index=241,
    )
    conflicting_raw, conflicting_input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0509,
        nonce_index=211,
        revocation_registry_root=registry_root,
        revocation_record_id=conflicting_id,
    )
    conflict = store.revoke(
        candidate=current,
        selector_input_bytes=conflicting_raw,
        expected_selector_input_id=conflicting_input_id,
        revocation_record_bytes=conflicting_record,
        expected_revocation_record_id=conflicting_id,
    )
    assert conflict.code == "REVOCATION_CONFLICT"

    successor = _checked_candidate(revision=2, parent_candidate_id=current.candidate_id, variant=1)
    successor_raw, successor_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=successor,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0510,
        nonce_index=212,
        revocation_registry_root=_position_bytes(191),
    )
    blocked = store.select(
        candidate=successor,
        selector_input_bytes=successor_raw,
        expected_selector_input_id=successor_id,
    )
    assert blocked.code == "CURRENT_HEAD_REVOKED"
    assert store.read_cursor() == revoked.cursor

    restarted = store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1(store.path)
    assert restarted.read_cursor() == revoked.cursor


def test_select_then_revoke_at_same_epoch_uses_database_revision_total_order(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    current, _raw, _input_id, selected = _commit_genesis(store)
    selected_root = selected.cursor.state_root
    same_epoch = cast(int, selected.cursor.last_evaluation_epoch)
    registry_root = _position_bytes(190)
    record_raw, record_id = _revocation_bytes(
        candidate=current,
        revocation_registry_root=registry_root,
        effective_epoch=same_epoch,
    )
    revoke_raw, revoke_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=selected.cursor,
        evaluation_epoch=same_epoch,
        nonce_index=215,
        revocation_registry_root=registry_root,
        revocation_record_id=record_id,
    )
    revoked = store.revoke(
        candidate=current,
        selector_input_bytes=revoke_raw,
        expected_selector_input_id=revoke_id,
        revocation_record_bytes=record_raw,
        expected_revocation_record_id=record_id,
    )

    assert revoked.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert revoked.cursor.database_revision == selected.cursor.database_revision + 1
    assert revoked.cursor.last_evaluation_epoch == same_epoch
    assert revoked.cursor.state_root != selected_root
    assert revoked.cursor.current_revoked is True


def test_future_or_wrong_policy_revocation_rejects_without_mutation(tmp_path: Path) -> None:
    store = _store(tmp_path)
    current, _raw, _input_id, _result = _commit_genesis(store)
    stable = store.read_cursor()
    registry_root = _position_bytes(190)
    future_record, future_id = _revocation_bytes(
        candidate=current,
        revocation_registry_root=registry_root,
        effective_epoch=0x1122_3344_5566,
    )
    revoke_raw, revoke_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=stable,
        evaluation_epoch=0x0102_0304_0508,
        nonce_index=210,
        revocation_registry_root=registry_root,
        revocation_record_id=future_id,
    )
    future = store.revoke(
        candidate=current,
        selector_input_bytes=revoke_raw,
        expected_selector_input_id=revoke_id,
        revocation_record_bytes=future_record,
        expected_revocation_record_id=future_id,
    )
    assert future.code == "FUTURE_REVOCATION_REJECTED"

    wrong_policy = bytearray(future_record)
    wrong_policy[64:96] = _position_bytes(245)
    wrong_policy_raw = bytes(wrong_policy)
    wrong_policy_id = selector.derive_spot_v7_revocation_record_id_v1(wrong_policy_raw)
    wrong_revoke_raw, wrong_revoke_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=stable,
        evaluation_epoch=0x1122_3344_5567,
        nonce_index=211,
        revocation_registry_root=registry_root,
        revocation_record_id=wrong_policy_id,
    )
    wrong = store.revoke(
        candidate=current,
        selector_input_bytes=wrong_revoke_raw,
        expected_selector_input_id=wrong_revoke_id,
        revocation_record_bytes=wrong_policy_raw,
        expected_revocation_record_id=wrong_policy_id,
    )
    assert wrong.code == "REVOCATION_POLICY_ROOT_MISMATCH"

    wrong_registry_selector = bytearray(revoke_raw)
    wrong_registry_selector[220:252] = _position_bytes(246)
    wrong_registry_raw = bytes(wrong_registry_selector)
    wrong_registry_id = selector.derive_governed_release_selector_input_id_v1(wrong_registry_raw)
    wrong_registry = store.revoke(
        candidate=current,
        selector_input_bytes=wrong_registry_raw,
        expected_selector_input_id=wrong_registry_id,
        revocation_record_bytes=future_record,
        expected_revocation_record_id=future_id,
    )
    assert wrong_registry.code == "REVOCATION_REGISTRY_ROOT_MISMATCH"
    assert store.read_cursor() == stable


def test_rebound_wrong_revocation_candidate_and_selector_record_id_reject(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    current, _raw, _input_id, _result = _commit_genesis(store)
    stable = store.read_cursor()
    registry_root = _position_bytes(190)
    record_raw, record_id = _revocation_bytes(
        candidate=current,
        revocation_registry_root=registry_root,
        effective_epoch=0x0102_0304_0506,
    )

    wrong_candidate_record = record_raw[:32] + _position_bytes(247) + record_raw[64:]
    wrong_candidate_id = selector.derive_spot_v7_revocation_record_id_v1(wrong_candidate_record)
    wrong_candidate_selector, wrong_candidate_selector_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=stable,
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=213,
        revocation_registry_root=registry_root,
        revocation_record_id=wrong_candidate_id,
    )
    wrong_candidate = store.revoke(
        candidate=current,
        selector_input_bytes=wrong_candidate_selector,
        expected_selector_input_id=wrong_candidate_selector_id,
        revocation_record_bytes=wrong_candidate_record,
        expected_revocation_record_id=wrong_candidate_id,
    )
    assert wrong_candidate.code == "REVOCATION_CANDIDATE_MISMATCH"

    mismatched_record_id = _position_bytes(248)
    mismatched_selector, mismatched_selector_id = _selector_bytes(
        operation=selector.SelectorOperationV1.REVOKE,
        candidate=current,
        cursor=stable,
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=214,
        revocation_registry_root=registry_root,
        revocation_record_id=mismatched_record_id,
    )
    mismatch = store.revoke(
        candidate=current,
        selector_input_bytes=mismatched_selector,
        expected_selector_input_id=mismatched_selector_id,
        revocation_record_bytes=record_raw,
        expected_revocation_record_id=record_id,
    )
    assert mismatch.code == "REVOCATION_RECORD_INPUT_BINDING_MISMATCH"
    assert store.read_cursor() == stable


def test_two_concurrent_fork_candidates_commit_exactly_one(tmp_path: Path) -> None:
    store = _store(tmp_path)
    first, _raw, _input_id, _result = _commit_genesis(store)
    initial = store.read_cursor()
    candidates = [
        _checked_candidate(
            revision=2,
            parent_candidate_id=first.candidate_id,
            variant=variant,
        )
        for variant in (1, 2)
    ]
    inputs = [
        _selector_bytes(
            operation=selector.SelectorOperationV1.SELECT,
            candidate=value,
            cursor=initial,
            evaluation_epoch=0x0102_0304_0508,
            nonce_index=220 + index,
            revocation_registry_root=_position_bytes(200 + index),
        )
        for index, value in enumerate(candidates)
    ]
    barrier = threading.Barrier(3)
    results: list[store_module.SpotV7ReleaseSelectionResultV1] = []

    def worker(index: int) -> None:
        barrier.wait()
        raw, input_id = inputs[index]
        result = store.select(
            candidate=candidates[index],
            selector_input_bytes=raw,
            expected_selector_input_id=input_id,
        )
        results.append(result)

    threads = [threading.Thread(target=worker, args=(index,)) for index in range(2)]
    for thread in threads:
        thread.start()
    barrier.wait()
    for thread in threads:
        thread.join()

    assert len(results) == 2
    assert (
        sum(
            result.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
            for result in results
        )
        == 1
    )
    assert (
        sum(
            result.disposition is store_module.ReleaseSelectionDispositionV1.REJECTED
            for result in results
        )
        == 1
    )
    assert store.read_cursor().database_revision == 2


def test_read_cursor_uses_one_snapshot_across_meta_and_event_reads(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=initial,
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=220,
        revocation_registry_root=_position_bytes(200),
    )
    reader_between_queries = threading.Event()
    writer_precommit = threading.Event()
    writer_committed = threading.Event()
    original_read_all_events = store_module._read_all_events
    original_cas_meta = store_module._cas_meta
    original_fsync_directory = store_module._fsync_directory
    reader_results: list[store_module.SpotV7ReleaseSelectionCursorV1] = []
    writer_results: list[store_module.SpotV7ReleaseSelectionResultV1] = []
    errors: list[BaseException] = []

    def interleaved_read_all_events(connection: sqlite3.Connection) -> list[sqlite3.Row]:
        if threading.current_thread().name == "snapshot-reader":
            reader_between_queries.set()
            if not writer_precommit.wait(timeout=5):
                raise AssertionError("writer did not reach precommit state")
            if not connection.in_transaction and not writer_committed.wait(timeout=5):
                raise AssertionError("writer did not commit in the non-snapshot control")
        return original_read_all_events(connection)

    def signal_precommit(
        connection: sqlite3.Connection,
        previous: store_module.SpotV7ReleaseSelectionCursorV1,
        result: store_module.SpotV7ReleaseSelectionCursorV1,
    ) -> None:
        original_cas_meta(connection, previous, result)
        writer_precommit.set()

    def signal_committed(path: Path) -> None:
        original_fsync_directory(path)
        writer_committed.set()

    monkeypatch.setattr(store_module, "_read_all_events", interleaved_read_all_events)
    monkeypatch.setattr(store_module, "_cas_meta", signal_precommit)
    monkeypatch.setattr(store_module, "_fsync_directory", signal_committed)

    def reader() -> None:
        try:
            reader_results.append(store.read_cursor())
        except BaseException as exc:  # pragma: no cover - asserted below
            errors.append(exc)

    def writer() -> None:
        try:
            writer_results.append(
                store.select(
                    candidate=candidate,
                    selector_input_bytes=raw,
                    expected_selector_input_id=input_id,
                )
            )
        except BaseException as exc:  # pragma: no cover - asserted below
            errors.append(exc)

    reader_thread = threading.Thread(target=reader, name="snapshot-reader")
    reader_thread.start()
    assert reader_between_queries.wait(timeout=5)
    writer_thread = threading.Thread(target=writer, name="snapshot-writer")
    writer_thread.start()
    reader_thread.join(timeout=5)
    writer_thread.join(timeout=5)

    assert not reader_thread.is_alive()
    assert not writer_thread.is_alive()
    assert errors == []
    assert reader_results == [initial]
    assert len(writer_results) == 1
    assert writer_results[0].disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert store.read_cursor().database_revision == 1


def test_failure_between_event_insert_and_meta_cas_rolls_back(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=200,
        revocation_registry_root=_position_bytes(180),
    )

    def fail_cas(*_args: object, **_kwargs: object) -> None:
        raise ValueError("injected meta CAS failure")

    monkeypatch.setattr(store_module, "_cas_meta", fail_cas)
    with pytest.raises(store_module.SpotV7ReleaseSelectionStoreErrorV1) as captured:
        store.select(
            candidate=candidate,
            selector_input_bytes=raw,
            expected_selector_input_id=input_id,
        )
    assert captured.value.code == "STORE_COMMIT_FAILED"
    assert store.read_cursor().database_revision == 0
    with sqlite3.connect(store.path) as connection:
        assert (
            connection.execute("SELECT count(*) FROM spot_v7_release_selection_events").fetchone()[
                0
            ]
            == 0
        )


def test_post_commit_directory_fsync_failure_resolves_exact_committed_event(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=221,
        revocation_registry_root=_position_bytes(201),
    )

    def fail_directory_fsync(_path: Path) -> None:
        raise OSError("injected directory fsync failure")

    with monkeypatch.context() as context:
        context.setattr(store_module, "_fsync_directory", fail_directory_fsync)
        result = store.select(
            candidate=candidate,
            selector_input_bytes=raw,
            expected_selector_input_id=input_id,
        )

    assert result.disposition is store_module.ReleaseSelectionDispositionV1.COMMITTED
    assert result.code == "SELECT_COMMITTED_POST_COMMIT_RESOLVED"
    assert result.cursor.database_revision == 1
    replay = store.select(
        candidate=candidate,
        selector_input_bytes=raw,
        expected_selector_input_id=input_id,
    )
    assert replay.disposition is store_module.ReleaseSelectionDispositionV1.IDEMPOTENT
    assert replay.cursor == result.cursor


def test_unresolved_post_commit_state_raises_typed_uncertainty_and_retry_resolves(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    candidate = _checked_candidate(revision=1, parent_candidate_id=None, variant=0)
    raw, input_id = _selector_bytes(
        operation=selector.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=store.read_cursor(),
        evaluation_epoch=0x0102_0304_0506,
        nonce_index=222,
        revocation_registry_root=_position_bytes(202),
    )
    original_validate_history = store_module._validate_complete_history
    validation_calls = 0

    def fail_post_commit_resolution(
        connection: sqlite3.Connection,
    ) -> store_module.SpotV7ReleaseSelectionCursorV1:
        nonlocal validation_calls
        validation_calls += 1
        result = original_validate_history(connection)
        if validation_calls == 2:
            raise ValueError("injected post-commit replay failure")
        return result

    def fail_directory_fsync(_path: Path) -> None:
        raise OSError("injected directory fsync failure")

    with monkeypatch.context() as context:
        context.setattr(store_module, "_validate_complete_history", fail_post_commit_resolution)
        context.setattr(store_module, "_fsync_directory", fail_directory_fsync)
        with pytest.raises(store_module.SpotV7ReleaseSelectionDurabilityUncertainV1) as captured:
            store.select(
                candidate=candidate,
                selector_input_bytes=raw,
                expected_selector_input_id=input_id,
            )

    assert captured.value.code == "POST_COMMIT_DURABILITY_UNCERTAIN"
    assert captured.value.operation is selector.SelectorOperationV1.SELECT
    assert captured.value.input_id == input_id
    assert captured.value.candidate_selected is False
    assert captured.value.revocation_authority is False
    assert captured.value.release_authority is False
    assert captured.value.production_authority is False
    retry = store.select(
        candidate=candidate,
        selector_input_bytes=raw,
        expected_selector_input_id=input_id,
    )
    assert retry.disposition is store_module.ReleaseSelectionDispositionV1.IDEMPOTENT
    assert retry.cursor.database_revision == 1


def test_restart_rejects_history_and_schema_corruption(tmp_path: Path) -> None:
    history_store = _store(tmp_path, "history.sqlite3")
    _commit_genesis(history_store)
    with sqlite3.connect(history_store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_release_selection_events SET candidate_bytes = zeroblob(length(candidate_bytes))"
        )
    with pytest.raises(store_module.SpotV7ReleaseSelectionStoreErrorV1) as captured:
        store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1(history_store.path)
    assert captured.value.code == "STORE_OPEN_FAILED"

    schema_store = _store(tmp_path, "schema.sqlite3")
    with sqlite3.connect(schema_store.path) as connection:
        connection.execute("CREATE TABLE injected(value INTEGER) STRICT")
    with pytest.raises(store_module.SpotV7ReleaseSelectionStoreErrorV1) as captured:
        store_module.SQLiteSpotV7GovernedReleaseSelectionStoreV1(schema_store.path)
    assert captured.value.code == "STORE_OPEN_FAILED"
