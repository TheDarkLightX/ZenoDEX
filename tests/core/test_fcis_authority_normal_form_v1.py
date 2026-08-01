"""Adversarial tests for the unmounted D01 Authority Normal Form carrier."""
from __future__ import annotations

import json
from dataclasses import replace
from typing import Any, cast

import pytest

from src.core.fcis_authority_normal_form_v1 import (
    FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1,
    FCISAuthorityNormalFormCodeV1,
    FCISAuthorityNormalFormRejectV1,
    FCISAuthorityNormalFormV1,
    FCISProofContextRequirementV1,
    canonical_authority_normal_form_root_v1,
    decode_authority_normal_form_v1,
    encode_authority_normal_form_v1,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


def _root(label: str) -> str:
    return cast(str, sha256_hex(domain_sep_bytes("fcis-m6-d01-test", version=1) + label.encode()))


def _value(
    requirement: FCISProofContextRequirementV1 = FCISProofContextRequirementV1.NOT_REQUIRED,
) -> FCISAuthorityNormalFormV1:
    return FCISAuthorityNormalFormV1(
        command_root=_root("command"),
        execution_context_root=_root("execution-context"),
        pre_state_root=_root("pre-state"),
        next_state_root=_root("next-state"),
        support_root=_root("support"),
        support_set_commitment=_root("support-set"),
        snapshot_commitment=_root("snapshot"),
        boundary_root=_root("boundary"),
        policy_root=_root("policy"),
        witness_tuple_root=_root("witness-tuple"),
        semantic_stream_root=_root("semantic-stream"),
        lineage_stream_root=_root("lineage-stream"),
        patch_root=_root("patch"),
        commit_plan_root=_root("commit-plan"),
        c3_claim_set_root=_root("c3-claim-set"),
        budget_root=_root("budget"),
        evaluation_certificate_root=_root("evaluation-certificate"),
        receipt_certificate_root=_root("receipt-certificate"),
        bundle_certificate_root=_root("bundle-certificate"),
        outbox_certificate_root=_root("outbox-certificate"),
        acceptance_decision_root=_root("acceptance-decision"),
        acceptance_receipt_root=_root("acceptance-receipt"),
        base_bundle_root=_root("base-bundle"),
        outbox_plan_root=_root("outbox-plan"),
        tcg_topology_root=_root("tcg-topology"),
        tcg_instance_root=_root("tcg-instance"),
        dra_pre_history_root=_root("dra-pre-history"),
        dra_post_history_root=_root("dra-post-history"),
        migration_authority_epoch_root=_root("migration-authority-epoch"),
        proof_context_requirement=requirement,
        proof_context_root=(
            _root("proof-context")
            if requirement is FCISProofContextRequirementV1.REQUIRED
            else None
        ),
    )


def _decoded_reject(payload: bytes) -> FCISAuthorityNormalFormRejectV1:
    result = decode_authority_normal_form_v1(payload)
    assert type(result) is FCISAuthorityNormalFormRejectV1
    return result


def test_optional_and_required_proof_context_round_trip() -> None:
    for requirement in FCISProofContextRequirementV1:
        value = _value(requirement)
        encoded = encode_authority_normal_form_v1(value)
        assert decode_authority_normal_form_v1(encoded) == value
        assert canonical_authority_normal_form_root_v1(value) == value.root


def test_each_root_field_changes_the_complete_anf_root() -> None:
    value = _value()
    original_root = value.root
    for field_name in FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1:
        changed = replace(value, **cast(Any, {field_name: _root(f"changed:{field_name}")}))
        assert changed.root != original_root, field_name


def test_wrong_exact_types_reject() -> None:
    with pytest.raises(TypeError):
        encode_authority_normal_form_v1({})
    rejection = decode_authority_normal_form_v1(bytearray(b"{}"))
    assert type(rejection) is FCISAuthorityNormalFormRejectV1
    assert rejection.code is FCISAuthorityNormalFormCodeV1.WRONG_EXACT_TYPE


def test_unknown_and_missing_fields_reject() -> None:
    value = _value()
    envelope = json.loads(encode_authority_normal_form_v1(value))
    envelope["value"]["foreign_root"] = _root("foreign")
    unknown = _decoded_reject(canonical_json_bytes(envelope))
    assert unknown.code is FCISAuthorityNormalFormCodeV1.UNKNOWN_FIELD

    missing_envelope = json.loads(encode_authority_normal_form_v1(value))
    del missing_envelope["value"]["next_state_root"]
    missing = _decoded_reject(canonical_json_bytes(missing_envelope))
    assert missing.code is FCISAuthorityNormalFormCodeV1.MISSING_FIELD


def test_duplicate_and_noncanonical_bytes_reject() -> None:
    duplicate = (
        b'{"schema":"zenodex/fcis/authority-normal-form/v1",'
        b'"schema":"zenodex/fcis/authority-normal-form/v1","value":{}}'
    )
    assert _decoded_reject(duplicate).code is FCISAuthorityNormalFormCodeV1.DUPLICATE_FIELD

    encoded = encode_authority_normal_form_v1(_value())
    noncanonical = _decoded_reject(encoded + b" ")
    assert noncanonical.code is FCISAuthorityNormalFormCodeV1.NONCANONICAL_BYTES


def test_proof_context_pair_is_closed() -> None:
    with pytest.raises(ValueError):
        replace(
            _value(),
            proof_context_requirement=FCISProofContextRequirementV1.REQUIRED,
            proof_context_root=None,
        )
    with pytest.raises(ValueError):
        replace(
            _value(),
            proof_context_root=_root("foreign-proof-context"),
        )


def test_invalid_root_type_rejects_at_decode() -> None:
    value = _value()
    envelope = json.loads(encode_authority_normal_form_v1(value))
    envelope["value"]["command_root"] = 7
    rejection = _decoded_reject(canonical_json_bytes(envelope))
    assert rejection.code is FCISAuthorityNormalFormCodeV1.INVALID_VALUE
