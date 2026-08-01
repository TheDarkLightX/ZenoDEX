"""Recompute the deterministic D01 Authority Normal Form vector."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

from src.core.fcis_authority_normal_form_v1 import (
    FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1,
    FCIS_AUTHORITY_NORMAL_FORM_SCHEMA_ID_V1,
    FCISAuthorityNormalFormV1,
    FCISProofContextRequirementV1,
    decode_authority_normal_form_v1,
    encode_authority_normal_form_v1,
)
from src.state.canonical import domain_sep_bytes, sha256_hex

_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_D01_AUTHORITY_NORMAL_FORM_VECTOR.json")


def _root(label: str) -> str:
    return cast(
        str,
        sha256_hex(domain_sep_bytes("fcis-m6-d01-test", version=1) + label.encode()),
    )


def _text(fields: dict[str, Any], name: str) -> str:
    value = fields.get(name)
    if type(value) is not str:
        raise AssertionError(f"vector field label is not text: {name}")
    return value


def _build_value(fields: dict[str, Any]) -> FCISAuthorityNormalFormV1:
    return FCISAuthorityNormalFormV1(
        command_root=_root(_text(fields, "command_root")),
        execution_context_root=_root(_text(fields, "execution_context_root")),
        pre_state_root=_root(_text(fields, "pre_state_root")),
        next_state_root=_root(_text(fields, "next_state_root")),
        support_root=_root(_text(fields, "support_root")),
        support_set_commitment=_root(_text(fields, "support_set_commitment")),
        snapshot_commitment=_root(_text(fields, "snapshot_commitment")),
        boundary_root=_root(_text(fields, "boundary_root")),
        policy_root=_root(_text(fields, "policy_root")),
        witness_tuple_root=_root(_text(fields, "witness_tuple_root")),
        semantic_stream_root=_root(_text(fields, "semantic_stream_root")),
        lineage_stream_root=_root(_text(fields, "lineage_stream_root")),
        patch_root=_root(_text(fields, "patch_root")),
        commit_plan_root=_root(_text(fields, "commit_plan_root")),
        c3_claim_set_root=_root(_text(fields, "c3_claim_set_root")),
        budget_root=_root(_text(fields, "budget_root")),
        evaluation_certificate_root=_root(_text(fields, "evaluation_certificate_root")),
        receipt_certificate_root=_root(_text(fields, "receipt_certificate_root")),
        bundle_certificate_root=_root(_text(fields, "bundle_certificate_root")),
        outbox_certificate_root=_root(_text(fields, "outbox_certificate_root")),
        acceptance_decision_root=_root(_text(fields, "acceptance_decision_root")),
        acceptance_receipt_root=_root(_text(fields, "acceptance_receipt_root")),
        base_bundle_root=_root(_text(fields, "base_bundle_root")),
        outbox_plan_root=_root(_text(fields, "outbox_plan_root")),
        tcg_topology_root=_root(_text(fields, "tcg_topology_root")),
        tcg_instance_root=_root(_text(fields, "tcg_instance_root")),
        dra_pre_history_root=_root(_text(fields, "dra_pre_history_root")),
        dra_post_history_root=_root(_text(fields, "dra_post_history_root")),
        migration_authority_epoch_root=_root(_text(fields, "migration_authority_epoch_root")),
        proof_context_requirement=FCISProofContextRequirementV1.NOT_REQUIRED,
        proof_context_root=None,
    )


def main() -> int:
    vector = cast(dict[str, Any], json.loads(_VECTOR_PATH.read_text(encoding="utf-8")))
    if vector["schema_version"] != FCIS_AUTHORITY_NORMAL_FORM_SCHEMA_ID_V1:
        raise AssertionError("D01 schema version drift")
    fields = cast(dict[str, Any], vector["fields"])
    if tuple(fields) != tuple(sorted(fields)):
        raise AssertionError("D01 vector field order is not canonical")
    if frozenset(fields) != frozenset(FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1):
        raise AssertionError("D01 vector root field registry drift")
    value = _build_value(fields)
    encoded = encode_authority_normal_form_v1(value)
    if encoded.decode("utf-8") != vector["canonical_bytes_utf8"]:
        raise AssertionError("D01 canonical bytes drift")
    if value.root != vector["root"]:
        raise AssertionError("D01 root drift")
    if decode_authority_normal_form_v1(encoded) != value:
        raise AssertionError("D01 canonical decode round trip failed")
    print("D01_VECTOR_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
