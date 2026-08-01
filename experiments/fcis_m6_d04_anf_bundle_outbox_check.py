"""Recompute the deterministic D04 ANF-to-bundle/outbox relation."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_anf_bound_commit_bundle_v1,
    build_commit_bundle_v1,
    recompute_anf_root_v1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
    recompute_outbox_root_v1,
    verify_anf_bound_commit_bundle_v1,
)
from src.core.fcis_commit_bundle_values import (
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2,
)
from src.core.fcis_commit_reference import ReferenceCommitStatusV1, reference_commit_v1
from src.core.fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    acceptance_receipt_root_v1,
)
from src.core.fcis_outbox_values import (
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V1,
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V2,
    OutboxPlanV1,
    OutboxPlanV2,
)
from src.state.canonical import sha256_hex
from tests.core.test_fcis_commit_bundle_derivation import _anf_accept_with_value, _event_accept
from tests.core.test_fcis_commit_reference import _store_from_pre_state

_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json")


def main() -> int:
    vector = cast(dict[str, Any], json.loads(_VECTOR_PATH.read_text(encoding="utf-8")))
    if vector["schema_version"] != "zenodex.fcis.m6.d04.anf-bundle-outbox.v2":
        raise AssertionError("D04 schema version drift")
    if vector["outbox_schema_id"] != FCIS_OUTBOX_PLAN_SCHEMA_ID_V2:
        raise AssertionError("D04 outbox schema identity drift")
    if vector["bundle_schema_id"] != FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2:
        raise AssertionError("D04 bundle schema identity drift")
    expected = cast(dict[str, Any], vector["expected"])
    decision, anf = _anf_accept_with_value()
    if type(decision) is not AcceptV1:
        raise AssertionError("D04 fixture decision type drift")
    bundle = build_anf_bound_commit_bundle_v1(decision, anf)
    if type(bundle) is not CommitBundleV1:
        raise AssertionError("D04 ANF-bound bundle rejected")
    if type(bundle.outbox_plan) is not OutboxPlanV2:
        raise AssertionError("D04 ANF-bound outbox did not use V2")
    if bundle.outbox_schema_id != FCIS_OUTBOX_PLAN_SCHEMA_ID_V2:
        raise AssertionError("D04 ANF-bound outbox schema projection drift")
    if bundle.bundle_schema_id != FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2:
        raise AssertionError("D04 ANF-bound bundle schema projection drift")
    decision_identity_retained = bundle.decision is decision
    if decision_identity_retained is not expected["decision_identity_retained"]:
        raise AssertionError("D04 bundle did not retain exact decision")
    if bundle.decision is not decision:
        raise AssertionError("D04 bundle did not retain exact decision")
    if bundle.authority_normal_form_root != vector["anf_root"]:
        raise AssertionError("D04 ANF root drift")
    receipt_root_recomputes = bundle.receipt_root == acceptance_receipt_root_v1(decision)
    if receipt_root_recomputes is not expected["receipt_root_recomputes"]:
        raise AssertionError("D04 receipt root did not recompute")
    if bundle.receipt_root != vector["decision_receipt_root"]:
        raise AssertionError("D04 receipt root drift")
    if recompute_anf_root_v1(bundle) != vector["anf_root"]:
        raise AssertionError("D04 ANF root did not recompute")
    anf_root_retained_in_outbox = (
        bundle.outbox_plan.authority_normal_form_root == vector["anf_root"]
    )
    if anf_root_retained_in_outbox is not expected["anf_root_retained_in_outbox"]:
        raise AssertionError("D04 outbox lost the ANF root")
    if bundle.outbox_plan.authority_normal_form_root != vector["anf_root"]:
        raise AssertionError("D04 outbox lost the ANF root")
    if recompute_outbox_plan_v1(bundle) != bundle.outbox_plan:
        raise AssertionError("D04 outbox plan did not recompute")
    if recompute_outbox_root_v1(bundle) != vector["outbox_root"]:
        raise AssertionError("D04 outbox root drift")
    canonical_bytes, bundle_root = recompute_bundle_root_v1(bundle)
    bundle_root_recomputes = (
        bundle_root == vector["bundle_root"] and canonical_bytes == bundle.canonical_bundle_bytes
    )
    if bundle_root_recomputes is not expected["bundle_root_recomputes"]:
        raise AssertionError("D04 bundle root did not recompute")
    if bundle_root != vector["bundle_root"] or canonical_bytes != bundle.canonical_bundle_bytes:
        raise AssertionError("D04 bundle root or bytes drift")
    if sha256_hex(bundle.canonical_bundle_bytes) != vector["bundle_bytes_sha256"]:
        raise AssertionError("D04 bundle byte digest drift")
    if len(bundle.outbox_plan.records) != vector["outbox_record_count"]:
        raise AssertionError("D04 outbox cardinality drift")
    if not verify_anf_bound_commit_bundle_v1(bundle):
        raise AssertionError("D04 valid bundle failed verification")

    valid_publication = reference_commit_v1(_store_from_pre_state(), bundle)
    valid_reference_publication = valid_publication.status is ReferenceCommitStatusV1.PUBLISHED
    if valid_reference_publication is not expected["valid_reference_publication"]:
        raise AssertionError("D04 valid reference publication drift")

    legacy = build_commit_bundle_v1(_event_accept())
    if type(legacy) is not CommitBundleV1 or type(legacy.outbox_plan) is not OutboxPlanV1:
        raise AssertionError("D04 legacy V1 fixture drift")
    legacy_v1_canonical_preserved = (
        legacy.outbox_schema_id == FCIS_OUTBOX_PLAN_SCHEMA_ID_V1
        and legacy.bundle_schema_id == FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1
        and legacy.outbox_root == vector["legacy_outbox_root"]
        and legacy.bundle_root == vector["legacy_bundle_root"]
        and sha256_hex(legacy.canonical_bundle_bytes) == vector["legacy_bundle_bytes_sha256"]
    )
    if legacy_v1_canonical_preserved is not expected["legacy_v1_canonical_preserved"]:
        raise AssertionError("D04 legacy V1 canonical identity changed")

    corrupted_decision, corrupted_anf = _anf_accept_with_value()
    corrupted_bundle = build_anf_bound_commit_bundle_v1(corrupted_decision, corrupted_anf)
    if type(corrupted_bundle) is not CommitBundleV1:
        raise AssertionError("D04 corrupted fixture bundle rejected too early")
    object.__setattr__(
        corrupted_bundle,
        "authority_normal_form",
        replace(corrupted_anf, command_root="0x" + "99" * 32),
    )
    corrupted_result = reference_commit_v1(_store_from_pre_state(), corrupted_bundle)
    corrupted_anf_rejected_at_commit = (
        corrupted_result.status is ReferenceCommitStatusV1.INVALID
        and corrupted_result.store.publications == ()
    )
    if corrupted_anf_rejected_at_commit is not expected["corrupted_anf_rejected_at_commit"]:
        raise AssertionError("D04 commit port accepted a corrupted retained ANF")

    stored_decision, stored_anf = _anf_accept_with_value()
    stored_bundle = build_anf_bound_commit_bundle_v1(stored_decision, stored_anf)
    if type(stored_bundle) is not CommitBundleV1:
        raise AssertionError("D04 stored fixture bundle rejected")
    stored_publication = reference_commit_v1(_store_from_pre_state(), stored_bundle)
    if stored_publication.status is not ReferenceCommitStatusV1.PUBLISHED:
        raise AssertionError("D04 stored fixture did not publish")
    object.__setattr__(
        stored_publication.store.publications[0].bundle,
        "authority_normal_form",
        replace(stored_anf, command_root="0x" + "99" * 32),
    )
    retry_decision, retry_anf = _anf_accept_with_value()
    retry_bundle = build_anf_bound_commit_bundle_v1(retry_decision, retry_anf)
    if type(retry_bundle) is not CommitBundleV1:
        raise AssertionError("D04 retry fixture bundle rejected")
    stored_result = reference_commit_v1(stored_publication.store, retry_bundle)
    stored_corrupted_anf_rejected = stored_result.status is ReferenceCommitStatusV1.INVALID
    if stored_corrupted_anf_rejected is not expected["stored_corrupted_anf_rejected"]:
        raise AssertionError("D04 store validation accepted a corrupted retained ANF")

    foreign_anf = replace(anf, command_root="0x" + "99" * 32)
    foreign_anf_result = build_anf_bound_commit_bundle_v1(decision, foreign_anf)
    foreign_anf_rejected = type(foreign_anf_result) is RejectV1
    if not foreign_anf_rejected:
        raise AssertionError("D04 foreign ANF was accepted")

    foreign = build_commit_bundle_v1(_event_accept())
    if type(foreign) is not CommitBundleV1:
        raise AssertionError("D04 foreign fixture bundle drift")
    crossed_decision_value, crossed_anf = _anf_accept_with_value()
    crossed_outbox = build_anf_bound_commit_bundle_v1(crossed_decision_value, crossed_anf)
    if type(crossed_outbox) is not CommitBundleV1:
        raise AssertionError("D04 crossed-outbox base bundle rejected")
    object.__setattr__(crossed_outbox, "outbox_plan", foreign.outbox_plan)
    crossed_outbox_rejected = not verify_anf_bound_commit_bundle_v1(crossed_outbox)

    decision_value, decision_anf = _anf_accept_with_value()
    crossed_decision = build_anf_bound_commit_bundle_v1(decision_value, decision_anf)
    if type(crossed_decision) is not CommitBundleV1:
        raise AssertionError("D04 crossed-decision base bundle rejected")
    object.__setattr__(crossed_decision, "decision", foreign.decision)
    crossed_decision_rejected = not verify_anf_bound_commit_bundle_v1(crossed_decision)

    if crossed_outbox_rejected is not expected["crossed_outbox_rejected"]:
        raise AssertionError("D04 crossed outbox was accepted")
    if foreign_anf_rejected is not expected["foreign_anf_rejected"]:
        raise AssertionError("D04 foreign ANF result drift")
    if crossed_decision_rejected is not expected["crossed_decision_rejected"]:
        raise AssertionError("D04 crossed decision was accepted")
    print("D04_ANF_BUNDLE_OUTBOX_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
