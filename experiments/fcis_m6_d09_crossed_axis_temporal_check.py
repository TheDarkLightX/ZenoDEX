"""Deterministic D09 crossed-axis and temporal mutant checker."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import cast

import experiments.fcis_m6_d08_combined_anf_check as d08_fixture
from src.core.batch_clearing import compute_settlement
from src.core.fcis_decision_derivation import FCIS_SPOT_TRANSITION_BUDGET_V1
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFCodeV1,
    D08CombinedANFInstanceV1,
    D08CombinedANFRejectV1,
    verify_combined_anf_v1,
)
from src.core.fcis_stutter_receipt import (
    NonStutterOperationKindV1,
    StutterRejectV1,
    verify_stutter_candidate_v1,
)
from src.core.settlement_snapshots import snapshot_settlement
from src.state.intent_snapshots import admit_intent_batch
from tests.core.test_fcis_step_evaluator import (
    _context_source,
    _iid,
    _state_source,
    _swap_case,
)

_ROOT = Path(__file__).resolve().parents[1]
_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_D09_CROSSED_AXIS_VECTOR.json"


def _root(label: str) -> str:
    return f"0x{cast(str, d08_fixture.tagged_digest('d09/' + label))}"


def _variant_inputs() -> dict[str, object]:
    state, intent, _ = _swap_case()
    fields = dict(intent.fields)
    fields["amount_in"] = 200_000
    variant = replace(intent, intent_id=_iid(2), fields=fields)
    settlement = compute_settlement(
        [variant],
        state.pools,
        state.balances,
        state.lp_balances,
    )
    return {
        "state_source": _state_source(state),
        "settlement": snapshot_settlement(settlement),
        "intents": admit_intent_batch([variant]),
        "context": _context_source(),
        "budget": FCIS_SPOT_TRANSITION_BUDGET_V1,
    }


def _build_instance_from(inputs: dict[str, object]) -> D08CombinedANFInstanceV1:
    original = d08_fixture._exact_inputs
    d08_fixture._exact_inputs = lambda: inputs
    try:
        return d08_fixture.build_instance()
    finally:
        d08_fixture._exact_inputs = original


def _build_transitions() -> tuple[
    D08CombinedANFInstanceV1,
    D08CombinedANFInstanceV1,
]:
    first = d08_fixture.build_instance()
    second = _build_instance_from(_variant_inputs())
    if first.authority_normal_form.root == second.authority_normal_form.root:
        raise AssertionError("D09 transitions unexpectedly share an ANF root")
    if first.base_bundle.bundle_root == second.base_bundle.bundle_root:
        raise AssertionError("D09 transitions unexpectedly share a bundle root")
    return first, second


def _d08_code(value: object) -> str:
    if type(value) is not D08CombinedANFRejectV1:
        raise AssertionError(f"D08 mutant unexpectedly accepted: {value!r}")
    rejection = cast(D08CombinedANFRejectV1, value)
    return cast(str, rejection.code.value)


def _stutter_code(operation_kind: NonStutterOperationKindV1) -> str:
    root = _root("temporal/" + operation_kind.value)
    result = verify_stutter_candidate_v1(
        operation_id=root,
        operation_kind=operation_kind,
        pre_canonical_root=root,
        post_canonical_root=root,
        observable_pre_root=root,
        observable_post_root=root,
    )
    if type(result) is not StutterRejectV1:
        raise AssertionError(f"{operation_kind.value} was hidden as a stutter")
    rejection = cast(StutterRejectV1, result)
    return cast(str, rejection.code.value)


def _read_vector() -> dict[str, object]:
    value = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("D09 vector must be an object")
    return cast(dict[str, object], value)


def run_checks() -> dict[str, object]:
    first, second = _build_transitions()

    semantic_receipt_cross = replace(first, base_decision=second.base_decision)
    receipt_bundle_cross = replace(first, base_bundle=second.base_bundle)
    bundle_outbox_cross = replace(first, base_bundle=second.base_bundle)
    foreign_tcg = replace(first, tcg_certificate=second.tcg_certificate)
    foreign_atom = replace(
        first,
        publication_atom=replace(
            first.publication_atom,
            authority_state_root=_root("foreign-authority-epoch")[2:],
        ),
    )
    foreign_lineage = replace(
        first.authority_normal_form,
        lineage_stream_root=second.authority_normal_form.lineage_stream_root,
    )
    if foreign_lineage.lineage_stream_root == first.authority_normal_form.lineage_stream_root:
        raise AssertionError("D09 lineage mutant did not change the lineage root")
    semantic_lineage_cross = replace(first, authority_normal_form=foreign_lineage)

    cases = {
        "semantic_transition_1_receipt_transition_2": _d08_code(
            verify_combined_anf_v1(semantic_receipt_cross)
        ),
        "receipt_transition_1_bundle_transition_2": _d08_code(
            verify_combined_anf_v1(receipt_bundle_cross)
        ),
        "bundle_transition_1_outbox_transition_2": _d08_code(
            verify_combined_anf_v1(bundle_outbox_cross)
        ),
        "tcg_receipt_foreign_topology": _d08_code(verify_combined_anf_v1(foreign_tcg)),
        "dra_atom_foreign_authority_epoch": _d08_code(verify_combined_anf_v1(foreign_atom)),
        "same_semantic_different_lineage": _d08_code(
            verify_combined_anf_v1(semantic_lineage_cross)
        ),
        "stutter_hiding_new_commit": _stutter_code(NonStutterOperationKindV1.NEW_COMMIT),
        "stutter_hiding_migration": _stutter_code(NonStutterOperationKindV1.MIGRATION),
    }
    expected_codes = {
        "semantic_transition_1_receipt_transition_2": D08CombinedANFCodeV1.SOURCE_LINEAGE_MISMATCH.value,
        "receipt_transition_1_bundle_transition_2": D08CombinedANFCodeV1.SOURCE_LINEAGE_MISMATCH.value,
        "bundle_transition_1_outbox_transition_2": D08CombinedANFCodeV1.SOURCE_LINEAGE_MISMATCH.value,
        "tcg_receipt_foreign_topology": D08CombinedANFCodeV1.TCG_REJECTED.value,
        "dra_atom_foreign_authority_epoch": D08CombinedANFCodeV1.PUBLICATION_REJECTED.value,
        "same_semantic_different_lineage": D08CombinedANFCodeV1.ANF_BASE_BINDING_MISMATCH.value,
        "stutter_hiding_new_commit": "forbidden_operation",
        "stutter_hiding_migration": "forbidden_operation",
    }
    if cases != expected_codes:
        raise AssertionError(f"D09 mutant code drift: {cases!r}")
    payload: dict[str, object] = {
        "transition_1_anf_root": first.authority_normal_form.root,
        "transition_2_anf_root": second.authority_normal_form.root,
        "transition_1_bundle_root": first.base_bundle.bundle_root,
        "transition_2_bundle_root": second.base_bundle.bundle_root,
        "cases": cases,
        "mutants_killed": len(cases),
    }
    vector = _read_vector()
    if vector.pop("schema_version", None) != "zenodex.fcis.m6.d09.crossed-axis.v1":
        raise AssertionError("D09 vector has the wrong schema")
    if vector != payload:
        raise AssertionError("D09 vector does not match regenerated mutant outputs")
    return payload


if __name__ == "__main__":
    print(json.dumps(run_checks(), sort_keys=True))
    print("D09_CROSSED_AXIS_MATCH")
