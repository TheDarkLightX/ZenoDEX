"""Deterministic D08 composition checker and adversarial witnesses."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

from src.core.fcis_authority_normal_form_v1 import (
    FCISProofContextRequirementV1,
)
from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_anf_bound_commit_bundle_v1,
    build_commit_bundle_v1,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    acceptance_receipt_root_v1,
    evaluate_source_bound_fcis_decision_v1,
    evaluate_source_bound_fcis_decision_with_anf_v1,
)
from src.core.fcis_durable_retraction import (
    AuthorizedHistoryV1,
    encode_history,
    initial_authority_state,
    reopen_snapshot,
    tagged_digest,
)
from src.core.fcis_lineage_closure import (
    FCISLineageClaimKeyV1,
    FCISLineageClosureCertificateV1,
    _build_fcis_lineage_closure_from_artifacts_v1,
)
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    D08CombinedANFCodeV1,
    D08CombinedANFInstanceV1,
    D08ProofContextV1,
    D08TCGExpectationV1,
    derive_d08_proof_context_root_v1,
    derive_d08_publication_atom_v1,
    verify_combined_anf_v1,
)
from src.core.fcis_transition_budget import TransitionBudgetV1
from src.core.fcis_tree_chord_gate_authority import (
    AuthorityEdgeV1,
    AuthorityGateV1,
    AuthorityNodeV1,
    LineageBindingV1,
    NodeArtifactExpectationV1,
    TreeChordGateCertificateV1,
    authority_instance_root,
    authority_topology_root,
    edge_receipt_subject_root,
    merge_lineage,
)
from tests.core.test_fcis_decision_derivation import _exact_inputs
from tests.core.test_fcis_m6_d03_anf_receipt_binding import (
    _authority_normal_form,
    _source_occurrence,
    evaluate_source_bound_fcis_step_candidate_v1_for_test,
)

_ROOT = Path(__file__).resolve().parents[1]
_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_D08_COMBINED_ANF_VECTOR.json"
_D05_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json"


def _tagged(label: str) -> str:
    return cast(str, tagged_digest(label))


def _anf_tagged(label: str) -> str:
    return f"0x{_tagged(label)}"


def _raw(value: str) -> str:
    return value[2:] if value.startswith("0x") else value


def _decision_root(decision: AcceptV1, bundle: CommitBundleV1) -> str:
    return _tagged(
        "d08/decision/"
        + acceptance_receipt_root_v1(decision)
        + "/"
        + decision.receipt.binding.commit_plan_root
        + "/"
        + bundle.bundle_root
    )


def _require_accept(value: object, name: str) -> AcceptV1:
    if type(value) is not AcceptV1:
        raise AssertionError(f"{name} is not an AcceptV1")
    return value


def _require_bundle(value: object, name: str) -> CommitBundleV1:
    if type(value) is not CommitBundleV1:
        raise AssertionError(f"{name} is not a CommitBundleV1")
    return value


def _build_tcg(
    closure: FCISLineageClosureCertificateV1,
    bundle: CommitBundleV1,
) -> tuple[TreeChordGateCertificateV1, D08TCGExpectationV1]:
    source_lineage = (LineageBindingV1("source_closure", _raw(closure.certificate_root)),)
    gate = AuthorityGateV1(0, "bind_base_bundle", ("base_bundle",))
    sink_lineage = merge_lineage(
        source_lineage,
        (LineageBindingV1("base_bundle", _raw(bundle.bundle_root)),),
    )
    source = AuthorityNodeV1(
        "n0_source_closure",
        0,
        _raw(closure.certificate_root),
        source_lineage,
    )
    sink = AuthorityNodeV1(
        "n1_base_bundle",
        1,
        _raw(bundle.bundle_root),
        sink_lineage,
    )
    edge = AuthorityEdgeV1(
        edge_id="e0_bind_base_bundle",
        source_node_id=source.node_id,
        target_node_id=sink.node_id,
        relation_label="source_closure_to_base_bundle",
        checker_digest=_tagged("d08/tcg/checker"),
        introductions=(LineageBindingV1("base_bundle", _raw(bundle.bundle_root)),),
        gate_index=0,
        gate_label=gate.gate_label,
        receipt_subject_digest="0" * 64,
        receipt_digest="0" * 64,
    )
    nodes = (source, sink)
    skeleton_edges = (edge,)
    topology_root = authority_topology_root(
        source_node_id=source.node_id,
        sink_node_ids=(sink.node_id,),
        gates=(gate,),
        nodes=nodes,
        edges=skeleton_edges,
        parent_edge_ids=(edge.edge_id,),
    )
    subject = edge_receipt_subject_root(
        topology_root=topology_root,
        edge=edge,
        source=source,
        target=sink,
    )
    sealed_edge = replace(
        edge,
        receipt_subject_digest=subject,
        receipt_digest=_tagged("d08/tcg/receipt/" + subject),
    )
    instance_root = authority_instance_root(
        topology_root=topology_root,
        nodes=nodes,
        edges=(sealed_edge,),
    )
    certificate = TreeChordGateCertificateV1(
        source_node_id=source.node_id,
        sink_node_ids=(sink.node_id,),
        gates=(gate,),
        nodes=nodes,
        edges=(sealed_edge,),
        parent_edge_ids=(edge.edge_id,),
        topology_root=topology_root,
        instance_root=instance_root,
    )
    d05 = cast(dict[str, Any], json.loads(_D05_VECTOR_PATH.read_text(encoding="utf-8")))
    expectation = D08TCGExpectationV1(
        inventory_root=cast(str, d05["publisher_inventory_root"]),
        topology_root=topology_root,
        instance_root=instance_root,
        source_node_id=source.node_id,
        source_artifact_digest=source.artifact_digest,
        source_lineage=source.lineage,
        sink_artifacts=(NodeArtifactExpectationV1(sink.node_id, sink.artifact_digest),),
        gates=(gate,),
    )
    return certificate, expectation


def build_instance() -> D08CombinedANFInstanceV1:
    inputs = _exact_inputs()
    budget = cast(TransitionBudgetV1, inputs["budget"])
    occurrence = _source_occurrence(inputs)
    evaluation = evaluate_source_bound_fcis_step_candidate_v1_for_test(occurrence)
    base_decision = _require_accept(
        evaluate_source_bound_fcis_decision_v1(
            source_occurrence=occurrence,
            budget=budget,
        ),
        "base decision",
    )
    base_bundle = _require_bundle(
        build_commit_bundle_v1(base_decision),
        "base bundle",
    )
    closure = _build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=evaluation,
        occurrence_segment=occurrence.segment,
        decision=base_decision,
        bundle=base_bundle,
        budget=budget,
    )
    if type(closure) is not FCISLineageClosureCertificateV1:
        raise AssertionError("base C3 closure rejected")

    authority = initial_authority_state(
        _tagged("d08/legacy-writer"),
        _tagged("d08/target-writer"),
    )
    pre_snapshot = encode_history(
        AuthorizedHistoryV1(
            genesis_state_root=_raw(base_decision.receipt.binding.pre_state_root),
            authority_epochs=(authority,),
            atoms=(),
            acks=(),
        )
    )
    pre_history_value = reopen_snapshot(pre_snapshot)
    if type(pre_history_value) is not AuthorizedHistoryV1:
        raise AssertionError("D08 pre-history fixture failed to reopen")

    tcg_certificate, tcg_expectation = _build_tcg(closure, base_bundle)
    seed_anf = _authority_normal_form(evaluation, base_decision, budget)
    binding = base_decision.receipt.binding
    proof_root = _anf_tagged("d08/proof-fixture")
    proof_context_root = derive_d08_proof_context_root_v1(
        proof_id="d08-proof-fixture",
        command_root=binding.command_or_batch_root,
        execution_context_root=binding.execution_context_hash,
        pre_state_root=binding.pre_state_root,
        next_state_root=binding.next_state_root,
        authority_epoch_root=f"0x{pre_history_value.authority.root}",
        verifier_profile_root=f"0x{pre_snapshot.verifier_profile_root}",
        proof_root=proof_root,
    )
    proof_context = D08ProofContextV1(
        proof_id="d08-proof-fixture",
        command_root=binding.command_or_batch_root,
        execution_context_root=binding.execution_context_hash,
        pre_state_root=binding.pre_state_root,
        next_state_root=binding.next_state_root,
        authority_epoch_root=f"0x{pre_history_value.authority.root}",
        verifier_profile_root=f"0x{pre_snapshot.verifier_profile_root}",
        proof_root=proof_root,
        context_root=proof_context_root,
    )
    derived = closure.closed_claims
    anf_partial = replace(
        seed_anf,
        c3_claim_set_root=derived.root,
        evaluation_certificate_root=cast(
            str,
            derived.value_for(FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT),
        ),
        receipt_certificate_root=cast(
            str,
            derived.value_for(FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT),
        ),
        bundle_certificate_root=cast(
            str,
            derived.value_for(FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT),
        ),
        outbox_certificate_root=cast(
            str,
            derived.value_for(FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT),
        ),
        acceptance_decision_root=f"0x{_decision_root(base_decision, base_bundle)}",
        base_bundle_root=base_bundle.bundle_root,
        outbox_plan_root=base_bundle.outbox_root,
        tcg_topology_root=f"0x{tcg_expectation.topology_root}",
        tcg_instance_root=f"0x{tcg_expectation.instance_root}",
        dra_pre_history_root=f"0x{pre_history_value.root}",
        dra_post_history_root="0x" + "00" * 32,
        migration_authority_epoch_root=f"0x{pre_history_value.authority.root}",
        proof_context_requirement=FCISProofContextRequirementV1.REQUIRED,
        proof_context_root=proof_context.context_root,
    )
    atom = derive_d08_publication_atom_v1(
        authority_normal_form=anf_partial,
        base_bundle=base_bundle,
        pre_history=pre_history_value,
        outbox_bindings=(),
    )
    post_history = AuthorizedHistoryV1(
        genesis_state_root=pre_history_value.genesis_state_root,
        authority_epochs=pre_history_value.authority_epochs,
        atoms=(atom,),
        acks=(),
        deployment_config_root=pre_history_value.deployment_config_root,
        verifier_profile_root=pre_history_value.verifier_profile_root,
    )
    post_snapshot = encode_history(post_history)
    anf = replace(
        anf_partial,
        dra_post_history_root=f"0x{post_history.root}",
    )
    decision = _require_accept(
        evaluate_source_bound_fcis_decision_with_anf_v1(
            source_occurrence=occurrence,
            budget=budget,
            authority_normal_form=anf,
        ),
        "ANF decision",
    )
    bundle = _require_bundle(
        build_anf_bound_commit_bundle_v1(decision, anf),
        "ANF bundle",
    )
    return D08CombinedANFInstanceV1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
        budget=budget,
        authority_normal_form=anf,
        base_decision=base_decision,
        base_bundle=base_bundle,
        decision=decision,
        bundle=bundle,
        tcg_certificate=tcg_certificate,
        tcg_expectation=tcg_expectation,
        proof_context=proof_context,
        pre_snapshot=pre_snapshot,
        publication_atom=atom,
        outbox_bindings=(),
        post_snapshot=post_snapshot,
    )


def _expect_code(
    instance: D08CombinedANFInstanceV1,
    code: D08CombinedANFCodeV1,
) -> None:
    result = verify_combined_anf_v1(instance)
    if getattr(result, "code", None) is not code:
        raise AssertionError(f"expected {code.value}, got {result!r}")


def _read_vector() -> dict[str, object]:
    value = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("D08 vector must be an object")
    return cast(dict[str, object], value)


def run_checks() -> dict[str, Any]:
    instance = build_instance()
    result = verify_combined_anf_v1(instance)
    if type(result) is not D08CombinedANFAcceptV1:
        raise AssertionError(f"valid D08 instance rejected: {result!r}")
    if result.anf_root != instance.authority_normal_form.root:
        raise AssertionError("D08 accepted the wrong ANF root")

    foreign_tcg = replace(
        instance.tcg_certificate,
        topology_root=_tagged("d08/foreign-topology"),
    )
    _expect_code(
        replace(instance, tcg_certificate=foreign_tcg),
        D08CombinedANFCodeV1.TCG_REJECTED,
    )
    foreign_c3 = replace(
        instance.authority_normal_form,
        c3_claim_set_root=_anf_tagged("d08/foreign-c3"),
    )
    _expect_code(
        replace(instance, authority_normal_form=foreign_c3),
        D08CombinedANFCodeV1.C3_ROOT_MISMATCH,
    )
    proof = instance.proof_context
    if proof is None:
        raise AssertionError("D08 fixture requires a proof context")
    foreign_proof_root = _anf_tagged("d08/foreign-proof")
    foreign_proof = replace(
        proof,
        proof_root=foreign_proof_root,
        context_root=derive_d08_proof_context_root_v1(
            proof_id=proof.proof_id,
            command_root=proof.command_root,
            execution_context_root=proof.execution_context_root,
            pre_state_root=proof.pre_state_root,
            next_state_root=proof.next_state_root,
            authority_epoch_root=proof.authority_epoch_root,
            verifier_profile_root=proof.verifier_profile_root,
            proof_root=foreign_proof_root,
        ),
    )
    _expect_code(
        replace(instance, proof_context=foreign_proof),
        D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
    )
    foreign_atom = replace(
        instance.publication_atom,
        authority_state_root=_tagged("d08/foreign-authority"),
    )
    _expect_code(
        replace(instance, publication_atom=foreign_atom),
        D08CombinedANFCodeV1.PUBLICATION_REJECTED,
    )
    _expect_code(
        replace(instance, decision=instance.base_decision),
        D08CombinedANFCodeV1.LATER_ROOT_SUBSTITUTION,
    )
    payload: dict[str, Any] = {
        "anf_root": result.anf_root,
        "c3_root": instance.authority_normal_form.c3_claim_set_root,
        "tcg_topology_root": instance.tcg_expectation.topology_root,
        "tcg_instance_root": instance.tcg_expectation.instance_root,
        "proof_context_root": proof.context_root,
        "pre_history_root": instance.authority_normal_form.dra_pre_history_root,
        "post_history_root": instance.authority_normal_form.dra_post_history_root,
        "atom_root": instance.publication_atom.atom_root,
        "base_bundle_root": instance.base_bundle.bundle_root,
        "bundle_root": instance.bundle.bundle_root,
        "d05_inventory_root": instance.tcg_expectation.inventory_root,
        "mutants_killed": 5,
    }
    vector = _read_vector()
    if vector.pop("schema_version", None) != ("zenodex.fcis.m6.d08.combined-anf-vector.v1"):
        raise AssertionError("D08 vector has the wrong schema")
    if vector != payload:
        raise AssertionError("D08 vector does not match regenerated outputs")
    return payload


if __name__ == "__main__":
    print(json.dumps(run_checks(), sort_keys=True))
    print("D08_COMBINED_ANF_MATCH")
