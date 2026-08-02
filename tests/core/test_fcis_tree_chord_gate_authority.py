from __future__ import annotations

from dataclasses import replace
from hashlib import sha256

import pytest

from src.core.fcis_tree_chord_gate_authority import (
    AuthorityCertificateError,
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
    verify_tree_chord_gate_certificate,
)


def _digest(label: str) -> str:
    return sha256(label.encode("utf-8")).hexdigest()


_GATE_SPECS = (
    ("canonical_ingress", "canonical_command"),
    ("authenticate_invocation", "authenticated_invocation"),
    ("bind_current_state", "current_state"),
    ("bind_execution_context", "execution_context"),
    ("validate_runtime_decision", "validated_decision"),
    ("authorize_candidate", "authorized_candidate"),
    ("atomic_publication", "committed_history"),
    ("reopen_reauthorization", "reopened_head"),
    ("deliver_outbox", "delivered_effect"),
)


def _gates() -> tuple[AuthorityGateV1, ...]:
    return tuple(
        AuthorityGateV1(index, label, (role,)) for index, (label, role) in enumerate(_GATE_SPECS)
    )


def _nodes(gates: tuple[AuthorityGateV1, ...]) -> tuple[AuthorityNodeV1, ...]:
    lineage = (LineageBindingV1("raw_request", _digest("raw_request")),)
    nodes = [AuthorityNodeV1("n0_raw_request", 0, _digest("artifact:0"), lineage)]
    for index, gate in enumerate(gates, start=1):
        introductions = tuple(
            LineageBindingV1(role, _digest(f"source:{role}")) for role in gate.introduction_roles
        )
        lineage = merge_lineage(lineage, introductions)
        nodes.append(
            AuthorityNodeV1(
                f"n{index}_{gate.introduction_roles[0]}",
                index,
                _digest(f"artifact:{index}"),
                lineage,
            )
        )
    return tuple(sorted(nodes, key=lambda node: node.node_id.encode("utf-8")))


def _edge_skeletons(
    gates: tuple[AuthorityGateV1, ...],
    nodes: tuple[AuthorityNodeV1, ...],
) -> tuple[AuthorityEdgeV1, ...]:
    by_stage = {node.stage: node for node in nodes}
    descriptions = (
        ("e00_python_decode", 0, 1, "python_decode"),
        ("e01_rust_decode", 0, 1, "rust_decode"),
        ("e10_authenticate", 1, 2, "approved_authenticator"),
        ("e20_current_state", 2, 3, "current_state_reader"),
        ("e30_context", 3, 4, "consensus_context_reader"),
        ("e40_reference_decision", 4, 5, "pure_reference_transition"),
        ("e41_runtime_decision", 4, 5, "runtime_refinement_checker"),
        ("e50_authorize", 5, 6, "catalog_commit_authority"),
        ("e60_commit", 6, 7, "sqlite_atomic_commit"),
        ("e70_reopen", 7, 8, "normal_reopen"),
        ("e71_recovery_reopen", 7, 8, "recovery_replay"),
        ("e80_delivery", 8, 9, "outbox_delivery"),
    )
    edges: list[AuthorityEdgeV1] = []
    placeholder = "0" * 64
    for edge_id, source_stage, target_stage, relation in descriptions:
        gate = gates[source_stage]
        target = by_stage[target_stage]
        introductions = tuple(
            binding for binding in target.lineage if binding.role in gate.introduction_roles
        )
        edges.append(
            AuthorityEdgeV1(
                edge_id=edge_id,
                source_node_id=by_stage[source_stage].node_id,
                target_node_id=target.node_id,
                relation_label=relation,
                checker_digest=_digest(f"checker:{relation}"),
                introductions=introductions,
                gate_index=gate.gate_index,
                gate_label=gate.gate_label,
                receipt_subject_digest=placeholder,
                receipt_digest=placeholder,
            )
        )
    return tuple(sorted(edges, key=lambda edge: edge.edge_id.encode("utf-8")))


def _build_certificate(
    *,
    gates: tuple[AuthorityGateV1, ...] | None = None,
    nodes: tuple[AuthorityNodeV1, ...] | None = None,
    edges: tuple[AuthorityEdgeV1, ...] | None = None,
    parent_edge_ids: tuple[str, ...] | None = None,
) -> TreeChordGateCertificateV1:
    exact_gates = _gates() if gates is None else gates
    exact_nodes = _nodes(exact_gates) if nodes is None else nodes
    exact_edges = (
        _edge_skeletons(exact_gates, exact_nodes)
        if edges is None
        else tuple(sorted(edges, key=lambda edge: edge.edge_id.encode("utf-8")))
    )
    exact_parent_ids = (
        (
            "e00_python_decode",
            "e10_authenticate",
            "e20_current_state",
            "e30_context",
            "e40_reference_decision",
            "e50_authorize",
            "e60_commit",
            "e70_reopen",
            "e80_delivery",
        )
        if parent_edge_ids is None
        else parent_edge_ids
    )
    exact_parent_ids = tuple(sorted(exact_parent_ids))
    source_node_id = next(node.node_id for node in exact_nodes if node.stage == 0)
    sink_node_ids = tuple(
        sorted(node.node_id for node in exact_nodes if node.stage == len(exact_gates))
    )
    topology_root = authority_topology_root(
        source_node_id=source_node_id,
        sink_node_ids=sink_node_ids,
        gates=exact_gates,
        nodes=exact_nodes,
        edges=exact_edges,
        parent_edge_ids=exact_parent_ids,
    )
    node_map = {node.node_id: node for node in exact_nodes}
    sealed_edges: list[AuthorityEdgeV1] = []
    for edge in exact_edges:
        subject = edge_receipt_subject_root(
            topology_root=topology_root,
            edge=edge,
            source=node_map[edge.source_node_id],
            target=node_map[edge.target_node_id],
        )
        sealed_edges.append(
            replace(
                edge,
                receipt_subject_digest=subject,
                receipt_digest=_digest(f"receipt:{subject}"),
            )
        )
    sealed = tuple(sorted(sealed_edges, key=lambda edge: edge.edge_id.encode("utf-8")))
    instance_root = authority_instance_root(
        topology_root=topology_root,
        nodes=exact_nodes,
        edges=sealed,
    )
    return TreeChordGateCertificateV1(
        source_node_id=source_node_id,
        sink_node_ids=sink_node_ids,
        gates=exact_gates,
        nodes=exact_nodes,
        edges=sealed,
        parent_edge_ids=exact_parent_ids,
        topology_root=topology_root,
        instance_root=instance_root,
    )


def _verify(
    certificate: TreeChordGateCertificateV1,
    *,
    topology_root: str | None = None,
    instance_root: str | None = None,
    gates: tuple[AuthorityGateV1, ...] | None = None,
    source_artifact: str | None = None,
    sink_artifact: str | None = None,
):
    source = next(node for node in certificate.nodes if node.node_id == certificate.source_node_id)
    sink = next(node for node in certificate.nodes if node.node_id == certificate.sink_node_ids[0])
    return verify_tree_chord_gate_certificate(
        expected_topology_root=certificate.topology_root
        if topology_root is None
        else topology_root,
        expected_instance_root=certificate.instance_root
        if instance_root is None
        else instance_root,
        expected_source_node_id=certificate.source_node_id,
        expected_source_artifact_digest=(
            source.artifact_digest if source_artifact is None else source_artifact
        ),
        expected_source_lineage=source.lineage,
        expected_sink_artifacts=(
            NodeArtifactExpectationV1(
                sink.node_id,
                sink.artifact_digest if sink_artifact is None else sink_artifact,
            ),
        ),
        expected_gates=certificate.gates if gates is None else gates,
        certificate=certificate,
    )


def test_valid_tree_chord_gate_certificate() -> None:
    certificate = _build_certificate()
    verdict = _verify(certificate)

    assert verdict.accepted
    assert verdict.reason == "PASS"
    assert verdict.node_count == 10
    assert verdict.edge_count == 12
    assert verdict.tree_edge_count == 9
    assert verdict.chord_receipt_count == 3
    assert verdict.gate_crossing_edge_count == 12


def test_external_topology_root_detects_inserted_bypass() -> None:
    certificate = _build_certificate()
    source = next(node for node in certificate.nodes if node.stage == 0)
    sink = next(node for node in certificate.nodes if node.stage == len(certificate.gates))
    bypass = AuthorityEdgeV1(
        edge_id="e02_direct_publish",
        source_node_id=source.node_id,
        target_node_id=sink.node_id,
        relation_label="caller_selected_publish",
        checker_digest=_digest("checker:bypass"),
        introductions=tuple(binding for binding in sink.lineage if binding not in source.lineage),
        gate_index=0,
        gate_label=certificate.gates[0].gate_label,
        receipt_subject_digest="0" * 64,
        receipt_digest="0" * 64,
    )
    mutated = _build_certificate(edges=certificate.edges + (bypass,))

    old_anchor = _verify(mutated, topology_root=certificate.topology_root)
    new_anchor = _verify(mutated)

    assert not old_anchor.accepted
    assert "topology root" in old_anchor.reason
    assert not new_anchor.accepted
    assert "skips or reverses" in new_anchor.reason


def test_instance_root_and_receipt_subject_bind_artifacts() -> None:
    certificate = _build_certificate()
    decision = next(node for node in certificate.nodes if node.stage == 5)
    mutated_node = replace(decision, artifact_digest=_digest("substituted-decision"))
    mutated_nodes = tuple(
        sorted(
            (
                mutated_node if node.node_id == decision.node_id else node
                for node in certificate.nodes
            ),
            key=lambda node: node.node_id.encode("utf-8"),
        )
    )
    hostile = replace(certificate, nodes=mutated_nodes)

    verdict = _verify(hostile)

    assert not verdict.accepted
    assert "receipt subject" in verdict.reason or "instance root" in verdict.reason


def test_crossed_lineage_chord_is_rejected() -> None:
    certificate = _build_certificate()
    edge = next(item for item in certificate.edges if item.edge_id == "e41_runtime_decision")
    wrong_introductions = (LineageBindingV1("validated_decision", _digest("other-decision")),)
    hostile_edge = replace(edge, introductions=wrong_introductions)
    hostile = _build_certificate(
        edges=tuple(
            hostile_edge if item.edge_id == edge.edge_id else item for item in certificate.edges
        )
    )

    verdict = _verify(hostile)

    assert not verdict.accepted
    assert "lineage conflict" in verdict.reason or "target lineage" in verdict.reason


def test_same_stage_edge_cannot_introduce_lineage() -> None:
    certificate = _build_certificate()
    stage_five = next(node for node in certificate.nodes if node.stage == 5)
    hostile_nodes = tuple(
        sorted(
            (
                replace(stage_five, stage=4) if node.node_id == stage_five.node_id else node
                for node in certificate.nodes
            ),
            key=lambda node: node.node_id.encode("utf-8"),
        )
    )
    hostile = _build_certificate(nodes=hostile_nodes, edges=certificate.edges)

    verdict = _verify(hostile)

    assert not verdict.accepted
    assert "same-stage edge introduces" in verdict.reason


def test_gate_metadata_and_role_profile_are_exact() -> None:
    certificate = _build_certificate()
    edge = next(item for item in certificate.edges if item.edge_id == "e50_authorize")
    hostile_edge = replace(edge, gate_label="wrong-gate")
    hostile = _build_certificate(
        edges=tuple(
            hostile_edge if item.edge_id == edge.edge_id else item for item in certificate.edges
        )
    )
    verdict = _verify(hostile)
    assert not verdict.accepted
    assert "gate label" in verdict.reason

    changed_gate = replace(certificate.gates[5], introduction_roles=("other_authority",))
    changed_gates = tuple(
        changed_gate if gate.gate_index == 5 else gate for gate in certificate.gates
    )
    profile_verdict = _verify(certificate, gates=changed_gates)
    assert not profile_verdict.accepted
    assert "gate profile substitution" in profile_verdict.reason


def test_receipt_subject_checker_and_sink_expectation_are_bound() -> None:
    certificate = _build_certificate()
    edge = certificate.edges[0]
    hostile_subject = replace(edge, receipt_subject_digest=_digest("unrelated-subject"))
    hostile = replace(
        certificate,
        edges=tuple(
            hostile_subject if item.edge_id == edge.edge_id else item for item in certificate.edges
        ),
    )
    subject_verdict = _verify(hostile)
    assert not subject_verdict.accepted
    assert "receipt subject" in subject_verdict.reason

    checker_edge = replace(edge, checker_digest=_digest("substituted-checker"))
    checker_hostile = _build_certificate(
        edges=tuple(
            checker_edge if item.edge_id == edge.edge_id else item for item in certificate.edges
        )
    )
    checker_verdict = _verify(
        checker_hostile,
        topology_root=certificate.topology_root,
    )
    assert not checker_verdict.accepted
    assert "topology root" in checker_verdict.reason

    sink_verdict = _verify(certificate, sink_artifact=_digest("wrong-sink"))
    assert not sink_verdict.accepted
    assert "sink artifact substitution" in sink_verdict.reason


def test_parent_edges_must_form_a_spanning_arborescence() -> None:
    certificate = _build_certificate()
    hostile = replace(certificate, parent_edge_ids=certificate.parent_edge_ids[:-1])

    verdict = _verify(hostile)

    assert not verdict.accepted
    assert "arborescence cardinality" in verdict.reason


def test_exact_types_reject_bool_integer_aliases_and_hostile_mutation() -> None:
    with pytest.raises(AuthorityCertificateError, match="exact int"):
        AuthorityGateV1(True, "gate", ("role",))

    certificate = _build_certificate()
    object.__setattr__(certificate.gates[0], "gate_index", True)
    verdict = _verify(certificate)
    assert not verdict.accepted
    assert "exact int" in verdict.reason


def test_partial_lineage_join_rejects_conflicting_sources() -> None:
    base = (LineageBindingV1("state", _digest("state-a")),)
    conflict = (LineageBindingV1("state", _digest("state-b")),)

    with pytest.raises(AuthorityCertificateError, match="lineage conflict"):
        merge_lineage(base, conflict)


def _all_source_sink_paths(certificate: TreeChordGateCertificateV1) -> tuple[tuple[str, ...], ...]:
    outgoing: dict[str, list[AuthorityEdgeV1]] = {}
    for edge in certificate.edges:
        outgoing.setdefault(edge.source_node_id, []).append(edge)
    sink = certificate.sink_node_ids[0]
    paths: list[tuple[str, ...]] = []

    def walk(node_id: str, edge_ids: tuple[str, ...]) -> None:
        if node_id == sink:
            paths.append(edge_ids)
            return
        for edge in sorted(outgoing.get(node_id, ()), key=lambda item: item.edge_id):
            walk(edge.target_node_id, edge_ids + (edge.edge_id,))

    walk(certificate.source_node_id, ())
    return tuple(paths)


def test_every_declared_source_sink_path_crosses_all_gates_in_order() -> None:
    certificate = _build_certificate()
    edge_map = {edge.edge_id: edge for edge in certificate.edges}
    paths = _all_source_sink_paths(certificate)

    assert len(paths) == 8
    expected = tuple(range(len(certificate.gates)))
    for path in paths:
        crossed = tuple(edge_map[edge_id].gate_index for edge_id in path)
        assert crossed == expected
