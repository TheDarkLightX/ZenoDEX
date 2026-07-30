"""Research-only Tree–Chord–Gate authority certificate checker.

The checker represents one authority-bearing runtime instance as a finite rooted
DAG.  A static topology root commits to the complete declared authority graph,
relation/checker identities, theorem-bearing gate profile, sinks, and canonical
arborescence.  A dynamic instance root commits to exact artifact identities,
lineage bindings, and independently checkable edge receipts.

The checker grants no runtime authority.  In particular, it does not establish
that the supplied topology inventory is complete or that an opaque receipt is
sound.  Those values must be anchored and verified by an external FCIS
boundary.  Its purpose is to make the remaining global composition claim small:
local edge receipts plus a complete topology inventory imply declared-path
coherence and ordered gate mediation.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Final, Iterable

MAX_NODES: Final = 256
MAX_EDGES: Final = 1_024
MAX_GATES: Final = 32
MAX_LINEAGE_BINDINGS: Final = 64
MAX_TEXT_BYTES: Final = 128
_HEX = frozenset("0123456789abcdef")
_NONE_GATE = 0xFFFF


class AuthorityCertificateError(ValueError):
    """Raised when a value is outside the closed research language."""


def _exact_int(value: object, name: str) -> int:
    if type(value) is not int:
        raise AuthorityCertificateError(f"{name} must be an exact int")
    return value


def _bounded_text(value: object, name: str) -> str:
    if type(value) is not str:
        raise AuthorityCertificateError(f"{name} must be an exact str")
    try:
        raw = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise AuthorityCertificateError(f"{name} is not valid UTF-8") from exc
    if not raw or len(raw) > MAX_TEXT_BYTES:
        raise AuthorityCertificateError(
            f"{name} must contain 1..{MAX_TEXT_BYTES} UTF-8 bytes"
        )
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise AuthorityCertificateError(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    if type(value) is not str or len(value) != 64 or any(ch not in _HEX for ch in value):
        raise AuthorityCertificateError(
            f"{name} must be 64 lowercase hexadecimal characters"
        )
    return value


def _exact_text_tuple(value: object, name: str, *, nonempty: bool = False) -> tuple[str, ...]:
    if type(value) is not tuple or (nonempty and not value):
        qualifier = "nonempty " if nonempty else ""
        raise AuthorityCertificateError(f"{name} must be a {qualifier}exact tuple")
    checked = tuple(_bounded_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if tuple(sorted(checked, key=lambda item: item.encode("utf-8"))) != checked:
        raise AuthorityCertificateError(f"{name} is not canonically ordered")
    if len(set(checked)) != len(checked):
        raise AuthorityCertificateError(f"{name} contains duplicates")
    return checked


def _hash_fields(domain: str, fields: Iterable[bytes]) -> str:
    encoded_domain = domain.encode("ascii")
    field_tuple = tuple(fields)
    material = bytearray()
    material.extend(len(encoded_domain).to_bytes(2, "big"))
    material.extend(encoded_domain)
    material.extend(len(field_tuple).to_bytes(4, "big"))
    for field in field_tuple:
        material.extend(len(field).to_bytes(8, "big"))
        material.extend(field)
    return sha256(material).hexdigest()


@dataclass(frozen=True, slots=True, order=True)
class LineageBindingV1:
    """One semantic role bound to one independently derived source identity."""

    role: str
    source_digest: str

    def __post_init__(self) -> None:
        _bounded_text(self.role, "role")
        _digest(self.source_digest, "source_digest")


LineageV1 = tuple[LineageBindingV1, ...]


def _validate_lineage(value: object, name: str) -> LineageV1:
    if type(value) is not tuple:
        raise AuthorityCertificateError(f"{name} must be an exact tuple")
    if len(value) > MAX_LINEAGE_BINDINGS:
        raise AuthorityCertificateError(f"{name} exceeds the lineage binding limit")
    checked: list[LineageBindingV1] = []
    for index, item in enumerate(value):
        if type(item) is not LineageBindingV1:
            raise AuthorityCertificateError(f"{name}[{index}] has the wrong exact type")
        item.__post_init__()
        checked.append(item)
    canonical = tuple(sorted(checked, key=lambda item: item.role.encode("utf-8")))
    if tuple(checked) != canonical:
        raise AuthorityCertificateError(f"{name} is not canonically role ordered")
    if len({item.role for item in checked}) != len(checked):
        raise AuthorityCertificateError(f"{name} contains duplicate roles")
    return tuple(checked)


def lineage_root(lineage: LineageV1) -> str:
    checked = _validate_lineage(lineage, "lineage")
    fields: list[bytes] = []
    for binding in checked:
        fields.extend((binding.role.encode("utf-8"), bytes.fromhex(binding.source_digest)))
    return _hash_fields("zenodex/fcis/tcg/lineage/v1", fields)


def merge_lineage(base: LineageV1, introductions: LineageV1) -> LineageV1:
    """Partial agreement join: overlapping roles must bind the same source."""

    base_checked = _validate_lineage(base, "base")
    additions_checked = _validate_lineage(introductions, "introductions")
    merged = {item.role: item.source_digest for item in base_checked}
    for item in additions_checked:
        old = merged.get(item.role)
        if old is not None and old != item.source_digest:
            raise AuthorityCertificateError(f"lineage conflict for role {item.role!r}")
        merged[item.role] = item.source_digest
    return tuple(
        LineageBindingV1(role, digest)
        for role, digest in sorted(merged.items(), key=lambda item: item[0].encode("utf-8"))
    )


@dataclass(frozen=True, slots=True, order=True)
class AuthorityGateV1:
    """One theorem-bearing mediation gate and the roles it must introduce."""

    gate_index: int
    gate_label: str
    introduction_roles: tuple[str, ...]

    def __post_init__(self) -> None:
        index = _exact_int(self.gate_index, "gate_index")
        if index < 0 or index >= MAX_GATES:
            raise AuthorityCertificateError("gate_index is outside the admitted range")
        _bounded_text(self.gate_label, "gate_label")
        _exact_text_tuple(self.introduction_roles, "introduction_roles", nonempty=True)


@dataclass(frozen=True, slots=True, order=True)
class AuthorityNodeV1:
    """One typed authority artifact at one filtration stage."""

    node_id: str
    stage: int
    artifact_digest: str
    lineage: LineageV1

    def __post_init__(self) -> None:
        _bounded_text(self.node_id, "node_id")
        stage = _exact_int(self.stage, "stage")
        if stage < 0 or stage > MAX_GATES:
            raise AuthorityCertificateError("stage is outside the admitted range")
        _digest(self.artifact_digest, "artifact_digest")
        _validate_lineage(self.lineage, "lineage")


@dataclass(frozen=True, slots=True, order=True)
class AuthorityEdgeV1:
    """One locally checked relation between exact source and target artifacts."""

    edge_id: str
    source_node_id: str
    target_node_id: str
    relation_label: str
    checker_digest: str
    introductions: LineageV1
    gate_index: int | None
    gate_label: str | None
    receipt_subject_digest: str
    receipt_digest: str

    def __post_init__(self) -> None:
        _bounded_text(self.edge_id, "edge_id")
        _bounded_text(self.source_node_id, "source_node_id")
        _bounded_text(self.target_node_id, "target_node_id")
        _bounded_text(self.relation_label, "relation_label")
        _digest(self.checker_digest, "checker_digest")
        _validate_lineage(self.introductions, "introductions")
        _digest(self.receipt_subject_digest, "receipt_subject_digest")
        _digest(self.receipt_digest, "receipt_digest")
        if self.gate_index is None:
            if self.gate_label is not None:
                raise AuthorityCertificateError("non-gate edge carries a gate label")
        else:
            index = _exact_int(self.gate_index, "gate_index")
            if index < 0 or index >= MAX_GATES:
                raise AuthorityCertificateError("gate_index is outside the admitted range")
            _bounded_text(self.gate_label, "gate_label")


@dataclass(frozen=True, slots=True, order=True)
class NodeArtifactExpectationV1:
    """External equality target for one authority sink artifact."""

    node_id: str
    artifact_digest: str

    def __post_init__(self) -> None:
        _bounded_text(self.node_id, "node_id")
        _digest(self.artifact_digest, "artifact_digest")


@dataclass(frozen=True, slots=True)
class TreeChordGateCertificateV1:
    """Static authority topology plus one exact dynamic lineage instance."""

    source_node_id: str
    sink_node_ids: tuple[str, ...]
    gates: tuple[AuthorityGateV1, ...]
    nodes: tuple[AuthorityNodeV1, ...]
    edges: tuple[AuthorityEdgeV1, ...]
    parent_edge_ids: tuple[str, ...]
    topology_root: str
    instance_root: str

    def __post_init__(self) -> None:
        _bounded_text(self.source_node_id, "source_node_id")
        _exact_text_tuple(self.sink_node_ids, "sink_node_ids", nonempty=True)
        if type(self.gates) is not tuple or len(self.gates) > MAX_GATES:
            raise AuthorityCertificateError("gates has the wrong shape")
        if type(self.nodes) is not tuple or not 1 <= len(self.nodes) <= MAX_NODES:
            raise AuthorityCertificateError("nodes has the wrong shape")
        if type(self.edges) is not tuple or not 1 <= len(self.edges) <= MAX_EDGES:
            raise AuthorityCertificateError("edges has the wrong shape")
        _exact_text_tuple(self.parent_edge_ids, "parent_edge_ids")
        _digest(self.topology_root, "topology_root")
        _digest(self.instance_root, "instance_root")


@dataclass(frozen=True, slots=True)
class TreeChordGateVerdictV1:
    accepted: bool
    reason: str
    node_count: int = 0
    edge_count: int = 0
    tree_edge_count: int = 0
    chord_receipt_count: int = 0
    gate_crossing_edge_count: int = 0
    topology_root: str | None = None
    instance_root: str | None = None


def _validate_gate_profile(gates: tuple[AuthorityGateV1, ...]) -> tuple[AuthorityGateV1, ...]:
    if type(gates) is not tuple or len(gates) > MAX_GATES:
        raise AuthorityCertificateError("gates has the wrong shape")
    seen_labels: set[str] = set()
    seen_roles: set[str] = set()
    for expected_index, gate in enumerate(gates):
        if type(gate) is not AuthorityGateV1:
            raise AuthorityCertificateError("gate has the wrong exact type")
        gate.__post_init__()
        if gate.gate_index != expected_index:
            raise AuthorityCertificateError("gate indices must be contiguous from zero")
        if gate.gate_label in seen_labels:
            raise AuthorityCertificateError("gate labels must be unique")
        overlap = seen_roles.intersection(gate.introduction_roles)
        if overlap:
            raise AuthorityCertificateError("lineage roles cannot be introduced at two gates")
        seen_labels.add(gate.gate_label)
        seen_roles.update(gate.introduction_roles)
    return gates


def authority_topology_root(
    *,
    source_node_id: str,
    sink_node_ids: tuple[str, ...],
    gates: tuple[AuthorityGateV1, ...],
    nodes: tuple[AuthorityNodeV1, ...],
    edges: tuple[AuthorityEdgeV1, ...],
    parent_edge_ids: tuple[str, ...],
) -> str:
    """Commit to the complete declared graph and all static checker identities."""

    _bounded_text(source_node_id, "source_node_id")
    sinks = _exact_text_tuple(sink_node_ids, "sink_node_ids", nonempty=True)
    checked_gates = _validate_gate_profile(gates)
    parent_ids = _exact_text_tuple(parent_edge_ids, "parent_edge_ids")
    fields: list[bytes] = [source_node_id.encode("utf-8")]
    fields.extend(sink.encode("utf-8") for sink in sinks)
    for gate in checked_gates:
        fields.extend(
            (
                gate.gate_index.to_bytes(2, "big"),
                gate.gate_label.encode("utf-8"),
            )
        )
        fields.extend(role.encode("utf-8") for role in gate.introduction_roles)
    for node in nodes:
        if type(node) is not AuthorityNodeV1:
            raise AuthorityCertificateError("node has the wrong exact type")
        node.__post_init__()
        fields.extend((node.node_id.encode("utf-8"), node.stage.to_bytes(2, "big")))
    for edge in edges:
        if type(edge) is not AuthorityEdgeV1:
            raise AuthorityCertificateError("edge has the wrong exact type")
        edge.__post_init__()
        fields.extend(
            (
                edge.edge_id.encode("utf-8"),
                edge.source_node_id.encode("utf-8"),
                edge.target_node_id.encode("utf-8"),
                edge.relation_label.encode("utf-8"),
                bytes.fromhex(edge.checker_digest),
                (edge.gate_index if edge.gate_index is not None else _NONE_GATE).to_bytes(
                    2, "big"
                ),
                b"" if edge.gate_label is None else edge.gate_label.encode("utf-8"),
            )
        )
        fields.extend(binding.role.encode("utf-8") for binding in edge.introductions)
    fields.extend(edge_id.encode("utf-8") for edge_id in parent_ids)
    return _hash_fields("zenodex/fcis/tcg/topology/v1", fields)


def edge_receipt_subject_root(
    *,
    topology_root: str,
    edge: AuthorityEdgeV1,
    source: AuthorityNodeV1,
    target: AuthorityNodeV1,
) -> str:
    """Bind an edge receipt to its complete exact relation subject."""

    _digest(topology_root, "topology_root")
    edge.__post_init__()
    source.__post_init__()
    target.__post_init__()
    return _hash_fields(
        "zenodex/fcis/tcg/edge-subject/v1",
        (
            bytes.fromhex(topology_root),
            edge.edge_id.encode("utf-8"),
            edge.relation_label.encode("utf-8"),
            bytes.fromhex(edge.checker_digest),
            source.node_id.encode("utf-8"),
            bytes.fromhex(source.artifact_digest),
            bytes.fromhex(lineage_root(source.lineage)),
            target.node_id.encode("utf-8"),
            bytes.fromhex(target.artifact_digest),
            bytes.fromhex(lineage_root(target.lineage)),
            bytes.fromhex(lineage_root(edge.introductions)),
            (edge.gate_index if edge.gate_index is not None else _NONE_GATE).to_bytes(2, "big"),
            b"" if edge.gate_label is None else edge.gate_label.encode("utf-8"),
        ),
    )


def authority_instance_root(
    *,
    topology_root: str,
    nodes: tuple[AuthorityNodeV1, ...],
    edges: tuple[AuthorityEdgeV1, ...],
) -> str:
    """Commit to exact artifacts, lineage, and receipt evidence for one run."""

    _digest(topology_root, "topology_root")
    fields: list[bytes] = [bytes.fromhex(topology_root)]
    for node in nodes:
        node.__post_init__()
        fields.extend(
            (
                node.node_id.encode("utf-8"),
                bytes.fromhex(node.artifact_digest),
                bytes.fromhex(lineage_root(node.lineage)),
            )
        )
    for edge in edges:
        edge.__post_init__()
        fields.extend(
            (
                edge.edge_id.encode("utf-8"),
                bytes.fromhex(lineage_root(edge.introductions)),
                bytes.fromhex(edge.receipt_subject_digest),
                bytes.fromhex(edge.receipt_digest),
            )
        )
    return _hash_fields("zenodex/fcis/tcg/instance/v1", fields)


def _topological_order(
    nodes: dict[str, AuthorityNodeV1], edges: tuple[AuthorityEdgeV1, ...]
) -> tuple[str, ...]:
    incoming = {node_id: 0 for node_id in nodes}
    outgoing: dict[str, list[str]] = {node_id: [] for node_id in nodes}
    for edge in edges:
        incoming[edge.target_node_id] += 1
        outgoing[edge.source_node_id].append(edge.target_node_id)
    frontier = sorted(node_id for node_id, count in incoming.items() if count == 0)
    order: list[str] = []
    while frontier:
        node_id = frontier.pop(0)
        order.append(node_id)
        for target in sorted(outgoing[node_id]):
            incoming[target] -= 1
            if incoming[target] == 0:
                frontier.append(target)
                frontier.sort()
    if len(order) != len(nodes):
        raise AuthorityCertificateError("authority graph contains a directed cycle")
    return tuple(order)


def verify_tree_chord_gate_certificate(
    *,
    expected_topology_root: str,
    expected_instance_root: str,
    expected_source_node_id: str,
    expected_source_artifact_digest: str,
    expected_source_lineage: LineageV1,
    expected_sink_artifacts: tuple[NodeArtifactExpectationV1, ...],
    expected_gates: tuple[AuthorityGateV1, ...],
    certificate: TreeChordGateCertificateV1,
) -> TreeChordGateVerdictV1:
    """Fail closed against externally anchored topology and instance roots."""

    try:
        _digest(expected_topology_root, "expected_topology_root")
        _digest(expected_instance_root, "expected_instance_root")
        _bounded_text(expected_source_node_id, "expected_source_node_id")
        _digest(expected_source_artifact_digest, "expected_source_artifact_digest")
        source_lineage = _validate_lineage(expected_source_lineage, "expected_source_lineage")
        gates = _validate_gate_profile(expected_gates)
        if type(expected_sink_artifacts) is not tuple or not expected_sink_artifacts:
            raise AuthorityCertificateError(
                "expected_sink_artifacts must be a nonempty exact tuple"
            )
        for expectation in expected_sink_artifacts:
            if type(expectation) is not NodeArtifactExpectationV1:
                raise AuthorityCertificateError("sink expectation has the wrong exact type")
            expectation.__post_init__()
        if tuple(sorted(expected_sink_artifacts, key=lambda item: item.node_id)) != (
            expected_sink_artifacts
        ):
            raise AuthorityCertificateError("sink expectations are not canonically ordered")
        if len({item.node_id for item in expected_sink_artifacts}) != len(
            expected_sink_artifacts
        ):
            raise AuthorityCertificateError("sink expectations contain duplicates")
        expected_sink_ids = tuple(item.node_id for item in expected_sink_artifacts)

        if type(certificate) is not TreeChordGateCertificateV1:
            raise AuthorityCertificateError("certificate has the wrong exact type")
        certificate.__post_init__()
        if certificate.topology_root != expected_topology_root:
            raise AuthorityCertificateError("certificate topology root does not match authority")
        if certificate.instance_root != expected_instance_root:
            raise AuthorityCertificateError("certificate instance root does not match authority")
        if certificate.source_node_id != expected_source_node_id:
            raise AuthorityCertificateError("source node substitution")
        if certificate.sink_node_ids != expected_sink_ids:
            raise AuthorityCertificateError("sink node substitution")
        if certificate.gates != gates:
            raise AuthorityCertificateError("gate profile substitution")

        nodes = tuple(certificate.nodes)
        edges = tuple(certificate.edges)
        if tuple(sorted(nodes, key=lambda item: item.node_id.encode("utf-8"))) != nodes:
            raise AuthorityCertificateError("nodes are not canonically ordered")
        if tuple(sorted(edges, key=lambda item: item.edge_id.encode("utf-8"))) != edges:
            raise AuthorityCertificateError("edges are not canonically ordered")

        node_map: dict[str, AuthorityNodeV1] = {}
        for node in nodes:
            if type(node) is not AuthorityNodeV1:
                raise AuthorityCertificateError("node has the wrong exact type")
            node.__post_init__()
            if node.node_id in node_map:
                raise AuthorityCertificateError("duplicate node identifier")
            node_map[node.node_id] = node
        source = node_map.get(certificate.source_node_id)
        if source is None:
            raise AuthorityCertificateError("source node is absent")
        if source.stage != 0:
            raise AuthorityCertificateError("source stage must be zero")
        if source.artifact_digest != expected_source_artifact_digest:
            raise AuthorityCertificateError("source artifact substitution")
        if source.lineage != source_lineage:
            raise AuthorityCertificateError("source lineage substitution")

        source_roles = {binding.role for binding in source.lineage}
        gate_roles: set[str] = set()
        for gate in gates:
            overlap = source_roles.intersection(gate.introduction_roles)
            if overlap:
                raise AuthorityCertificateError("a source role is reintroduced by a gate")
            gate_roles.update(gate.introduction_roles)
        complete_roles = tuple(sorted(source_roles | gate_roles))
        sink_expectation_map = {
            item.node_id: item.artifact_digest for item in expected_sink_artifacts
        }
        final_stage = len(gates)
        for sink_id, expected_digest in sink_expectation_map.items():
            sink = node_map.get(sink_id)
            if sink is None:
                raise AuthorityCertificateError("sink node is absent")
            if sink.stage != final_stage:
                raise AuthorityCertificateError("sink is not at the final gate stage")
            if sink.artifact_digest != expected_digest:
                raise AuthorityCertificateError("sink artifact substitution")
            sink_roles = tuple(binding.role for binding in sink.lineage)
            if sink_roles != complete_roles:
                raise AuthorityCertificateError("sink lineage is not the complete gate lineage")

        edge_map: dict[str, AuthorityEdgeV1] = {}
        incoming_by_node: dict[str, list[str]] = {node_id: [] for node_id in node_map}
        gate_edges = 0
        for edge in edges:
            if type(edge) is not AuthorityEdgeV1:
                raise AuthorityCertificateError("edge has the wrong exact type")
            edge.__post_init__()
            if edge.edge_id in edge_map:
                raise AuthorityCertificateError("duplicate edge identifier")
            source_node = node_map.get(edge.source_node_id)
            target_node = node_map.get(edge.target_node_id)
            if source_node is None or target_node is None:
                raise AuthorityCertificateError("edge endpoint is absent")
            if edge.source_node_id == edge.target_node_id:
                raise AuthorityCertificateError("self edge is forbidden")
            if target_node.stage not in (source_node.stage, source_node.stage + 1):
                raise AuthorityCertificateError("edge skips or reverses an authority stage")
            derived_lineage = merge_lineage(source_node.lineage, edge.introductions)
            if derived_lineage != target_node.lineage:
                raise AuthorityCertificateError("edge does not reconstruct target lineage")
            if target_node.stage == source_node.stage:
                if edge.introductions:
                    raise AuthorityCertificateError(
                        "same-stage edge introduces a new lineage source"
                    )
                if edge.gate_index is not None or edge.gate_label is not None:
                    raise AuthorityCertificateError("same-stage edge claims a gate crossing")
            else:
                gate_edges += 1
                gate = gates[source_node.stage]
                if edge.gate_index != gate.gate_index:
                    raise AuthorityCertificateError(
                        "gate index does not equal the crossed stage"
                    )
                if edge.gate_label != gate.gate_label:
                    raise AuthorityCertificateError(
                        "gate label does not match the authority filtration"
                    )
                introduction_roles = tuple(binding.role for binding in edge.introductions)
                if introduction_roles != gate.introduction_roles:
                    raise AuthorityCertificateError(
                        "gate crossing does not introduce its exact role set"
                    )
            expected_subject = edge_receipt_subject_root(
                topology_root=certificate.topology_root,
                edge=edge,
                source=source_node,
                target=target_node,
            )
            if edge.receipt_subject_digest != expected_subject:
                raise AuthorityCertificateError("edge receipt subject does not rederive")
            edge_map[edge.edge_id] = edge
            incoming_by_node[edge.target_node_id].append(edge.edge_id)

        _topological_order(node_map, edges)
        if incoming_by_node[certificate.source_node_id]:
            raise AuthorityCertificateError("source node has an incoming edge")
        reachable = {certificate.source_node_id}
        changed = True
        while changed:
            changed = False
            for edge in edges:
                if edge.source_node_id in reachable and edge.target_node_id not in reachable:
                    reachable.add(edge.target_node_id)
                    changed = True
        if reachable != set(node_map):
            raise AuthorityCertificateError(
                "graph contains a node unreachable from the authority source"
            )

        parent_ids = _exact_text_tuple(certificate.parent_edge_ids, "parent_edge_ids")
        if len(parent_ids) != len(nodes) - 1:
            raise AuthorityCertificateError(
                "parent edge set is not an arborescence cardinality"
            )
        parent_target: dict[str, str] = {}
        for edge_id in parent_ids:
            edge = edge_map.get(edge_id)
            if edge is None:
                raise AuthorityCertificateError("parent edge is absent from the graph")
            if edge.target_node_id == certificate.source_node_id:
                raise AuthorityCertificateError("source cannot have a parent edge")
            if edge.target_node_id in parent_target:
                raise AuthorityCertificateError("node has more than one parent edge")
            parent_target[edge.target_node_id] = edge_id
        if set(parent_target) != set(node_map) - {certificate.source_node_id}:
            raise AuthorityCertificateError(
                "parent edge set does not span every non-source node"
            )

        recomputed_topology = authority_topology_root(
            source_node_id=certificate.source_node_id,
            sink_node_ids=certificate.sink_node_ids,
            gates=certificate.gates,
            nodes=nodes,
            edges=edges,
            parent_edge_ids=parent_ids,
        )
        if recomputed_topology != certificate.topology_root:
            raise AuthorityCertificateError("topology root does not rederive")
        recomputed_instance = authority_instance_root(
            topology_root=certificate.topology_root,
            nodes=nodes,
            edges=edges,
        )
        if recomputed_instance != certificate.instance_root:
            raise AuthorityCertificateError("instance root does not rederive")

        return TreeChordGateVerdictV1(
            accepted=True,
            reason="PASS",
            node_count=len(nodes),
            edge_count=len(edges),
            tree_edge_count=len(parent_ids),
            chord_receipt_count=len(edges) - len(parent_ids),
            gate_crossing_edge_count=gate_edges,
            topology_root=certificate.topology_root,
            instance_root=certificate.instance_root,
        )
    except AuthorityCertificateError as exc:
        return TreeChordGateVerdictV1(accepted=False, reason=str(exc))


__all__ = (
    "AuthorityCertificateError",
    "AuthorityEdgeV1",
    "AuthorityGateV1",
    "AuthorityNodeV1",
    "LineageBindingV1",
    "NodeArtifactExpectationV1",
    "TreeChordGateCertificateV1",
    "TreeChordGateVerdictV1",
    "authority_instance_root",
    "authority_topology_root",
    "edge_receipt_subject_root",
    "lineage_root",
    "merge_lineage",
    "verify_tree_chord_gate_certificate",
)
