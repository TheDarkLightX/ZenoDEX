"""Bounded exact treewidth replay paired with canonical ZRPF subcube coverage.

This is a research reference model. It derives every bag, separator, factor
owner, message table, and ZRPF ordinal manifest from exact source values. The
returned receipt has no settlement or production authority.
"""

from __future__ import annotations

import hashlib
import json
import struct
from dataclasses import dataclass
from itertools import product

from experiments.choice_fiber_robustness_v1.named_choice_fiber import (
    ChoiceFiberError,
    ChoiceFiberPolynomial,
    _owned_polynomial_snapshot,
)
from experiments.choice_fiber_treewidth_certificate_v1.source_identity import (
    TREEWIDTH_SOURCE_SHA256,
)
from experiments.zrpf_choice_subcube_coverage_v1.subcube_certificate import (
    CertificateReject,
    CoverageCertificate,
    Leaf,
    ShardReceipt,
    Split,
    Subcube,
    Tree,
    build_canonical_certificate,
    verify_certificate,
)
from experiments.zrpf_choice_subcube_coverage_v1.subcube_certificate import (
    ChoiceManifest as CoverageChoiceManifest,
)

Digest = bytes
MAX_IDENTIFIER_BYTES = 128
MAX_ELIMINATION_CHOICES = 256
MAX_SCOPES = 256
MAX_INDUCED_WIDTH = 12
MAX_AGGREGATE_DP_WORK = 20_000_000
MAX_AGGREGATE_MESSAGE_CELLS = 50_000
MAX_AGGREGATE_FILL_PROBES = 1_000_000
MAX_PROJECTION_INCIDENCE_VISITS = 1_000_000
MAX_ARITHMETIC_BITS = 512
MAX_BRUTE_FREE_CHOICES = 16
MAX_BRUTE_WORK = 20_000_000

ROBUSTNESS_SOURCE_SHA256 = "2b6994aaba35f3625ac0146eef9582660d871ccfcae6ac91a6eb3aaa3e74b798"
ZRPF_SOURCE_SHA256 = "cd2e5a5f29ec0b4a9a937e2926901114ecc3656de11ebaa16567cdbd1ef3a643"


class TreewidthReject(ValueError):
    """Typed research rejection with a stable machine-readable code."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


def _u32(value: int) -> bytes:
    if type(value) is not int or value < 0 or value > 0xFFFF_FFFF:
        raise TreewidthReject("U32_OUT_OF_RANGE")
    return struct.pack(">I", value)


def _frame(value: bytes) -> bytes:
    return _u32(len(value)) + value


def _canonical(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")


def _hash(domain: str, value: object) -> Digest:
    tag = domain.encode("ascii")
    payload = _canonical(value)
    return hashlib.sha256(_frame(tag) + _frame(payload)).digest()


def _require_digest(value: object, code: str) -> Digest:
    if type(value) is not bytes or len(value) != 32:
        raise TreewidthReject(code)
    return value


def _require_text(value: object, code: str) -> str:
    if type(value) is not str or not value:
        raise TreewidthReject(code)
    try:
        encoded = value.encode("utf-8")
    except UnicodeError as error:
        raise TreewidthReject(code) from error
    if len(encoded) > MAX_IDENTIFIER_BYTES:
        raise TreewidthReject(code)
    return value


def _require_assignment(
    value: object,
    code: str,
    expected_choices: tuple[str, ...] | None = None,
) -> tuple[tuple[str, int], ...]:
    if type(value) is not tuple or len(value) > MAX_ELIMINATION_CHOICES:
        raise TreewidthReject(code)
    previous = ""
    retained: list[tuple[str, int]] = []
    for item in value:
        if (
            type(item) is not tuple
            or len(item) != 2
            or type(item[1]) is not int
            or item[1] not in (-1, 1)
        ):
            raise TreewidthReject(code)
        choice_id = _require_text(item[0], code)
        if choice_id <= previous:
            raise TreewidthReject(code)
        previous = choice_id
        retained.append((choice_id, item[1]))
    result = tuple(retained)
    if expected_choices is not None and tuple(choice for choice, _ in result) != expected_choices:
        raise TreewidthReject(code)
    return result


def _polynomial_root(polynomial: ChoiceFiberPolynomial) -> Digest:
    try:
        return bytes.fromhex(polynomial.root)
    except (TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_POLYNOMIAL_ROOT") from error


def _semantic_root(polynomial: ChoiceFiberPolynomial) -> Digest:
    try:
        return bytes.fromhex(polynomial.semantic_root)
    except (TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_POLYNOMIAL_ROOT") from error


def _lineage_root(polynomial: ChoiceFiberPolynomial) -> Digest:
    try:
        return bytes.fromhex(polynomial.lineage_root)
    except (TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_POLYNOMIAL_ROOT") from error


def _own_polynomial(value: object) -> ChoiceFiberPolynomial:
    try:
        return _owned_polynomial_snapshot(value)
    except (ChoiceFiberError, AttributeError, TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_POLYNOMIAL") from error


def _coverage_manifest(polynomial: ChoiceFiberPolynomial) -> CoverageChoiceManifest:
    try:
        return CoverageChoiceManifest(tuple(polynomial.manifest.choice_ids))
    except (CertificateReject, UnicodeError, AttributeError, TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_DERIVED_COVERAGE_MANIFEST") from error


def _own_scope(value: object, nchoices: int) -> Subcube:
    if type(value) is not Subcube:
        raise TreewidthReject("INVALID_SUBCUBE_SCOPE")
    try:
        scope = Subcube(value.fixed_mask, value.positive_mask)
        scope.validate(nchoices)
    except (CertificateReject, AttributeError, TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_SUBCUBE_SCOPE") from error
    return scope


def _scope_value(scope: Subcube) -> dict[str, int]:
    return {
        "fixed_mask": scope.fixed_mask,
        "positive_mask": scope.positive_mask,
    }


@dataclass(frozen=True, slots=True)
class EliminationOrderV1:
    """One complete source-bound order; bags and separators are derived."""

    choice_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.choice_ids) is not tuple:
            raise TreewidthReject("INVALID_ELIMINATION_ORDER")
        if not self.choice_ids or len(self.choice_ids) > MAX_ELIMINATION_CHOICES:
            raise TreewidthReject("INVALID_ELIMINATION_ORDER")
        retained = tuple(
            _require_text(choice_id, "INVALID_ELIMINATION_ORDER") for choice_id in self.choice_ids
        )
        if len(set(retained)) != len(retained):
            raise TreewidthReject("DUPLICATE_ELIMINATION_CHOICE")

    @property
    def root(self) -> Digest:
        return _hash(
            "zenodex.choice-fiber.elimination-order.v1",
            {"choice_ids": self.choice_ids},
        )


def _own_order(value: object, expected_choices: tuple[str, ...]) -> EliminationOrderV1:
    if type(value) is not EliminationOrderV1 or type(value.choice_ids) is not tuple:
        raise TreewidthReject("INVALID_ELIMINATION_ORDER")
    order = EliminationOrderV1(tuple(value.choice_ids))
    if len(order.choice_ids) != len(expected_choices) or set(order.choice_ids) != set(
        expected_choices
    ):
        raise TreewidthReject("ELIMINATION_ORDER_DOMAIN_MISMATCH")
    return order


@dataclass(frozen=True, slots=True)
class CoveragePlanV1:
    """Canonical tuple of subcube scopes; proof evidence is derived later."""

    scopes: tuple[Subcube, ...]

    def __post_init__(self) -> None:
        if type(self.scopes) is not tuple or not self.scopes:
            raise TreewidthReject("INVALID_COVERAGE_PLAN")
        if len(self.scopes) > MAX_SCOPES:
            raise TreewidthReject("COVERAGE_SCOPE_CAPACITY_EXCEEDED")
        if any(type(scope) is not Subcube for scope in self.scopes):
            raise TreewidthReject("INVALID_COVERAGE_PLAN")
        keys = tuple((scope.fixed_mask, scope.positive_mask) for scope in self.scopes)
        if tuple(sorted(keys)) != keys:
            raise TreewidthReject("NONCANONICAL_SCOPE_ORDER")
        if len(set(keys)) != len(keys):
            raise TreewidthReject("DUPLICATE_SUBCUBE_SCOPE")

    def root(self, manifest: CoverageChoiceManifest) -> Digest:
        return _hash(
            "zenodex.choice-fiber.coverage-plan.v1",
            {
                "manifest_root": manifest.root.hex(),
                "scopes": [_scope_value(scope) for scope in self.scopes],
            },
        )


def prefix_coverage_plan(nchoices: int, depth: int) -> CoveragePlanV1:
    if (
        type(nchoices) is not int
        or type(depth) is not int
        or nchoices <= 0
        or nchoices > MAX_ELIMINATION_CHOICES
        or depth < 0
        or depth > nchoices
        or (1 << depth) > MAX_SCOPES
    ):
        raise TreewidthReject("INVALID_PREFIX_COVERAGE_DEPTH")
    fixed = (1 << depth) - 1
    return CoveragePlanV1(tuple(Subcube(fixed, assignment) for assignment in range(1 << depth)))


def _own_plan(value: object, nchoices: int) -> CoveragePlanV1:
    if type(value) is not CoveragePlanV1 or type(value.scopes) is not tuple:
        raise TreewidthReject("INVALID_COVERAGE_PLAN")
    if not value.scopes or len(value.scopes) > MAX_SCOPES:
        raise TreewidthReject("COVERAGE_SCOPE_CAPACITY_EXCEEDED")
    scopes = tuple(_own_scope(scope, nchoices) for scope in value.scopes)
    return CoveragePlanV1(scopes)


@dataclass(frozen=True, slots=True)
class VerifierProfileV1:
    profile_id: str
    algorithm_id: str
    max_induced_width: int
    max_aggregate_dp_work: int
    max_aggregate_message_cells: int
    max_aggregate_fill_probes: int
    treewidth_source_sha256: str
    robustness_source_sha256: str
    zrpf_source_sha256: str

    def __post_init__(self) -> None:
        _require_text(self.profile_id, "INVALID_VERIFIER_PROFILE")
        _require_text(self.algorithm_id, "INVALID_VERIFIER_PROFILE")
        integer_fields = (
            self.max_induced_width,
            self.max_aggregate_dp_work,
            self.max_aggregate_message_cells,
            self.max_aggregate_fill_probes,
        )
        if any(type(value) is not int or value <= 0 for value in integer_fields):
            raise TreewidthReject("INVALID_VERIFIER_PROFILE")
        for digest in (
            self.treewidth_source_sha256,
            self.robustness_source_sha256,
            self.zrpf_source_sha256,
        ):
            if (
                type(digest) is not str
                or len(digest) != 64
                or any(character not in "0123456789abcdef" for character in digest)
            ):
                raise TreewidthReject("INVALID_VERIFIER_PROFILE")

    @property
    def root(self) -> Digest:
        return _hash(
            "zenodex.choice-fiber.treewidth-verifier-profile.v1",
            {
                "algorithm_id": self.algorithm_id,
                "coverage_mode": "canonical_recursive_subcube_partition",
                "max_arithmetic_bits": MAX_ARITHMETIC_BITS,
                "max_aggregate_dp_work": self.max_aggregate_dp_work,
                "max_aggregate_fill_probes": self.max_aggregate_fill_probes,
                "max_aggregate_message_cells": self.max_aggregate_message_cells,
                "max_elimination_choices": MAX_ELIMINATION_CHOICES,
                "max_identifier_bytes": MAX_IDENTIFIER_BYTES,
                "max_induced_width": self.max_induced_width,
                "max_projection_incidence_visits": MAX_PROJECTION_INCIDENCE_VISITS,
                "max_scopes": MAX_SCOPES,
                "profile_id": self.profile_id,
                "receipt_backend": "PYTHON_REFERENCE_REPLAY",
                "robustness_source_sha256": self.robustness_source_sha256,
                "treewidth_source_sha256": self.treewidth_source_sha256,
                "zrpf_source_sha256": self.zrpf_source_sha256,
            },
        )


DEFAULT_PROFILE = VerifierProfileV1(
    profile_id="choice-fiber-treewidth-reference-v1",
    algorithm_id="scoped-elimination-message-dp-v1",
    max_induced_width=MAX_INDUCED_WIDTH,
    max_aggregate_dp_work=MAX_AGGREGATE_DP_WORK,
    max_aggregate_message_cells=MAX_AGGREGATE_MESSAGE_CELLS,
    max_aggregate_fill_probes=MAX_AGGREGATE_FILL_PROBES,
    treewidth_source_sha256=TREEWIDTH_SOURCE_SHA256,
    robustness_source_sha256=ROBUSTNESS_SOURCE_SHA256,
    zrpf_source_sha256=ZRPF_SOURCE_SHA256,
)


def _own_profile(value: object) -> VerifierProfileV1:
    if type(value) is not VerifierProfileV1:
        raise TreewidthReject("INVALID_VERIFIER_PROFILE")
    try:
        profile = VerifierProfileV1(
            value.profile_id,
            value.algorithm_id,
            value.max_induced_width,
            value.max_aggregate_dp_work,
            value.max_aggregate_message_cells,
            value.max_aggregate_fill_probes,
            value.treewidth_source_sha256,
            value.robustness_source_sha256,
            value.zrpf_source_sha256,
        )
    except (AttributeError, TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_VERIFIER_PROFILE") from error
    if profile != DEFAULT_PROFILE:
        raise TreewidthReject("FOREIGN_VERIFIER_PROFILE")
    return profile


@dataclass(frozen=True, slots=True)
class TreewidthCoverageRequestV1:
    """Untrusted request. Verification deep-owns and rederives every output."""

    claim_context_root: Digest
    polynomial: ChoiceFiberPolynomial
    elimination_order: EliminationOrderV1
    coverage_plan: CoveragePlanV1
    profile: VerifierProfileV1 = DEFAULT_PROFILE

    def __post_init__(self) -> None:
        _require_digest(self.claim_context_root, "INVALID_CLAIM_CONTEXT_ROOT")
        if type(self.polynomial) is not ChoiceFiberPolynomial:
            raise TreewidthReject("INVALID_POLYNOMIAL")
        if type(self.elimination_order) is not EliminationOrderV1:
            raise TreewidthReject("INVALID_ELIMINATION_ORDER")
        if type(self.coverage_plan) is not CoveragePlanV1:
            raise TreewidthReject("INVALID_COVERAGE_PLAN")
        if type(self.profile) is not VerifierProfileV1:
            raise TreewidthReject("INVALID_VERIFIER_PROFILE")


@dataclass(frozen=True, slots=True, order=True)
class ScopedTermV1:
    choices: tuple[str, ...]
    coefficient: int


@dataclass(frozen=True, slots=True)
class ScopedProjectionV1:
    free_choices: tuple[str, ...]
    constant: int
    terms: tuple[ScopedTermV1, ...]
    semantic_root: Digest
    lineage_root: Digest


def _scope_fixed_assignment(
    choices: tuple[str, ...],
    scope: Subcube,
) -> dict[str, int]:
    fixed: dict[str, int] = {}
    for ordinal, choice_id in enumerate(choices):
        bit = 1 << ordinal
        if scope.fixed_mask & bit:
            fixed[choice_id] = 1 if scope.positive_mask & bit else -1
    return fixed


def _project_polynomial(
    polynomial: ChoiceFiberPolynomial,
    scope: Subcube,
) -> ScopedProjectionV1:
    choices = polynomial.manifest.choice_ids
    fixed = _scope_fixed_assignment(choices, scope)
    coefficients: dict[tuple[str, ...], int] = {}
    lineage: list[object] = []
    for term in polynomial.terms:
        coefficient = term.coefficient
        free: list[str] = []
        substitutions: list[tuple[str, int]] = []
        for choice_id in term.choices:
            sign = fixed.get(choice_id)
            if sign is None:
                free.append(choice_id)
            else:
                coefficient *= sign
                substitutions.append((choice_id, sign))
        free_tuple = tuple(free)
        coefficients[free_tuple] = coefficients.get(free_tuple, 0) + coefficient
        lineage.append(
            {
                "projected_choices": free_tuple,
                "projected_coefficient": coefficient,
                "source_choices": term.choices,
                "source_coefficient": term.coefficient,
                "substitutions": substitutions,
            }
        )
    constant = coefficients.pop((), 0)
    terms = tuple(
        ScopedTermV1(term_choices, coefficient)
        for term_choices, coefficient in sorted(coefficients.items())
        if coefficient != 0
    )
    free_choices = tuple(choice for choice in choices if choice not in fixed)
    semantic = _hash(
        "zenodex.choice-fiber.scoped-polynomial.semantic.v1",
        {
            "constant": constant,
            "free_choices": free_choices,
            "terms": [(term.choices, term.coefficient) for term in terms],
        },
    )
    lineage_root = _hash(
        "zenodex.choice-fiber.scoped-polynomial.lineage.v1",
        {
            "polynomial_root": polynomial.root,
            "scope": _scope_value(scope),
            "source_contributions": lineage,
        },
    )
    return ScopedProjectionV1(free_choices, constant, terms, semantic, lineage_root)


@dataclass(frozen=True, slots=True)
class EliminationNodeV1:
    choice_id: str
    separator: tuple[str, ...]
    parent_choice_id: str
    owned_term_indexes: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class DerivedDecompositionV1:
    nodes: tuple[EliminationNodeV1, ...]
    roots: tuple[str, ...]
    induced_width: int
    fill_probes: int
    root: Digest


def _derive_decomposition(
    projection: ScopedProjectionV1,
    order: EliminationOrderV1,
    profile: VerifierProfileV1,
    fill_budget_remaining: int,
) -> DerivedDecompositionV1:
    free_set = set(projection.free_choices)
    free_order = tuple(choice for choice in order.choice_ids if choice in free_set)
    if set(free_order) != free_set or len(free_order) != len(free_set):
        raise TreewidthReject("SCOPED_ELIMINATION_ORDER_MISMATCH")
    rank = {choice: index for index, choice in enumerate(free_order)}
    ordinal = {choice: index for index, choice in enumerate(order.choice_ids)}
    adjacency: dict[str, set[str]] = {choice: set() for choice in free_order}
    primal_probes = sum(
        len(term.choices) * (len(term.choices) - 1) // 2 for term in projection.terms
    )
    if primal_probes > fill_budget_remaining:
        raise TreewidthReject("FILL_PROBE_CAPACITY_EXCEEDED")
    fill_probes = primal_probes
    for term in projection.terms:
        for left_index, left in enumerate(term.choices):
            for right in term.choices[left_index + 1 :]:
                adjacency[left].add(right)
                adjacency[right].add(left)

    separators: dict[str, tuple[str, ...]] = {}
    parents: dict[str, str] = {}
    induced_width = 0
    for choice_id in free_order:
        neighbors = tuple(sorted(adjacency[choice_id], key=ordinal.__getitem__))
        induced_width = max(induced_width, len(neighbors))
        if induced_width > profile.max_induced_width:
            raise TreewidthReject("INDUCED_WIDTH_CAPACITY_EXCEEDED")
        separators[choice_id] = neighbors
        if neighbors:
            parents[choice_id] = min(neighbors, key=rank.__getitem__)
        pair_count = len(neighbors) * (len(neighbors) - 1) // 2
        fill_probes += pair_count
        if fill_probes > fill_budget_remaining:
            raise TreewidthReject("FILL_PROBE_CAPACITY_EXCEEDED")
        for left_index, left in enumerate(neighbors):
            for right in neighbors[left_index + 1 :]:
                adjacency[left].add(right)
                adjacency[right].add(left)
        for neighbor in neighbors:
            adjacency[neighbor].discard(choice_id)
        adjacency[choice_id].clear()

    owned: dict[str, list[int]] = {choice: [] for choice in free_order}
    for term_index, term in enumerate(projection.terms):
        owner = min(term.choices, key=rank.__getitem__)
        if not set(term.choices).issubset({owner, *separators[owner]}):
            raise TreewidthReject("INTERNAL_TERM_OWNER_BAG_MISMATCH")
        owned[owner].append(term_index)

    nodes = tuple(
        EliminationNodeV1(
            choice_id,
            separators[choice_id],
            parents.get(choice_id, ""),
            tuple(owned[choice_id]),
        )
        for choice_id in free_order
    )
    roots = tuple(choice for choice in free_order if choice not in parents)
    node_by_choice = {node.choice_id: node for node in nodes}
    for node in nodes:
        if not node.parent_choice_id:
            continue
        parent = node_by_choice[node.parent_choice_id]
        if not set(node.separator).issubset({parent.choice_id, *parent.separator}):
            raise TreewidthReject("INTERNAL_SEPARATOR_PARENT_MISMATCH")
    decomposition_root = _hash(
        "zenodex.choice-fiber.derived-elimination-decomposition.v1",
        {
            "induced_width": induced_width,
            "nodes": [
                {
                    "choice_id": node.choice_id,
                    "owned_term_indexes": node.owned_term_indexes,
                    "parent_choice_id": node.parent_choice_id,
                    "separator": node.separator,
                }
                for node in nodes
            ],
            "roots": roots,
        },
    )
    return DerivedDecompositionV1(
        nodes,
        roots,
        induced_width,
        fill_probes,
        decomposition_root,
    )


@dataclass(frozen=True, slots=True, order=True)
class MessageEntryV1:
    separator_mask: int
    minimum: int
    interior_assignment: tuple[tuple[str, int], ...]


@dataclass(frozen=True, slots=True)
class NodeMessageV1:
    choice_id: str
    separator: tuple[str, ...]
    entries: tuple[MessageEntryV1, ...]


@dataclass(frozen=True, slots=True)
class ScopedMinimumV1:
    minimum: int
    assignment: tuple[tuple[str, int], ...]
    decomposition_root: Digest
    projection_semantic_root: Digest
    projection_lineage_root: Digest
    message_root: Digest
    induced_width: int
    work_units: int
    message_cells: int
    fill_probes: int

    def __post_init__(self) -> None:
        if type(self.minimum) is not int:
            raise TreewidthReject("INVALID_SCOPED_MINIMUM")
        _require_assignment(self.assignment, "INVALID_SCOPED_MINIMUM")
        for digest in (
            self.decomposition_root,
            self.projection_semantic_root,
            self.projection_lineage_root,
            self.message_root,
        ):
            _require_digest(digest, "INVALID_SCOPED_MINIMUM")
        counters = (
            self.induced_width,
            self.work_units,
            self.message_cells,
            self.fill_probes,
        )
        if any(type(value) is not int or value < 0 for value in counters):
            raise TreewidthReject("INVALID_SCOPED_MINIMUM")


@dataclass(frozen=True, slots=True)
class _PreflightV1:
    projection: ScopedProjectionV1
    decomposition: DerivedDecompositionV1
    children: dict[str, tuple[str, ...]]
    node_by_choice: dict[str, EliminationNodeV1]
    subtree_choice_orders: dict[str, tuple[str, ...]]
    work_units: int
    message_cells: int


def _children(decomposition: DerivedDecompositionV1) -> dict[str, tuple[str, ...]]:
    pending: dict[str, list[str]] = {node.choice_id: [] for node in decomposition.nodes}
    for node in decomposition.nodes:
        if node.parent_choice_id:
            pending[node.parent_choice_id].append(node.choice_id)
    return {key: tuple(value) for key, value in pending.items()}


def _subtree_sizes(
    decomposition: DerivedDecompositionV1,
    children: dict[str, tuple[str, ...]],
) -> dict[str, int]:
    sizes: dict[str, int] = {}
    for node in decomposition.nodes:
        sizes[node.choice_id] = 1 + sum(sizes[child] for child in children[node.choice_id])
    return sizes


def _subtree_choice_orders(
    decomposition: DerivedDecompositionV1,
    children: dict[str, tuple[str, ...]],
    manifest_choices: tuple[str, ...],
) -> tuple[dict[str, tuple[str, ...]], int]:
    subtree_sets: dict[str, set[str]] = {}
    orders: dict[str, tuple[str, ...]] = {}
    work_units = 0
    for node in decomposition.nodes:
        subtree = {node.choice_id}
        work_units += 1
        for child in children[node.choice_id]:
            subtree.update(subtree_sets[child])
            work_units += len(subtree_sets[child])
        subtree_sets[node.choice_id] = subtree
        orders[node.choice_id] = tuple(
            choice_id for choice_id in manifest_choices if choice_id in subtree
        )
        work_units += len(manifest_choices)
    return orders, work_units


def _preflight_scope(
    polynomial: ChoiceFiberPolynomial,
    order: EliminationOrderV1,
    scope: Subcube,
    profile: VerifierProfileV1,
    fill_budget_remaining: int,
) -> _PreflightV1:
    projection = _project_polynomial(polynomial, scope)
    absolute_sum = abs(projection.constant) + sum(
        abs(term.coefficient) for term in projection.terms
    )
    if absolute_sum.bit_length() > MAX_ARITHMETIC_BITS:
        raise TreewidthReject("ARITHMETIC_CAPACITY_EXCEEDED")
    decomposition = _derive_decomposition(
        projection,
        order,
        profile,
        fill_budget_remaining,
    )
    children = _children(decomposition)
    sizes = _subtree_sizes(decomposition, children)
    subtree_choice_orders, order_work = _subtree_choice_orders(
        decomposition,
        children,
        polynomial.manifest.choice_ids,
    )
    node_by_choice = {node.choice_id: node for node in decomposition.nodes}
    term_by_index = projection.terms
    manifest_size = len(polynomial.manifest.choice_ids)
    original_incidence = sum(max(1, len(term.choices)) for term in polynomial.terms)
    work_units = 4 * manifest_size + original_incidence + order_work
    message_cells = 0
    for node in decomposition.nodes:
        cells = 1 << len(node.separator)
        message_cells += cells
        local_incidence = sum(
            max(1, len(term_by_index[index].choices)) for index in node.owned_term_indexes
        )
        child_merge_atoms = sum(sizes[child] for child in children[node.choice_id])
        child_separator_atoms = sum(
            len(node_by_choice[child].separator) for child in children[node.choice_id]
        )
        work_units += cells * (
            len(node.separator)
            + 2
            * (
                2
                + len(node.separator)
                + local_incidence
                + len(children[node.choice_id])
                + child_merge_atoms
                + child_separator_atoms
                + sizes[node.choice_id]
            )
            + 2 * sizes[node.choice_id]
            + 2
        )
        work_units += 1 + len(node.separator)
    return _PreflightV1(
        projection,
        decomposition,
        children,
        node_by_choice,
        subtree_choice_orders,
        work_units,
        message_cells,
    )


def _assignment_from_mask(choices: tuple[str, ...], mask: int) -> dict[str, int]:
    return {
        choice_id: (1 if mask & (1 << index) else -1) for index, choice_id in enumerate(choices)
    }


def _solve_preflight(
    polynomial: ChoiceFiberPolynomial,
    scope: Subcube,
    preflight: _PreflightV1,
) -> ScopedMinimumV1:
    projection = preflight.projection
    decomposition = preflight.decomposition
    nodes = preflight.node_by_choice
    children = preflight.children
    subtree_choice_orders = preflight.subtree_choice_orders
    messages: dict[str, tuple[MessageEntryV1, ...]] = {}
    lookup: dict[tuple[str, int], MessageEntryV1] = {}
    manifest_choices = polynomial.manifest.choice_ids

    for node in decomposition.nodes:
        entries: list[MessageEntryV1] = []
        for separator_mask in range(1 << len(node.separator)):
            separator_assignment = _assignment_from_mask(node.separator, separator_mask)
            best: tuple[int, tuple[tuple[str, int], ...]] | None = None
            for sign in (-1, 1):
                bag_assignment = dict(separator_assignment)
                bag_assignment[node.choice_id] = sign
                value = 0
                for term_index in node.owned_term_indexes:
                    term = projection.terms[term_index]
                    term_value = term.coefficient
                    for choice_id in term.choices:
                        term_value *= bag_assignment[choice_id]
                    value += term_value
                interior: dict[str, int] = {node.choice_id: sign}
                for child_choice in children[node.choice_id]:
                    child = nodes[child_choice]
                    child_mask = sum(
                        (1 << index)
                        for index, item in enumerate(child.separator)
                        if bag_assignment[item] == 1
                    )
                    child_entry = lookup[(child_choice, child_mask)]
                    value += child_entry.minimum
                    for choice_id, child_sign in child_entry.interior_assignment:
                        if choice_id in interior and interior[choice_id] != child_sign:
                            raise TreewidthReject("INTERNAL_ASSIGNMENT_CONFLICT")
                        interior[choice_id] = child_sign
                ordered_interior = tuple(
                    (choice_id, interior[choice_id])
                    for choice_id in subtree_choice_orders[node.choice_id]
                )
                candidate = (value, ordered_interior)
                if best is None or candidate < best:
                    best = candidate
            if best is None:
                raise TreewidthReject("INTERNAL_EMPTY_MESSAGE_CELL")
            entry = MessageEntryV1(separator_mask, best[0], best[1])
            entries.append(entry)
            lookup[(node.choice_id, separator_mask)] = entry
        messages[node.choice_id] = tuple(entries)

    free_assignment: dict[str, int] = {}
    minimum = projection.constant
    for root_choice in decomposition.roots:
        root_entry = messages[root_choice][0]
        minimum += root_entry.minimum
        for choice_id, sign in root_entry.interior_assignment:
            free_assignment[choice_id] = sign
    fixed = _scope_fixed_assignment(manifest_choices, scope)
    complete = dict(fixed)
    complete.update(free_assignment)
    assignment = tuple((choice, complete[choice]) for choice in manifest_choices)
    _require_assignment(assignment, "INTERNAL_INCOMPLETE_ASSIGNMENT", manifest_choices)
    if polynomial.evaluate(dict(assignment)) != minimum:
        raise TreewidthReject("INTERNAL_MINIMUM_EVALUATION_MISMATCH")

    transcript = tuple(
        NodeMessageV1(nodes[choice].choice_id, nodes[choice].separator, messages[choice])
        for choice in (node.choice_id for node in decomposition.nodes)
    )
    message_root = _hash(
        "zenodex.choice-fiber.elimination-message-table.v1",
        [
            {
                "choice_id": message.choice_id,
                "entries": [
                    {
                        "interior_assignment": entry.interior_assignment,
                        "minimum": entry.minimum,
                        "separator_mask": entry.separator_mask,
                    }
                    for entry in message.entries
                ],
                "separator": message.separator,
            }
            for message in transcript
        ],
    )
    return ScopedMinimumV1(
        minimum,
        assignment,
        decomposition.root,
        projection.semantic_root,
        projection.lineage_root,
        message_root,
        decomposition.induced_width,
        preflight.work_units,
        preflight.message_cells,
        decomposition.fill_probes,
    )


def brute_force_scoped_minimum(
    polynomial: ChoiceFiberPolynomial,
    scope: Subcube,
) -> tuple[int, tuple[tuple[str, int], ...], int]:
    """Independent oracle that evaluates the original polynomial directly."""

    owned = _own_polynomial(polynomial)
    owned_scope = _own_scope(scope, len(owned.manifest.choice_ids))
    choices = owned.manifest.choice_ids
    fixed = _scope_fixed_assignment(choices, owned_scope)
    free = tuple(choice for choice in choices if choice not in fixed)
    if len(free) > MAX_BRUTE_FREE_CHOICES:
        raise TreewidthReject("BRUTE_FORCE_CHOICE_CAPACITY_EXCEEDED")
    assignments = 1 << len(free)
    term_work = max(1, sum(max(1, len(term.choices)) for term in owned.terms))
    if assignments * term_work > MAX_BRUTE_WORK:
        raise TreewidthReject("BRUTE_FORCE_WORK_CAPACITY_EXCEEDED")
    best: tuple[int, tuple[int, ...], tuple[tuple[str, int], ...]] | None = None
    for signs in product((-1, 1), repeat=len(free)):
        assignment_map = dict(fixed)
        assignment_map.update(zip(free, signs, strict=True))
        assignment = tuple((choice, assignment_map[choice]) for choice in choices)
        value = owned.evaluate(assignment_map)
        candidate = (value, tuple(sign for _, sign in assignment), assignment)
        if best is None or candidate[:2] < best[:2]:
            best = candidate
    if best is None:
        raise TreewidthReject("INTERNAL_EMPTY_BRUTE_DOMAIN")
    return best[0], best[2], assignments


@dataclass(frozen=True, slots=True)
class TreewidthCoverageResultV1:
    minimum: int
    assignment: tuple[tuple[str, int], ...]
    winning_scope: Subcube
    leaf_count: int

    def __post_init__(self) -> None:
        if type(self.minimum) is not int:
            raise TreewidthReject("INVALID_COVERAGE_RESULT")
        _require_assignment(self.assignment, "INVALID_COVERAGE_RESULT")
        if type(self.winning_scope) is not Subcube:
            raise TreewidthReject("INVALID_COVERAGE_RESULT")
        if type(self.leaf_count) is not int or not 1 <= self.leaf_count <= MAX_SCOPES:
            raise TreewidthReject("INVALID_COVERAGE_RESULT")

    def root(self, verification_subject_root: Digest) -> Digest:
        _require_digest(verification_subject_root, "INVALID_VERIFICATION_SUBJECT_ROOT")
        return _hash(
            "zenodex.choice-fiber.treewidth-result.v1",
            {
                "assignment": self.assignment,
                "leaf_count": self.leaf_count,
                "minimum": self.minimum,
                "verification_subject_root": verification_subject_root.hex(),
                "winning_scope": _scope_value(self.winning_scope),
            },
        )


@dataclass(frozen=True, slots=True)
class LeafEvidenceV1:
    leaf_ordinal: int
    scope: Subcube
    scoped_minimum: ScopedMinimumV1
    result_root: Digest
    root: Digest

    def __post_init__(self) -> None:
        if type(self.leaf_ordinal) is not int or not 0 <= self.leaf_ordinal < MAX_SCOPES:
            raise TreewidthReject("INVALID_LEAF_EVIDENCE")
        if type(self.scope) is not Subcube:
            raise TreewidthReject("INVALID_LEAF_EVIDENCE")
        if type(self.scoped_minimum) is not ScopedMinimumV1:
            raise TreewidthReject("INVALID_LEAF_EVIDENCE")
        _require_digest(self.result_root, "INVALID_LEAF_EVIDENCE")
        _require_digest(self.root, "INVALID_LEAF_EVIDENCE")


_MINT_TOKEN = object()
CHECKED_CLAIMS = (
    "exact_owned_polynomial_snapshot",
    "declared_source_pinned_verifier_profile",
    "derived_choice_ordinal_manifest",
    "exact_scope_projection",
    "derived_elimination_decomposition",
    "complete_separator_messages",
    "canonical_recursive_scope_coverage",
    "exact_global_minimum",
)


@dataclass(frozen=True, slots=True, init=False)
class VerifiedTreewidthCoverageV1:
    """Small structural receipt minted only by the reference verifier.

    Python constructor privacy is not a cryptographic boundary. Every process
    or durability crossing must replay verification from the exact sources.
    """

    verification_subject_root: Digest
    evidence_root: Digest
    result_root: Digest

    def __init__(
        self,
        verification_subject_root: Digest,
        evidence_root: Digest,
        result_root: Digest,
        _token: object | None = None,
    ) -> None:
        if _token is not _MINT_TOKEN:
            raise TreewidthReject("VERIFIER_OWNERSHIP_REQUIRED")
        object.__setattr__(
            self,
            "verification_subject_root",
            _require_digest(
                verification_subject_root,
                "INVALID_VERIFICATION_SUBJECT_ROOT",
            ),
        )
        object.__setattr__(
            self,
            "evidence_root",
            _require_digest(evidence_root, "INVALID_EVIDENCE_ROOT"),
        )
        object.__setattr__(
            self,
            "result_root",
            _require_digest(result_root, "INVALID_RESULT_ROOT"),
        )

    @property
    def schema(self) -> str:
        return "zenodex.verified-treewidth-coverage.v1"

    @property
    def authority(self) -> str:
        return "NONE"

    @property
    def claim_status(self) -> str:
        return "BOUNDED_RESEARCH_ONLY"

    @property
    def root(self) -> Digest:
        return _hash(
            "zenodex.verified-treewidth-coverage.v1",
            {
                "authority": self.authority,
                "claim_status": self.claim_status,
                "evidence_root": self.evidence_root.hex(),
                "result_root": self.result_root.hex(),
                "schema": self.schema,
                "verification_subject_root": self.verification_subject_root.hex(),
            },
        )


@dataclass(frozen=True, slots=True)
class TreewidthCoverageOutcomeV1:
    receipt: VerifiedTreewidthCoverageV1
    result: TreewidthCoverageResultV1
    leaf_evidence: tuple[LeafEvidenceV1, ...]
    coverage_certificate: CoverageCertificate
    aggregate_work_units: int
    aggregate_message_cells: int
    aggregate_fill_probes: int

    def __post_init__(self) -> None:
        if type(self.receipt) is not VerifiedTreewidthCoverageV1:
            raise TreewidthReject("INVALID_VERIFICATION_OUTCOME")
        if type(self.result) is not TreewidthCoverageResultV1:
            raise TreewidthReject("INVALID_VERIFICATION_OUTCOME")
        if type(self.leaf_evidence) is not tuple or any(
            type(item) is not LeafEvidenceV1 for item in self.leaf_evidence
        ):
            raise TreewidthReject("INVALID_VERIFICATION_OUTCOME")
        if type(self.coverage_certificate) is not CoverageCertificate:
            raise TreewidthReject("INVALID_VERIFICATION_OUTCOME")
        counters = (
            self.aggregate_work_units,
            self.aggregate_message_cells,
            self.aggregate_fill_probes,
        )
        if any(type(value) is not int or value < 0 for value in counters):
            raise TreewidthReject("INVALID_VERIFICATION_OUTCOME")


def _verification_subject_root(
    claim_context_root: Digest,
    polynomial: ChoiceFiberPolynomial,
    manifest: CoverageChoiceManifest,
    profile: VerifierProfileV1,
) -> Digest:
    problem_root = _hash(
        "zenodex.choice-fiber.treewidth-problem.v1",
        {
            "claim_context_root": claim_context_root.hex(),
            "correlation_semantics": "shared_named_symmetric_signs_v1",
            "objective": "exact_global_minimum",
            "polynomial_lineage_root": _lineage_root(polynomial).hex(),
            "polynomial_root": _polynomial_root(polynomial).hex(),
            "polynomial_semantic_root": _semantic_root(polynomial).hex(),
            "zrpf_ordinal_manifest_root": manifest.root.hex(),
        },
    )
    return _hash(
        "zenodex.choice-fiber.treewidth-verification-subject.v1",
        {
            "problem_root": problem_root.hex(),
            "verifier_profile_root": profile.root.hex(),
        },
    )


def _own_request(
    value: object,
) -> tuple[
    Digest,
    ChoiceFiberPolynomial,
    EliminationOrderV1,
    CoveragePlanV1,
    VerifierProfileV1,
    CoverageChoiceManifest,
]:
    if type(value) is not TreewidthCoverageRequestV1:
        raise TreewidthReject("INVALID_VERIFICATION_REQUEST")
    try:
        context = _require_digest(value.claim_context_root, "INVALID_CLAIM_CONTEXT_ROOT")
        polynomial = _own_polynomial(value.polynomial)
        order = _own_order(value.elimination_order, polynomial.manifest.choice_ids)
        profile = _own_profile(value.profile)
        manifest = _coverage_manifest(polynomial)
        plan = _own_plan(value.coverage_plan, len(manifest.names))
    except (AttributeError, TypeError, ValueError) as error:
        if isinstance(error, TreewidthReject):
            raise
        raise TreewidthReject("INVALID_VERIFICATION_REQUEST") from error
    return context, polynomial, order, plan, profile, manifest


def _own_coverage_tree(tree: object) -> Tree:
    """Bound and reconstruct an untrusted tree without recursive traversal."""

    if type(tree) not in (Leaf, Split):
        raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE")
    maximum_nodes = 2 * MAX_SCOPES - 1
    pending: list[tuple[object, int, bool]] = [(tree, 0, False)]
    seen: set[int] = set()
    owned: dict[int, Tree] = {}
    nodes = 0
    leaves = 0
    while pending:
        node, depth, expanded = pending.pop()
        node_id = id(node)
        if expanded:
            if type(node) is not Split:
                raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE")
            try:
                negative = owned[id(node.negative)]
                positive = owned[id(node.positive)]
                owned[node_id] = Split(node.choice_ordinal, negative, positive)
            except (CertificateReject, AttributeError, KeyError, TypeError, ValueError) as error:
                raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE") from error
            continue

        if node_id in seen:
            raise TreewidthReject("ALIASED_OR_CYCLIC_COVERAGE_TREE")
        seen.add(node_id)
        nodes += 1
        if nodes > maximum_nodes:
            raise TreewidthReject("COVERAGE_TREE_NODE_CAPACITY_EXCEEDED")
        if depth > MAX_ELIMINATION_CHOICES:
            raise TreewidthReject("COVERAGE_TREE_DEPTH_CAPACITY_EXCEEDED")
        if type(node) is Leaf:
            leaves += 1
            if leaves > MAX_SCOPES:
                raise TreewidthReject("COVERAGE_TREE_LEAF_CAPACITY_EXCEEDED")
            try:
                owned[node_id] = Leaf(
                    _require_digest(
                        node.receipt_root,
                        "INVALID_COVERAGE_CERTIFICATE",
                    )
                )
            except (CertificateReject, AttributeError, TypeError, ValueError) as error:
                raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE") from error
            continue
        if type(node) is not Split:
            raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE")
        try:
            negative = node.negative
            positive = node.positive
            choice_ordinal = node.choice_ordinal
        except AttributeError as error:
            raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE") from error
        if type(choice_ordinal) is not int or not 0 <= choice_ordinal < MAX_ELIMINATION_CHOICES:
            raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE")
        if type(negative) not in (Leaf, Split) or type(positive) not in (Leaf, Split):
            raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE")
        pending.append((node, depth, True))
        pending.append((positive, depth + 1, False))
        pending.append((negative, depth + 1, False))
    try:
        return owned[id(tree)]
    except KeyError as error:
        raise TreewidthReject("INVALID_COVERAGE_CERTIFICATE") from error


def _mint_receipt(
    subject_root: Digest,
    evidence_root: Digest,
    result_root: Digest,
) -> VerifiedTreewidthCoverageV1:
    return VerifiedTreewidthCoverageV1(subject_root, evidence_root, result_root, _MINT_TOKEN)


def verify_treewidth_coverage(
    request: TreewidthCoverageRequestV1,
) -> TreewidthCoverageOutcomeV1:
    """Replay every leaf and mint one research-only exact-coverage receipt."""

    context, polynomial, order, plan, profile, manifest = _own_request(request)
    projection_incidence = sum(max(1, len(term.choices)) for term in polynomial.terms)
    if len(plan.scopes) * projection_incidence > MAX_PROJECTION_INCIDENCE_VISITS:
        raise TreewidthReject("PROJECTION_WORK_CAPACITY_EXCEEDED")
    subject_root = _verification_subject_root(context, polynomial, manifest, profile)
    plan_root = plan.root(manifest)

    preflights: list[_PreflightV1] = []
    total_work = 0
    total_cells = 0
    total_fill = 0
    for scope in plan.scopes:
        preflight = _preflight_scope(
            polynomial,
            order,
            scope,
            profile,
            profile.max_aggregate_fill_probes - total_fill,
        )
        total_work += preflight.work_units
        total_cells += preflight.message_cells
        total_fill += preflight.decomposition.fill_probes
        if total_work > profile.max_aggregate_dp_work:
            raise TreewidthReject("AGGREGATE_DP_WORK_CAPACITY_EXCEEDED")
        if total_cells > profile.max_aggregate_message_cells:
            raise TreewidthReject("MESSAGE_CELL_CAPACITY_EXCEEDED")
        if total_fill > profile.max_aggregate_fill_probes:
            raise TreewidthReject("FILL_PROBE_CAPACITY_EXCEEDED")
        preflights.append(preflight)

    leaf_evidence: list[LeafEvidenceV1] = []
    shard_receipts: list[ShardReceipt] = []
    for leaf_ordinal, (scope, preflight) in enumerate(zip(plan.scopes, preflights, strict=True)):
        minimum = _solve_preflight(polynomial, scope, preflight)
        leaf_result_root = _hash(
            "zenodex.choice-fiber.treewidth-leaf-result.v1",
            {
                "assignment": minimum.assignment,
                "minimum": minimum.minimum,
                "scope": _scope_value(scope),
                "verification_subject_root": subject_root.hex(),
            },
        )
        leaf_root = _hash(
            "zenodex.choice-fiber.treewidth-leaf-evidence.v1",
            {
                "decomposition_root": minimum.decomposition_root.hex(),
                "induced_width": minimum.induced_width,
                "leaf_ordinal": leaf_ordinal,
                "message_root": minimum.message_root.hex(),
                "plan_root": plan_root.hex(),
                "projection_lineage_root": minimum.projection_lineage_root.hex(),
                "projection_semantic_root": minimum.projection_semantic_root.hex(),
                "result_root": leaf_result_root.hex(),
                "scope": _scope_value(scope),
                "verification_subject_root": subject_root.hex(),
            },
        )
        evidence = LeafEvidenceV1(
            leaf_ordinal,
            scope,
            minimum,
            leaf_result_root,
            leaf_root,
        )
        leaf_evidence.append(evidence)
        shard_receipts.append(ShardReceipt(subject_root, scope, leaf_root))

    try:
        coverage_certificate = build_canonical_certificate(
            manifest,
            subject_root,
            tuple(shard_receipts),
        )
        verify_certificate(
            manifest,
            subject_root,
            coverage_certificate,
            tuple(shard_receipts),
        )
    except (CertificateReject, AttributeError, TypeError, ValueError) as error:
        raise TreewidthReject("INVALID_EXACT_SCOPE_COVERAGE") from error

    winner = min(
        leaf_evidence,
        key=lambda item: (
            item.scoped_minimum.minimum,
            tuple(sign for _, sign in item.scoped_minimum.assignment),
            item.scope.fixed_mask,
            item.scope.positive_mask,
            item.root,
        ),
    )
    result = TreewidthCoverageResultV1(
        winner.scoped_minimum.minimum,
        winner.scoped_minimum.assignment,
        winner.scope,
        len(leaf_evidence),
    )
    result_root = result.root(subject_root)
    evidence_root = _hash(
        "zenodex.choice-fiber.treewidth-coverage-evidence.v1",
        {
            "checked_claims": CHECKED_CLAIMS,
            "coverage_certificate_root": coverage_certificate.root.hex(),
            "elimination_order_root": order.root.hex(),
            "leaf_roots": [item.root.hex() for item in leaf_evidence],
            "plan_root": plan_root.hex(),
            "verification_subject_root": subject_root.hex(),
        },
    )
    receipt = _mint_receipt(subject_root, evidence_root, result_root)
    return TreewidthCoverageOutcomeV1(
        receipt,
        result,
        tuple(leaf_evidence),
        coverage_certificate,
        total_work,
        total_cells,
        total_fill,
    )


def _own_scoped_minimum(
    value: object,
    expected_choices: tuple[str, ...],
) -> ScopedMinimumV1:
    if type(value) is not ScopedMinimumV1:
        raise TreewidthReject("INVALID_SCOPED_MINIMUM")
    return ScopedMinimumV1(
        value.minimum,
        _require_assignment(
            value.assignment,
            "INVALID_SCOPED_MINIMUM",
            expected_choices,
        ),
        _require_digest(value.decomposition_root, "INVALID_SCOPED_MINIMUM"),
        _require_digest(value.projection_semantic_root, "INVALID_SCOPED_MINIMUM"),
        _require_digest(value.projection_lineage_root, "INVALID_SCOPED_MINIMUM"),
        _require_digest(value.message_root, "INVALID_SCOPED_MINIMUM"),
        value.induced_width,
        value.work_units,
        value.message_cells,
        value.fill_probes,
    )


def _own_result(
    value: object,
    expected_choices: tuple[str, ...],
    nchoices: int,
) -> TreewidthCoverageResultV1:
    if type(value) is not TreewidthCoverageResultV1:
        raise TreewidthReject("INVALID_COVERAGE_RESULT")
    return TreewidthCoverageResultV1(
        value.minimum,
        _require_assignment(
            value.assignment,
            "INVALID_COVERAGE_RESULT",
            expected_choices,
        ),
        _own_scope(value.winning_scope, nchoices),
        value.leaf_count,
    )


def _own_leaf_evidence(
    value: object,
    expected_choices: tuple[str, ...],
    nchoices: int,
) -> LeafEvidenceV1:
    if type(value) is not LeafEvidenceV1:
        raise TreewidthReject("INVALID_LEAF_EVIDENCE")
    return LeafEvidenceV1(
        value.leaf_ordinal,
        _own_scope(value.scope, nchoices),
        _own_scoped_minimum(value.scoped_minimum, expected_choices),
        _require_digest(value.result_root, "INVALID_LEAF_EVIDENCE"),
        _require_digest(value.root, "INVALID_LEAF_EVIDENCE"),
    )


def reverify_treewidth_coverage(
    request: TreewidthCoverageRequestV1,
    outcome: TreewidthCoverageOutcomeV1,
) -> bool:
    """Complete point-of-use replay for every process or durability crossing."""

    if type(outcome) is not TreewidthCoverageOutcomeV1:
        return False
    try:
        _, polynomial, _, _, _, _ = _own_request(request)
        expected_choices = polynomial.manifest.choice_ids
        nchoices = len(expected_choices)
        expected = verify_treewidth_coverage(request)
        if type(outcome.receipt) is not VerifiedTreewidthCoverageV1:
            return False
        owned_receipt = _mint_receipt(
            _require_digest(
                outcome.receipt.verification_subject_root,
                "INVALID_VERIFICATION_SUBJECT_ROOT",
            ),
            _require_digest(outcome.receipt.evidence_root, "INVALID_EVIDENCE_ROOT"),
            _require_digest(outcome.receipt.result_root, "INVALID_RESULT_ROOT"),
        )
        owned_result = _own_result(outcome.result, expected_choices, nchoices)
        if type(outcome.leaf_evidence) is not tuple or len(outcome.leaf_evidence) > MAX_SCOPES:
            return False
        owned_leaf_evidence = tuple(
            _own_leaf_evidence(item, expected_choices, nchoices) for item in outcome.leaf_evidence
        )
        if type(outcome.coverage_certificate) is not CoverageCertificate:
            return False
        owned_tree = _own_coverage_tree(outcome.coverage_certificate.tree)
        owned_certificate = CoverageCertificate(
            _require_digest(
                outcome.coverage_certificate.manifest_root,
                "INVALID_COVERAGE_CERTIFICATE",
            ),
            _require_digest(
                outcome.coverage_certificate.subject_root,
                "INVALID_COVERAGE_CERTIFICATE",
            ),
            owned_tree,
        )
        metrics = (
            outcome.aggregate_work_units,
            outcome.aggregate_message_cells,
            outcome.aggregate_fill_probes,
        )
        if any(type(value) is not int or value < 0 for value in metrics):
            return False
    except (
        TreewidthReject,
        CertificateReject,
        AttributeError,
        RecursionError,
        TypeError,
        ValueError,
    ):
        return False
    return (
        owned_receipt == expected.receipt
        and owned_result == expected.result
        and owned_leaf_evidence == expected.leaf_evidence
        and owned_certificate == expected.coverage_certificate
        and outcome.aggregate_work_units == expected.aggregate_work_units
        and outcome.aggregate_message_cells == expected.aggregate_message_cells
        and outcome.aggregate_fill_probes == expected.aggregate_fill_probes
    )


def deterministic_context(label: str) -> Digest:
    return hashlib.sha256(("choice-fiber-treewidth-context:" + label).encode()).digest()
