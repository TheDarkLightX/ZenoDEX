#!/usr/bin/env python3
"""Closed registry model and parser (WholeEconomyDisasterCoverageV1).

The registry owns obligations, runners, oracles, predicates, bounds, mutants,
formal obligations, applicability decisions, and the denominator floor.
Runner argv is fixed here and hashed; packets never carry argv.  Every
cross-reference is checked before the registry is admitted.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Mapping, Sequence, cast

from tools.runtime_disaster_discovery_primitives_v1 import (
    MAX_BOUND_V1,
    MAX_PATH_CHARS_V1,
    RejectCodeV1,
    decode_strict_json,
    domain_hash_hex,
    domain_root,
    reject,
    require_bool,
    require_closed_object,
    require_enum,
    require_git_oid,
    require_int,
    require_list,
    require_sha256,
    require_string,
    require_token,
    require_token_list,
    require_unique_ids,
    sha256_hex,
    validate_repo_path,
)
from tools.runtime_disaster_discovery_sources_v1 import SourcePinV1, parse_source_pins
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    AGGREGATE_FAMILIES_V1,
    ALLOWED_RUNNER_FLAGS_V1,
    ATTACK_FAMILIES_V1,
    CLAIM_CEILING_V1,
    CLOSURE_MODES_V1,
    HISTORICAL_MINIMUM_RELEASE_EVIDENCE_CELLS_V1,
    HISTORICAL_STRICT_RELEASE_CLOSURE_V1,
    IMPLEMENTATION_BASE_COMMIT_V1,
    IMPLEMENTATION_BASE_TREE_V1,
    MAX_REGISTRY_BYTES_V1,
    MAX_RUNNER_ARGV_V1,
    MAX_RUNNER_TIMEOUT_S_V1,
    PLAN_PATH_V1,
    REGISTRY_PATH_V1,
    REGISTRY_SCHEMA_V1,
    REGISTRY_STATUS_V1,
    REQUIRED_SOURCE_PATHS_V1,
    RUNNER_PROGRAM_V1,
    UNSPECIFIED_V1,
    V1_FLOOR_APPLICABILITY_CELLS,
    V1_FLOOR_CAPABILITIES,
    V1_FLOOR_EXCLUSIONS,
    V1_FLOOR_ROUTES,
    VM_GATE_IDS_V1,
    ApplicabilityV1,
    CertificateKindV1,
    InvariantFamilyV1,
    LifecyclePhaseV1,
    OracleKindV1,
    RegistrySectionStateV1,
    SourceRoleV1,
    TargetKindV1,
)

_RUNNER_MODULE_RE = re.compile(r"^(tools/[a-z0-9_]+\.py|tests/[a-z0-9_/]+\.py)$")

CellKey = tuple[TargetKindV1, str, LifecyclePhaseV1, InvariantFamilyV1]


@dataclass(frozen=True, slots=True)
class BoundsProfileV1:
    bounds_profile_id: str
    max_depth: int
    max_frontier: int
    max_participants: int
    description: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "bounds_profile_id": self.bounds_profile_id,
            "max_depth": self.max_depth,
            "max_frontier": self.max_frontier,
            "max_participants": self.max_participants,
            "description": self.description,
        }


@dataclass(frozen=True, slots=True)
class MutantV1:
    mutant_id: str
    bad_predicate_id: str
    description: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "mutant_id": self.mutant_id,
            "bad_predicate_id": self.bad_predicate_id,
            "description": self.description,
        }


@dataclass(frozen=True, slots=True)
class FormalObligationV1:
    formal_obligation_id: str
    bad_predicate_id: str
    certificate_kind: CertificateKindV1
    theorem_id: str
    oracle_id: str
    certificate_artifact_path: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "formal_obligation_id": self.formal_obligation_id,
            "bad_predicate_id": self.bad_predicate_id,
            "certificate_kind": self.certificate_kind.value,
            "theorem_id": self.theorem_id,
            "oracle_id": self.oracle_id,
            "certificate_artifact_path": self.certificate_artifact_path,
        }


@dataclass(frozen=True, slots=True)
class BadPredicateV1:
    """One registered bad-state predicate refining exactly one REQUIRED cell."""

    bad_predicate_id: str
    target_kind: TargetKindV1
    target_id: str
    lifecycle_phase: LifecyclePhaseV1
    invariant_family: InvariantFamilyV1
    attack_family: str
    bounds_profile_id: str
    closure_mode: str
    ordered_participants: tuple[str, ...]
    statement: str
    required_mutant_ids: tuple[str, ...]

    @property
    def cell(self) -> CellKey:
        return (self.target_kind, self.target_id, self.lifecycle_phase, self.invariant_family)

    def to_canonical(self) -> dict[str, object]:
        return {
            "bad_predicate_id": self.bad_predicate_id,
            "target_kind": self.target_kind.value,
            "target_id": self.target_id,
            "lifecycle_phase": self.lifecycle_phase.value,
            "invariant_family": self.invariant_family.value,
            "attack_family": self.attack_family,
            "bounds_profile_id": self.bounds_profile_id,
            "closure_mode": self.closure_mode,
            "ordered_participants": list(self.ordered_participants),
            "statement": self.statement,
            "required_mutant_ids": list(self.required_mutant_ids),
        }


@dataclass(frozen=True, slots=True)
class RegisteredRunnerV1:
    """Fixed argv owned by the registry.  Packets never carry argv."""

    runner_id: str
    bad_predicate_id: str
    oracle_id: str
    argv: tuple[str, ...]
    argv_sha256: str
    timeout_s: int
    witness_artifact_path: str | None

    def to_canonical(self) -> dict[str, object]:
        return {
            "runner_id": self.runner_id,
            "bad_predicate_id": self.bad_predicate_id,
            "oracle_id": self.oracle_id,
            "argv": list(self.argv),
            "argv_sha256": self.argv_sha256,
            "timeout_s": self.timeout_s,
            "witness_artifact_path": self.witness_artifact_path,
        }


@dataclass(frozen=True, slots=True)
class OracleV1:
    oracle_id: str
    kind: OracleKindV1
    version: str
    verifier_identity: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "oracle_id": self.oracle_id,
            "kind": self.kind.value,
            "version": self.version,
            "verifier_identity": self.verifier_identity,
        }


@dataclass(frozen=True, slots=True)
class NotApplicableCertificateV1:
    formal_obligation_id: str
    theorem_id: str
    subject_commit: str
    subject_tree: str
    artifact_path: str
    artifact_sha256: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "formal_obligation_id": self.formal_obligation_id,
            "theorem_id": self.theorem_id,
            "subject_commit": self.subject_commit,
            "subject_tree": self.subject_tree,
            "artifact_path": self.artifact_path,
            "artifact_sha256": self.artifact_sha256,
        }


@dataclass(frozen=True, slots=True)
class ApplicabilityDecisionV1:
    target_kind: TargetKindV1
    target_id: str
    lifecycle_phase: LifecyclePhaseV1
    invariant_family: InvariantFamilyV1
    classification: ApplicabilityV1
    basis_source_path: str
    basis_citation: str
    certificate: NotApplicableCertificateV1 | None

    @property
    def cell(self) -> CellKey:
        return (self.target_kind, self.target_id, self.lifecycle_phase, self.invariant_family)

    def to_canonical(self) -> dict[str, object]:
        return {
            "target_kind": self.target_kind.value,
            "target_id": self.target_id,
            "lifecycle_phase": self.lifecycle_phase.value,
            "invariant_family": self.invariant_family.value,
            "classification": self.classification.value,
            "basis_source_path": self.basis_source_path,
            "basis_citation": self.basis_citation,
            "certificate": None if self.certificate is None else self.certificate.to_canonical(),
        }


@dataclass(frozen=True, slots=True)
class DenominatorFloorV1:
    capabilities: int
    routes: int
    exclusions: int
    applicability_cells: int

    def to_canonical(self) -> dict[str, object]:
        return {
            "capabilities": self.capabilities,
            "routes": self.routes,
            "exclusions": self.exclusions,
            "applicability_cells": self.applicability_cells,
        }


@dataclass(frozen=True, slots=True)
class RegistryV1:
    sha256: str
    byte_size: int
    source_pins: tuple[SourcePinV1, ...]
    bounds_profiles: tuple[BoundsProfileV1, ...]
    bad_predicates: tuple[BadPredicateV1, ...]
    mutants: tuple[MutantV1, ...]
    formal_obligations: tuple[FormalObligationV1, ...]
    applicability_state: RegistrySectionStateV1
    applicability_decisions: tuple[ApplicabilityDecisionV1, ...]
    composition_state: RegistrySectionStateV1
    runners: tuple[RegisteredRunnerV1, ...]
    oracles: tuple[OracleV1, ...]
    denominator_floor: DenominatorFloorV1
    nonclaims: tuple[str, ...]
    obligation_registry_root: str
    runner_registry_root: str
    oracle_registry_root: str

    def bounds_profile(self, bounds_profile_id: str) -> BoundsProfileV1 | None:
        return next(
            (row for row in self.bounds_profiles if row.bounds_profile_id == bounds_profile_id),
            None,
        )

    def predicate(self, bad_predicate_id: str) -> BadPredicateV1 | None:
        return next(
            (row for row in self.bad_predicates if row.bad_predicate_id == bad_predicate_id), None
        )

    def runner(self, runner_id: str) -> RegisteredRunnerV1 | None:
        return next((row for row in self.runners if row.runner_id == runner_id), None)

    def oracle(self, oracle_id: str) -> OracleV1 | None:
        return next((row for row in self.oracles if row.oracle_id == oracle_id), None)

    def runners_for(self, bad_predicate_id: str) -> tuple[RegisteredRunnerV1, ...]:
        return tuple(row for row in self.runners if row.bad_predicate_id == bad_predicate_id)

    def formal_obligations_for(self, bad_predicate_id: str) -> tuple[FormalObligationV1, ...]:
        return tuple(
            row for row in self.formal_obligations if row.bad_predicate_id == bad_predicate_id
        )

    def mutants_for(self, bad_predicate_id: str) -> tuple[str, ...]:
        return tuple(
            row.mutant_id for row in self.mutants if row.bad_predicate_id == bad_predicate_id
        )

    def predicates_for(self, cell: CellKey) -> tuple[BadPredicateV1, ...]:
        return tuple(
            sorted(
                (row for row in self.bad_predicates if row.cell == cell),
                key=lambda row: row.bad_predicate_id,
            )
        )

    def decision_for(self, cell: CellKey) -> ApplicabilityDecisionV1 | None:
        return next((row for row in self.applicability_decisions if row.cell == cell), None)


_REGISTRY_FIELDS = (
    "schema",
    "registry_version",
    "status",
    "claim_ceiling",
    "implementation_base",
    "source_pins",
    "universe",
    "applicability_registry",
    "composition_registry",
    "runner_registry",
    "oracle_registry",
    "denominator_floor",
    "historical_baseline",
    "nonclaims",
)
_UNIVERSE_FIELDS = (
    "lifecycle_phases",
    "invariant_families",
    "attack_families",
    "closure_modes",
    "bounds_profiles",
    "bad_predicates",
    "mutants",
    "formal_obligations",
)
_ENUM_ROW_FIELDS = {
    "lifecycle_phases": ("phase_id", "definition"),
    "invariant_families": ("family_id", "definition", "aggregate", "contributes_to_vm_gates"),
    "attack_families": ("attack_family_id", "definition"),
    "closure_modes": ("closure_mode_id", "definition"),
}
_BOUNDS_FIELDS = (
    "bounds_profile_id",
    "max_depth",
    "max_frontier",
    "max_participants",
    "description",
)
_MUTANT_FIELDS = ("mutant_id", "bad_predicate_id", "description")
_FORMAL_FIELDS = (
    "formal_obligation_id",
    "bad_predicate_id",
    "certificate_kind",
    "theorem_id",
    "oracle_id",
    "certificate_artifact_path",
)
_PREDICATE_FIELDS = (
    "bad_predicate_id",
    "target_kind",
    "target_id",
    "lifecycle_phase",
    "invariant_family",
    "attack_family",
    "bounds_profile_id",
    "closure_mode",
    "ordered_participants",
    "statement",
    "required_mutant_ids",
)
_RUNNER_FIELDS = (
    "runner_id",
    "bad_predicate_id",
    "oracle_id",
    "argv",
    "argv_sha256",
    "timeout_s",
    "witness_artifact_path",
)
_ORACLE_FIELDS = ("oracle_id", "kind", "version", "verifier_identity")
_DECISION_FIELDS = (
    "target_kind",
    "target_id",
    "lifecycle_phase",
    "invariant_family",
    "classification",
    "basis",
    "certificate",
)
_CERTIFICATE_FIELDS = (
    "formal_obligation_id",
    "theorem_id",
    "subject_commit",
    "subject_tree",
    "artifact_path",
    "artifact_sha256",
)
_FLOOR_FIELDS = ("capabilities", "routes", "exclusions", "applicability_cells")
_BASELINE_FIELDS = (
    "strict_release_closure",
    "minimum_release_evidence_cell_count",
    "source_path",
    "rule",
)


def _cell_fields(raw: Mapping[str, object], name: str) -> CellKey:
    return (
        cast(TargetKindV1, require_enum(raw["target_kind"], TargetKindV1, f"{name}.target_kind")),
        require_token(raw["target_id"], f"{name}.target_id"),
        cast(
            LifecyclePhaseV1,
            require_enum(raw["lifecycle_phase"], LifecyclePhaseV1, f"{name}.lifecycle_phase"),
        ),
        cast(
            InvariantFamilyV1,
            require_enum(raw["invariant_family"], InvariantFamilyV1, f"{name}.invariant_family"),
        ),
    )


def _enumeration_ids(universe: Mapping[str, object], key: str, expected: Sequence[str]) -> None:
    id_field = _ENUM_ROW_FIELDS[key][0]
    ids: list[str] = []
    for index, row in enumerate(require_list(universe[key], f"universe.{key}")):
        name = f"universe.{key}[{index}]"
        raw = require_closed_object(row, _ENUM_ROW_FIELDS[key], name)
        ids.append(require_token(raw[id_field], f"{name}.{id_field}"))
        require_string(raw["definition"], f"{name}.definition")
        if key == "invariant_families":
            _check_family_row(raw, ids[-1], name)
    if tuple(ids) != tuple(expected):
        raise reject(RejectCodeV1.ENUMERATION_DRIFT, f"universe.{key}")


def _check_family_row(raw: Mapping[str, object], family_id: str, name: str) -> None:
    aggregate = require_bool(raw["aggregate"], f"{name}.aggregate")
    gates = require_token_list(
        raw["contributes_to_vm_gates"], f"{name}.contributes_to_vm_gates", unique=True
    )
    if any(gate not in VM_GATE_IDS_V1 for gate in gates):
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}: unknown VM gate")
    expected_aggregate = family_id in {family.value for family in AGGREGATE_FAMILIES_V1}
    if aggregate != expected_aggregate:
        raise reject(RejectCodeV1.AGGREGATE_FAMILY_MISSING, f"{name}: {family_id}")


def argv_sha256(argv: Sequence[str]) -> str:
    return domain_hash_hex("wedc1-runner-argv", list(argv))


def parse_runner_argv(value: object, name: str) -> tuple[str, ...]:
    """Accept only ``python3 <repo module> [allowed flags]``; no shell, no -c/-m."""

    if type(value) is str:
        raise reject(RejectCodeV1.RUNNER_ARGV_FORBIDDEN, f"{name}: command string")
    items = require_list(value, name)
    if len(items) < 2 or len(items) > MAX_RUNNER_ARGV_V1:
        raise reject(RejectCodeV1.RUNNER_ARGV_FORBIDDEN, f"{name}: argv length")
    argv = tuple(
        require_string(item, f"{name}[{index}]", max_chars=MAX_PATH_CHARS_V1)
        for index, item in enumerate(items)
    )
    if argv[0] != RUNNER_PROGRAM_V1:
        raise reject(RejectCodeV1.RUNNER_ARGV_FORBIDDEN, f"{name}: program {argv[0]!r}")
    module = validate_repo_path(argv[1], f"{name}[1]")
    if _RUNNER_MODULE_RE.fullmatch(module) is None:
        raise reject(RejectCodeV1.RUNNER_ARGV_FORBIDDEN, f"{name}: module {module!r}")
    for flag in argv[2:]:
        if flag not in ALLOWED_RUNNER_FLAGS_V1:
            raise reject(RejectCodeV1.RUNNER_ARGV_FORBIDDEN, f"{name}: argument {flag!r}")
    return argv


def _parse_runner(value: object, name: str) -> RegisteredRunnerV1:
    raw = require_closed_object(value, _RUNNER_FIELDS, name)
    argv = parse_runner_argv(raw["argv"], f"{name}.argv")
    declared = require_sha256(raw["argv_sha256"], f"{name}.argv_sha256")
    if declared != argv_sha256(argv):
        raise reject(RejectCodeV1.RUNNER_ARGV_HASH_MISMATCH, name)
    witness_path = raw["witness_artifact_path"]
    return RegisteredRunnerV1(
        runner_id=require_token(raw["runner_id"], f"{name}.runner_id"),
        bad_predicate_id=require_token(raw["bad_predicate_id"], f"{name}.bad_predicate_id"),
        oracle_id=require_token(raw["oracle_id"], f"{name}.oracle_id"),
        argv=argv,
        argv_sha256=declared,
        timeout_s=require_int(
            raw["timeout_s"], f"{name}.timeout_s", low=1, high=MAX_RUNNER_TIMEOUT_S_V1
        ),
        witness_artifact_path=(
            None
            if witness_path is None
            else validate_repo_path(witness_path, f"{name}.witness_artifact_path")
        ),
    )


def _parse_oracle(value: object, name: str) -> OracleV1:
    item = require_closed_object(value, _ORACLE_FIELDS, name)
    return OracleV1(
        oracle_id=require_token(item["oracle_id"], f"{name}.oracle_id"),
        kind=cast(OracleKindV1, require_enum(item["kind"], OracleKindV1, f"{name}.kind")),
        version=require_token(item["version"], f"{name}.version"),
        verifier_identity=require_token(item["verifier_identity"], f"{name}.verifier_identity"),
    )


def _parse_predicate(value: object, name: str) -> BadPredicateV1:
    raw = require_closed_object(value, _PREDICATE_FIELDS, name)
    attack_family = require_token(raw["attack_family"], f"{name}.attack_family")
    closure_mode = require_token(raw["closure_mode"], f"{name}.closure_mode")
    if attack_family not in ATTACK_FAMILIES_V1 or attack_family == UNSPECIFIED_V1:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}.attack_family")
    if closure_mode not in CLOSURE_MODES_V1 or closure_mode == UNSPECIFIED_V1:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}.closure_mode")
    bounds_profile_id = require_token(raw["bounds_profile_id"], f"{name}.bounds_profile_id")
    if bounds_profile_id == UNSPECIFIED_V1:
        raise reject(RejectCodeV1.BOUNDS_PROFILE_UNREGISTERED, f"{name}: unspecified bounds")
    target_kind, target_id, phase, family = _cell_fields(raw, name)
    return BadPredicateV1(
        bad_predicate_id=require_token(raw["bad_predicate_id"], f"{name}.bad_predicate_id"),
        target_kind=target_kind,
        target_id=target_id,
        lifecycle_phase=phase,
        invariant_family=family,
        attack_family=attack_family,
        bounds_profile_id=bounds_profile_id,
        closure_mode=closure_mode,
        ordered_participants=require_token_list(
            raw["ordered_participants"], f"{name}.ordered_participants", unique=True
        ),
        statement=require_string(raw["statement"], f"{name}.statement"),
        required_mutant_ids=require_token_list(
            raw["required_mutant_ids"], f"{name}.required_mutant_ids", unique=True
        ),
    )


def _parse_bounds_profile(value: object, name: str) -> BoundsProfileV1:
    item = require_closed_object(value, _BOUNDS_FIELDS, name)
    return BoundsProfileV1(
        bounds_profile_id=require_token(item["bounds_profile_id"], f"{name}.bounds_profile_id"),
        max_depth=require_int(item["max_depth"], f"{name}.max_depth", low=1, high=MAX_BOUND_V1),
        max_frontier=require_int(
            item["max_frontier"], f"{name}.max_frontier", low=1, high=MAX_BOUND_V1
        ),
        max_participants=require_int(
            item["max_participants"], f"{name}.max_participants", low=1, high=MAX_BOUND_V1
        ),
        description=require_string(item["description"], f"{name}.description"),
    )


def _parse_mutant(value: object, name: str) -> MutantV1:
    item = require_closed_object(value, _MUTANT_FIELDS, name)
    return MutantV1(
        mutant_id=require_token(item["mutant_id"], f"{name}.mutant_id"),
        bad_predicate_id=require_token(item["bad_predicate_id"], f"{name}.bad_predicate_id"),
        description=require_string(item["description"], f"{name}.description"),
    )


def _parse_formal_obligation(value: object, name: str) -> FormalObligationV1:
    item = require_closed_object(value, _FORMAL_FIELDS, name)
    return FormalObligationV1(
        formal_obligation_id=require_token(
            item["formal_obligation_id"], f"{name}.formal_obligation_id"
        ),
        bad_predicate_id=require_token(item["bad_predicate_id"], f"{name}.bad_predicate_id"),
        certificate_kind=cast(
            CertificateKindV1,
            require_enum(item["certificate_kind"], CertificateKindV1, f"{name}.certificate_kind"),
        ),
        theorem_id=require_token(item["theorem_id"], f"{name}.theorem_id"),
        oracle_id=require_token(item["oracle_id"], f"{name}.oracle_id"),
        certificate_artifact_path=validate_repo_path(
            item["certificate_artifact_path"], f"{name}.certificate_artifact_path"
        ),
    )


def _parse_certificate(value: object, name: str) -> NotApplicableCertificateV1:
    cert = require_closed_object(value, _CERTIFICATE_FIELDS, name)
    return NotApplicableCertificateV1(
        formal_obligation_id=require_token(
            cert["formal_obligation_id"], f"{name}.formal_obligation_id"
        ),
        theorem_id=require_token(cert["theorem_id"], f"{name}.theorem_id"),
        subject_commit=require_git_oid(cert["subject_commit"], f"{name}.subject_commit"),
        subject_tree=require_git_oid(cert["subject_tree"], f"{name}.subject_tree"),
        artifact_path=validate_repo_path(cert["artifact_path"], f"{name}.artifact_path"),
        artifact_sha256=require_sha256(cert["artifact_sha256"], f"{name}.artifact_sha256"),
    )


def _parse_decision(value: object, name: str) -> ApplicabilityDecisionV1:
    raw = require_closed_object(value, _DECISION_FIELDS, name)
    basis = require_closed_object(raw["basis"], ("source_path", "citation"), f"{name}.basis")
    classification = cast(
        ApplicabilityV1,
        require_enum(raw["classification"], ApplicabilityV1, f"{name}.classification"),
    )
    certificate_raw = raw["certificate"]
    certificate: NotApplicableCertificateV1 | None = None
    if classification is ApplicabilityV1.NOT_APPLICABLE_PROVED:
        if certificate_raw is None:
            raise reject(
                RejectCodeV1.APPLICABILITY_DECISION_INVALID, f"{name}: certificate required"
            )
        certificate = _parse_certificate(certificate_raw, f"{name}.certificate")
    elif certificate_raw is not None:
        raise reject(RejectCodeV1.APPLICABILITY_DECISION_INVALID, f"{name}: unexpected certificate")
    if classification is ApplicabilityV1.APPLICABILITY_UNKNOWN:
        raise reject(
            RejectCodeV1.APPLICABILITY_DECISION_INVALID,
            f"{name}: unknown is the default, not a decision",
        )
    target_kind, target_id, phase, family = _cell_fields(raw, name)
    return ApplicabilityDecisionV1(
        target_kind=target_kind,
        target_id=target_id,
        lifecycle_phase=phase,
        invariant_family=family,
        classification=classification,
        basis_source_path=validate_repo_path(basis["source_path"], f"{name}.basis.source_path"),
        basis_citation=require_string(basis["citation"], f"{name}.basis.citation"),
        certificate=certificate,
    )


def _parse_floor(value: object) -> DenominatorFloorV1:
    raw = require_closed_object(value, _FLOOR_FIELDS, "registry.denominator_floor")
    floor = DenominatorFloorV1(
        capabilities=require_int(
            raw["capabilities"], "denominator_floor.capabilities", low=1, high=MAX_BOUND_V1
        ),
        routes=require_int(raw["routes"], "denominator_floor.routes", low=1, high=MAX_BOUND_V1),
        exclusions=require_int(
            raw["exclusions"], "denominator_floor.exclusions", low=1, high=MAX_BOUND_V1
        ),
        applicability_cells=require_int(
            raw["applicability_cells"],
            "denominator_floor.applicability_cells",
            low=1,
            high=MAX_BOUND_V1,
        ),
    )
    expected_cells = (
        (floor.capabilities + floor.routes + floor.exclusions)
        * len(LifecyclePhaseV1)
        * len(InvariantFamilyV1)
    )
    if floor.applicability_cells != expected_cells:
        raise reject(RejectCodeV1.DENOMINATOR_MISMATCH, "denominator_floor.applicability_cells")
    if (
        floor.capabilities < V1_FLOOR_CAPABILITIES
        or floor.routes < V1_FLOOR_ROUTES
        or floor.exclusions < V1_FLOOR_EXCLUSIONS
        or floor.applicability_cells < V1_FLOOR_APPLICABILITY_CELLS
    ):
        raise reject(
            RejectCodeV1.DENOMINATOR_BELOW_FLOOR, "registry floor below the hard V1 minimum"
        )
    return floor


def _check_header(raw: Mapping[str, object]) -> None:
    if raw["schema"] != REGISTRY_SCHEMA_V1:
        raise reject(RejectCodeV1.SCHEMA_MISMATCH, "registry")
    require_int(raw["registry_version"], "registry.registry_version", low=1, high=1)
    if require_token(raw["status"], "registry.status") != REGISTRY_STATUS_V1:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, "registry.status")
    if require_token(raw["claim_ceiling"], "registry.claim_ceiling") != CLAIM_CEILING_V1:
        raise reject(RejectCodeV1.CALLER_SUPPLIED_CEILING, "registry.claim_ceiling")
    base = require_closed_object(
        raw["implementation_base"], ("commit", "tree", "note"), "registry.implementation_base"
    )
    if (
        require_git_oid(base["commit"], "registry.implementation_base.commit")
        != IMPLEMENTATION_BASE_COMMIT_V1
        or require_git_oid(base["tree"], "registry.implementation_base.tree")
        != IMPLEMENTATION_BASE_TREE_V1
    ):
        raise reject(RejectCodeV1.SUBJECT_COMMIT_INVALID, "registry.implementation_base")
    require_string(base["note"], "registry.implementation_base.note")


def _check_baseline(value: object) -> None:
    baseline = require_closed_object(value, _BASELINE_FIELDS, "registry.historical_baseline")
    if (
        baseline["strict_release_closure"] != HISTORICAL_STRICT_RELEASE_CLOSURE_V1
        or type(baseline["minimum_release_evidence_cell_count"]) is not int
        or baseline["minimum_release_evidence_cell_count"]
        != HISTORICAL_MINIMUM_RELEASE_EVIDENCE_CELLS_V1
        or baseline["source_path"] != PLAN_PATH_V1
    ):
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, "historical baseline must not be rewritten")
    require_string(baseline["rule"], "registry.historical_baseline.rule")


def _parse_universe(
    value: object,
) -> tuple[
    tuple[BoundsProfileV1, ...],
    tuple[BadPredicateV1, ...],
    tuple[MutantV1, ...],
    tuple[FormalObligationV1, ...],
]:
    universe = require_closed_object(value, _UNIVERSE_FIELDS, "registry.universe")
    _enumeration_ids(universe, "lifecycle_phases", [phase.value for phase in LifecyclePhaseV1])
    _enumeration_ids(universe, "invariant_families", [family.value for family in InvariantFamilyV1])
    _enumeration_ids(universe, "attack_families", ATTACK_FAMILIES_V1)
    _enumeration_ids(universe, "closure_modes", CLOSURE_MODES_V1)
    bounds = tuple(
        _parse_bounds_profile(row, f"universe.bounds_profiles[{index}]")
        for index, row in enumerate(
            require_list(universe["bounds_profiles"], "universe.bounds_profiles")
        )
    )
    require_unique_ids([row.bounds_profile_id for row in bounds], "universe.bounds_profiles")
    if any(row.bounds_profile_id == UNSPECIFIED_V1 for row in bounds):
        raise reject(RejectCodeV1.TOKEN_INVALID, "universe.bounds_profiles: reserved id")
    predicates = tuple(
        _parse_predicate(row, f"universe.bad_predicates[{index}]")
        for index, row in enumerate(
            require_list(universe["bad_predicates"], "universe.bad_predicates")
        )
    )
    require_unique_ids([row.bad_predicate_id for row in predicates], "universe.bad_predicates")
    if any(row.bad_predicate_id == UNSPECIFIED_V1 for row in predicates):
        raise reject(RejectCodeV1.TOKEN_INVALID, "universe.bad_predicates: reserved id")
    mutants = tuple(
        _parse_mutant(row, f"universe.mutants[{index}]")
        for index, row in enumerate(require_list(universe["mutants"], "universe.mutants"))
    )
    require_unique_ids([row.mutant_id for row in mutants], "universe.mutants")
    formal = tuple(
        _parse_formal_obligation(row, f"universe.formal_obligations[{index}]")
        for index, row in enumerate(
            require_list(universe["formal_obligations"], "universe.formal_obligations")
        )
    )
    require_unique_ids([row.formal_obligation_id for row in formal], "universe.formal_obligations")
    return bounds, predicates, mutants, formal


def _parse_applicability(
    value: object,
) -> tuple[RegistrySectionStateV1, tuple[ApplicabilityDecisionV1, ...]]:
    section = require_closed_object(
        value, ("state", "decisions"), "registry.applicability_registry"
    )
    state = cast(
        RegistrySectionStateV1,
        require_enum(
            section["state"], RegistrySectionStateV1, "registry.applicability_registry.state"
        ),
    )
    decisions = tuple(
        _parse_decision(row, f"registry.applicability_registry.decisions[{index}]")
        for index, row in enumerate(
            require_list(section["decisions"], "registry.applicability_registry.decisions")
        )
    )
    cells = [row.cell for row in decisions]
    if len(set(cells)) != len(cells):
        raise reject(
            RejectCodeV1.APPLICABILITY_DECISION_DUPLICATE,
            "registry.applicability_registry.decisions",
        )
    return state, decisions


def _parse_composition(value: object) -> RegistrySectionStateV1:
    section = require_closed_object(value, ("state", "cells"), "registry.composition_registry")
    state = cast(
        RegistrySectionStateV1,
        require_enum(
            section["state"], RegistrySectionStateV1, "registry.composition_registry.state"
        ),
    )
    if require_list(section["cells"], "registry.composition_registry.cells"):
        raise reject(
            RejectCodeV1.VALUE_OUT_OF_RANGE, "composition cells are not materialized in V1"
        )
    if state is not RegistrySectionStateV1.INCOMPLETE:
        raise reject(
            RejectCodeV1.VALUE_OUT_OF_RANGE, "composition registry cannot be complete in V1"
        )
    return state


def parse_registry(data: bytes) -> RegistryV1:
    """Parse the closed registry from owned bytes and cross-check every reference."""

    raw = require_closed_object(
        decode_strict_json(data, name="registry", max_bytes=MAX_REGISTRY_BYTES_V1),
        _REGISTRY_FIELDS,
        "registry",
    )
    _check_header(raw)
    pins = parse_source_pins(raw["source_pins"], "registry.source_pins")
    bounds, predicates, mutants, formal = _parse_universe(raw["universe"])
    applicability_state, decisions = _parse_applicability(raw["applicability_registry"])
    composition_state = _parse_composition(raw["composition_registry"])
    runner_section = require_closed_object(
        raw["runner_registry"], ("runners",), "registry.runner_registry"
    )
    runners = tuple(
        _parse_runner(row, f"registry.runner_registry.runners[{index}]")
        for index, row in enumerate(
            require_list(runner_section["runners"], "registry.runner_registry.runners")
        )
    )
    require_unique_ids([row.runner_id for row in runners], "registry.runner_registry.runners")
    oracle_section = require_closed_object(
        raw["oracle_registry"], ("oracles",), "registry.oracle_registry"
    )
    oracles = tuple(
        _parse_oracle(row, f"registry.oracle_registry.oracles[{index}]")
        for index, row in enumerate(
            require_list(oracle_section["oracles"], "registry.oracle_registry.oracles")
        )
    )
    require_unique_ids([row.oracle_id for row in oracles], "registry.oracle_registry.oracles")
    floor = _parse_floor(raw["denominator_floor"])
    _check_baseline(raw["historical_baseline"])
    nonclaims = tuple(
        require_string(item, f"registry.nonclaims[{index}]")
        for index, item in enumerate(require_list(raw["nonclaims"], "registry.nonclaims"))
    )
    if not nonclaims:
        raise reject(RejectCodeV1.MISSING_FIELD, "registry.nonclaims")
    registry = RegistryV1(
        sha256=sha256_hex(data),
        byte_size=len(data),
        source_pins=pins,
        bounds_profiles=bounds,
        bad_predicates=predicates,
        mutants=mutants,
        formal_obligations=formal,
        applicability_state=applicability_state,
        applicability_decisions=decisions,
        composition_state=composition_state,
        runners=runners,
        oracles=oracles,
        denominator_floor=floor,
        nonclaims=nonclaims,
        obligation_registry_root=domain_root(
            "wedc1-obligation-registry",
            {
                "universe": raw["universe"],
                "applicability_registry": raw["applicability_registry"],
                "composition_registry": raw["composition_registry"],
                "denominator_floor": raw["denominator_floor"],
            },
        ),
        runner_registry_root=domain_root("wedc1-runner-registry", raw["runner_registry"]),
        oracle_registry_root=domain_root("wedc1-oracle-registry", raw["oracle_registry"]),
    )
    _cross_check_registry(registry)
    return registry


def _cross_check_registry(registry: RegistryV1) -> None:
    """Reference checks in a fixed order: dangling references first, then per-predicate closure."""

    for mutant in registry.mutants:
        if registry.predicate(mutant.bad_predicate_id) is None:
            raise reject(RejectCodeV1.PREDICATE_UNREGISTERED, f"mutant {mutant.mutant_id}")
    for obligation in registry.formal_obligations:
        if registry.predicate(obligation.bad_predicate_id) is None:
            raise reject(
                RejectCodeV1.PREDICATE_UNREGISTERED, f"formal {obligation.formal_obligation_id}"
            )
        oracle = registry.oracle(obligation.oracle_id)
        if oracle is None:
            raise reject(
                RejectCodeV1.ORACLE_UNREGISTERED, f"formal {obligation.formal_obligation_id}"
            )
        if oracle.kind is not OracleKindV1.FORMAL_PROVER:
            raise reject(
                RejectCodeV1.VALUE_OUT_OF_RANGE,
                f"formal {obligation.formal_obligation_id}: oracle kind",
            )
    for runner in registry.runners:
        if registry.predicate(runner.bad_predicate_id) is None:
            raise reject(RejectCodeV1.PREDICATE_UNREGISTERED, f"runner {runner.runner_id}")
        if registry.oracle(runner.oracle_id) is None:
            raise reject(RejectCodeV1.ORACLE_UNREGISTERED, f"runner {runner.runner_id}")
        source_pin = next((pin for pin in registry.source_pins if pin.path == runner.argv[1]), None)
        if source_pin is None or source_pin.role is not SourceRoleV1.CHECKER_SOURCE:
            raise reject(
                RejectCodeV1.RUNNER_SOURCE_UNBOUND, f"runner {runner.runner_id}: {runner.argv[1]}"
            )
    for predicate in registry.bad_predicates:
        name = f"bad_predicate {predicate.bad_predicate_id}"
        if registry.bounds_profile(predicate.bounds_profile_id) is None:
            raise reject(RejectCodeV1.BOUNDS_PROFILE_UNREGISTERED, name)
        decision = registry.decision_for(predicate.cell)
        if decision is None or decision.classification is not ApplicabilityV1.REQUIRED:
            raise reject(RejectCodeV1.PREDICATE_CELL_NOT_REQUIRED, name)
        registered_mutants = registry.mutants_for(predicate.bad_predicate_id)
        if tuple(sorted(registered_mutants)) != tuple(sorted(predicate.required_mutant_ids)):
            raise reject(RejectCodeV1.MUTANT_SET_MISMATCH, name)
    for decision in registry.applicability_decisions:
        if (
            decision.basis_source_path not in REQUIRED_SOURCE_PATHS_V1
            and decision.basis_source_path != REGISTRY_PATH_V1
        ):
            raise reject(
                RejectCodeV1.APPLICABILITY_DECISION_INVALID, f"basis {decision.basis_source_path}"
            )
