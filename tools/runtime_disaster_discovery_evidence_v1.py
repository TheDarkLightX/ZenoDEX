#!/usr/bin/env python3
"""Observations, witnesses, certificates, results, and the evidence lattice (WholeEconomyDisasterCoverageV1).

Exit zero or passing output yields at most ``NOT_WITNESSED_IN_TESTS``.  Stdout
is hashed, never read.  A status is computed from bound evidence and
recomputed by the verifier; a caller-supplied status never survives.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final, Mapping, Sequence, cast

from tools.runtime_disaster_discovery_inventory_v1 import (
    ObligationInventoryV1,
    ObligationKeyV1,
    ObligationRowV1,
    parse_obligation_key,
)
from tools.runtime_disaster_discovery_primitives_v1 import (
    RejectCodeV1,
    domain_hash_hex,
    domain_root,
    reject,
    require_bool,
    require_closed_object,
    require_enum,
    require_int,
    require_list,
    require_root,
    require_sha256,
    require_string,
    require_token,
    require_token_list,
    validate_repo_path,
)
from tools.runtime_disaster_discovery_registry_v1 import (
    BadPredicateV1,
    BoundsProfileV1,
    RegisteredRunnerV1,
    RegistryV1,
)
from tools.runtime_disaster_discovery_sources_v1 import OwnedSourceV1, bind_artifact
from tools.runtime_disaster_discovery_subject_v1 import ExactSubjectV1
from tools.runtime_disaster_discovery_vocabulary_v1 import (
    CLAIM_CEILING_V1,
    STATUS_RANK_V1,
    CertificateKindV1,
    EvidenceStatusV1,
    ExecutionPremiseV1,
    InvariantFamilyV1,
    LifecyclePhaseV1,
    NoEffectOutcomeV1,
    NoEffectSurfaceV1,
    OracleKindV1,
    OracleVerdictV1,
    TargetKindV1,
    WitnessKindV1,
)

VM_GATE_EFFECT_V1: Final = "CONTRIBUTES_TO"


@dataclass(frozen=True, slots=True)
class ExecutionObservationV1:
    """What a fixed-registry execution observed.  Output text is hashed, never read."""

    runner_id: str
    argv_sha256: str
    returncode: int | None
    stdout_sha256: str
    stderr_sha256: str
    timed_out: bool
    output_limit_exceeded: bool

    def to_canonical(self) -> dict[str, object]:
        return {
            "runner_id": self.runner_id,
            "argv_sha256": self.argv_sha256,
            "returncode": self.returncode,
            "stdout_sha256": self.stdout_sha256,
            "stderr_sha256": self.stderr_sha256,
            "timed_out": self.timed_out,
            "output_limit_exceeded": self.output_limit_exceeded,
        }

    @property
    def replay_sha256(self) -> str:
        return domain_hash_hex("wedc1-replay-transcript", self.to_canonical())


@dataclass(frozen=True, slots=True)
class ArtifactRefV1:
    path: str
    sha256: str

    def to_canonical(self) -> dict[str, object]:
        return {"path": self.path, "sha256": self.sha256}


@dataclass(frozen=True, slots=True)
class WitnessV1:
    kind: WitnessKindV1
    artifact: ArtifactRefV1 | None
    replay_sha256: str | None

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind.value,
            "artifact": None if self.artifact is None else self.artifact.to_canonical(),
            "replay_sha256": self.replay_sha256,
        }


@dataclass(frozen=True, slots=True)
class FormalCertificateV1:
    kind: CertificateKindV1
    formal_obligation_id: str
    theorem_id: str
    toolchain_manifest_root: str
    artifact: ArtifactRefV1

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind.value,
            "formal_obligation_id": self.formal_obligation_id,
            "theorem_id": self.theorem_id,
            "toolchain_manifest_root": self.toolchain_manifest_root,
            "artifact": self.artifact.to_canonical(),
        }


@dataclass(frozen=True, slots=True)
class NoEffectObservationV1:
    """Reject-is-no-op observation for one authoritative surface; never assumed."""

    surface: NoEffectSurfaceV1
    outcome: NoEffectOutcomeV1

    def to_canonical(self) -> dict[str, object]:
        return {"surface": self.surface.value, "outcome": self.outcome.value}


UNOBSERVED_NO_EFFECT_V1: Final = tuple(
    NoEffectObservationV1(surface, NoEffectOutcomeV1.UNOBSERVED) for surface in NoEffectSurfaceV1
)
# Canonical order of the four authoritative surfaces is the enum declaration order.
NO_EFFECT_ORDER_V1: Final = {surface: index for index, surface in enumerate(NoEffectSurfaceV1)}

RESULT_FIELDS_V1: Final = (
    "obligation_id",
    "key",
    "predicate_root",
    "schema_root",
    "bounds_profile_id",
    "bounds_root",
    "cells",
    "runner_id",
    "oracle_id",
    "argv_sha256",
    "source_pins_root",
    "subject_root",
    "execution_premise",
    "observation",
    "oracle_verdict",
    "oracle_report_sha256",
    "witness",
    "no_effect_observations",
    "required_mutant_ids",
    "killed_mutant_ids",
    "formal_certificates",
    "vm_gate_effect",
    "contributes_to_vm_gates",
    "computed_status",
    "claim_ceiling",
)
RESULT_SCHEMA_ROOT_V1: Final = domain_root("wedc1-result-schema", list(RESULT_FIELDS_V1))


@dataclass(frozen=True, slots=True)
class ObligationResultV1:
    obligation_id: str
    key: ObligationKeyV1
    predicate_root: str
    schema_root: str
    bounds_profile_id: str
    bounds_root: str
    cells: tuple[tuple[LifecyclePhaseV1, InvariantFamilyV1], ...]
    runner_id: str
    oracle_id: str
    argv_sha256: str
    source_pins_root: str
    subject_root: str
    execution_premise: ExecutionPremiseV1
    observation: ExecutionObservationV1
    oracle_verdict: OracleVerdictV1
    oracle_report_sha256: str
    witness: WitnessV1
    no_effect_observations: tuple[NoEffectObservationV1, ...]
    required_mutant_ids: tuple[str, ...]
    killed_mutant_ids: tuple[str, ...]
    formal_certificates: tuple[FormalCertificateV1, ...]
    vm_gate_effect: str
    contributes_to_vm_gates: tuple[str, ...]
    computed_status: EvidenceStatusV1
    claim_ceiling: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "key": self.key.to_canonical(),
            "predicate_root": self.predicate_root,
            "schema_root": self.schema_root,
            "bounds_profile_id": self.bounds_profile_id,
            "bounds_root": self.bounds_root,
            "cells": [
                {"lifecycle_phase": phase.value, "invariant_family": family.value}
                for phase, family in self.cells
            ],
            "runner_id": self.runner_id,
            "oracle_id": self.oracle_id,
            "argv_sha256": self.argv_sha256,
            "source_pins_root": self.source_pins_root,
            "subject_root": self.subject_root,
            "execution_premise": self.execution_premise.value,
            "observation": self.observation.to_canonical(),
            "oracle_verdict": self.oracle_verdict.value,
            "oracle_report_sha256": self.oracle_report_sha256,
            "witness": self.witness.to_canonical(),
            "no_effect_observations": [item.to_canonical() for item in self.no_effect_observations],
            "required_mutant_ids": list(self.required_mutant_ids),
            "killed_mutant_ids": list(self.killed_mutant_ids),
            "formal_certificates": [item.to_canonical() for item in self.formal_certificates],
            "vm_gate_effect": self.vm_gate_effect,
            "contributes_to_vm_gates": list(self.contributes_to_vm_gates),
            "computed_status": self.computed_status.value,
            "claim_ceiling": self.claim_ceiling,
        }


def predicate_root(predicate: BadPredicateV1) -> str:
    return domain_root("wedc1-bad-predicate", predicate.to_canonical())


def bounds_root(profile: BoundsProfileV1) -> str:
    return domain_root("wedc1-bounds-profile", profile.to_canonical())


def oracle_report_sha256(
    oracle_id: str, verdict: OracleVerdictV1, observation: ExecutionObservationV1
) -> str:
    return domain_hash_hex(
        "wedc1-oracle-report",
        {
            "oracle_id": oracle_id,
            "verdict": verdict.value,
            "observation": observation.to_canonical(),
        },
    )


def derive_oracle_verdict(
    oracle_kind: OracleKindV1,
    observation: ExecutionObservationV1,
    *,
    witness_present: bool,
    certificates_present: bool,
) -> OracleVerdictV1:
    """Verdict from exit status and bound artifacts only; stdout text never participates."""

    if observation.timed_out or observation.output_limit_exceeded or observation.returncode is None:
        return OracleVerdictV1.INCONCLUSIVE
    if observation.returncode == 0:
        if oracle_kind is OracleKindV1.FORMAL_PROVER and not certificates_present:
            return OracleVerdictV1.INCONCLUSIVE
        return OracleVerdictV1.PASS
    return OracleVerdictV1.FAIL if witness_present else OracleVerdictV1.INCONCLUSIVE


def _formal_status(row: ObligationRowV1, kinds: frozenset[CertificateKindV1]) -> EvidenceStatusV1:
    if CertificateKindV1.MODEL_PROOF in kinds and CertificateKindV1.REFINEMENT_PROOF in kinds:
        return EvidenceStatusV1.RUNTIME_REFINEMENT_CLOSED
    if CertificateKindV1.MODEL_PROOF in kinds:
        return EvidenceStatusV1.MODEL_PROVED_UNREACHABLE
    if CertificateKindV1.CONSTRUCTION_PROOF in kinds:
        return EvidenceStatusV1.UNREACHABLE_BY_CONSTRUCTION
    if (
        CertificateKindV1.NO_WRITER_PROOF in kinds
        and row.key.target_kind is TargetKindV1.EXPLICIT_EXCLUSION
    ):
        return EvidenceStatusV1.DISABLED_PROVED_NO_WRITER
    return EvidenceStatusV1.INCONCLUSIVE


def compute_result_status(
    row: ObligationRowV1,
    result: ObligationResultV1,
    registry: RegistryV1,
    subject: ExactSubjectV1,
) -> EvidenceStatusV1:
    """Evidence lattice rules in precedence order."""

    if row.predicate is None:
        return EvidenceStatusV1.UNSPECIFIED_SEMANTICS
    if (
        result.source_pins_root != subject.source_pins_root
        or result.subject_root != subject.subject_root
    ):
        return EvidenceStatusV1.STALE_EVIDENCE
    if any(
        cert.toolchain_manifest_root != subject.toolchain_manifest_root
        for cert in result.formal_certificates
    ):
        return EvidenceStatusV1.STALE_EVIDENCE
    if result.execution_premise is not ExecutionPremiseV1.CLEAN_WORKTREE_HEAD_BOUND:
        return EvidenceStatusV1.EXTERNAL_PREMISE
    if result.oracle_verdict is OracleVerdictV1.INCONCLUSIVE:
        return EvidenceStatusV1.INCONCLUSIVE
    if result.oracle_verdict is OracleVerdictV1.FAIL:
        if result.witness.kind is WitnessKindV1.BAD_TRACE_WITNESS:
            return EvidenceStatusV1.WITNESSED_REACHABLE
        return EvidenceStatusV1.INCONCLUSIVE
    if any(item.outcome is NoEffectOutcomeV1.CHANGED for item in result.no_effect_observations):
        return EvidenceStatusV1.INCONCLUSIVE
    oracle = registry.oracle(result.oracle_id)
    if oracle is None or oracle.kind is not OracleKindV1.FORMAL_PROVER:
        return EvidenceStatusV1.NOT_WITNESSED_IN_TESTS
    return _formal_status(
        row, frozenset(certificate.kind for certificate in result.formal_certificates)
    )


def _witness_for(
    verdict: OracleVerdictV1, artifact: ArtifactRefV1 | None, observation: ExecutionObservationV1
) -> WitnessV1:
    if verdict is OracleVerdictV1.FAIL and artifact is not None:
        return WitnessV1(WitnessKindV1.BAD_TRACE_WITNESS, artifact, None)
    if verdict is OracleVerdictV1.PASS:
        return WitnessV1(WitnessKindV1.REPLAY_TRANSCRIPT, None, observation.replay_sha256)
    return WitnessV1(WitnessKindV1.NONE, None, None)


def build_result(
    *,
    row: ObligationRowV1,
    runner: RegisteredRunnerV1,
    registry: RegistryV1,
    subject: ExactSubjectV1,
    premise: ExecutionPremiseV1,
    observation: ExecutionObservationV1,
    witness_artifact: ArtifactRefV1 | None,
    certificates: Sequence[FormalCertificateV1],
    no_effect_observations: Sequence[NoEffectObservationV1],
    killed_mutant_ids: Sequence[str],
) -> ObligationResultV1:
    """Assemble one result row; the status is computed, never supplied."""

    predicate = row.predicate
    if predicate is None:
        raise reject(RejectCodeV1.PREDICATE_UNSPECIFIED, row.obligation_id)
    profile = registry.bounds_profile(predicate.bounds_profile_id)
    oracle = registry.oracle(runner.oracle_id)
    if profile is None:
        raise reject(RejectCodeV1.BOUNDS_PROFILE_UNREGISTERED, predicate.bounds_profile_id)
    if oracle is None:
        raise reject(RejectCodeV1.ORACLE_UNREGISTERED, runner.oracle_id)
    if observation.runner_id != runner.runner_id or observation.argv_sha256 != runner.argv_sha256:
        raise reject(RejectCodeV1.RUNNER_ARGV_HASH_MISMATCH, runner.runner_id)
    verdict = derive_oracle_verdict(
        oracle.kind,
        observation,
        witness_present=witness_artifact is not None,
        certificates_present=bool(certificates),
    )
    partial = ObligationResultV1(
        obligation_id=row.obligation_id,
        key=row.key,
        predicate_root=predicate_root(predicate),
        schema_root=RESULT_SCHEMA_ROOT_V1,
        bounds_profile_id=profile.bounds_profile_id,
        bounds_root=bounds_root(profile),
        cells=((row.key.lifecycle_phase, row.key.invariant_family),),
        runner_id=runner.runner_id,
        oracle_id=oracle.oracle_id,
        argv_sha256=runner.argv_sha256,
        source_pins_root=subject.source_pins_root,
        subject_root=subject.subject_root,
        execution_premise=premise,
        observation=observation,
        oracle_verdict=verdict,
        oracle_report_sha256=oracle_report_sha256(oracle.oracle_id, verdict, observation),
        witness=_witness_for(verdict, witness_artifact, observation),
        no_effect_observations=tuple(
            sorted(no_effect_observations, key=lambda item: NO_EFFECT_ORDER_V1[item.surface])
        ),
        required_mutant_ids=tuple(sorted(registry.mutants_for(predicate.bad_predicate_id))),
        killed_mutant_ids=tuple(sorted(killed_mutant_ids)),
        formal_certificates=tuple(sorted(certificates, key=lambda item: item.formal_obligation_id)),
        vm_gate_effect=VM_GATE_EFFECT_V1,
        contributes_to_vm_gates=(),
        computed_status=EvidenceStatusV1.UNSPECIFIED_SEMANTICS,
        claim_ceiling=CLAIM_CEILING_V1,
    )
    return replace(partial, computed_status=compute_result_status(row, partial, registry, subject))


# --------------------------------------------------------------------------
# Independent verification of result rows
# --------------------------------------------------------------------------


def _verify_identity(
    result: ObligationResultV1, inventory: ObligationInventoryV1, name: str
) -> tuple[ObligationRowV1, BadPredicateV1]:
    if result.key.obligation_id != result.obligation_id:
        raise reject(RejectCodeV1.OBLIGATION_ID_MISMATCH, name)
    row = inventory.row(result.obligation_id)
    if row is None:
        raise reject(RejectCodeV1.OBLIGATION_UNREGISTERED, name)
    if row.key != result.key:
        raise reject(RejectCodeV1.OBLIGATION_KEY_ALIAS, name)
    if row.predicate is None:
        raise reject(RejectCodeV1.PREDICATE_UNSPECIFIED, name)
    if result.predicate_root != predicate_root(row.predicate):
        raise reject(RejectCodeV1.PREDICATE_ROOT_MISMATCH, name)
    if result.schema_root != RESULT_SCHEMA_ROOT_V1:
        raise reject(RejectCodeV1.SCHEMA_ROOT_MISMATCH, name)
    if result.cells != ((row.key.lifecycle_phase, row.key.invariant_family),):
        raise reject(RejectCodeV1.RESULT_CELL_MISMATCH, name)
    return row, row.predicate


def _verify_registrations(
    result: ObligationResultV1,
    predicate: BadPredicateV1,
    registry: RegistryV1,
    subject: ExactSubjectV1,
    name: str,
) -> tuple[RegisteredRunnerV1, OracleKindV1]:
    profile = registry.bounds_profile(result.bounds_profile_id)
    if profile is None or result.bounds_profile_id != predicate.bounds_profile_id:
        raise reject(RejectCodeV1.BOUNDS_PROFILE_UNREGISTERED, name)
    if result.bounds_root != bounds_root(profile):
        raise reject(RejectCodeV1.BOUNDS_ROOT_MISMATCH, name)
    runner = registry.runner(result.runner_id)
    if runner is None or runner.bad_predicate_id != predicate.bad_predicate_id:
        raise reject(RejectCodeV1.RUNNER_UNREGISTERED, name)
    if (
        result.argv_sha256 != runner.argv_sha256
        or result.observation.argv_sha256 != runner.argv_sha256
    ):
        raise reject(RejectCodeV1.RUNNER_ARGV_HASH_MISMATCH, name)
    if result.observation.runner_id != runner.runner_id:
        raise reject(RejectCodeV1.RUNNER_UNREGISTERED, f"{name}: observation runner")
    oracle = registry.oracle(result.oracle_id)
    if oracle is None or runner.oracle_id != oracle.oracle_id:
        raise reject(RejectCodeV1.ORACLE_UNREGISTERED, name)
    if result.source_pins_root != subject.source_pins_root:
        raise reject(RejectCodeV1.SOURCE_PINS_ROOT_MISMATCH, name)
    if result.subject_root != subject.subject_root:
        raise reject(RejectCodeV1.SUBJECT_MISMATCH, name)
    return runner, oracle.kind


def _verify_witness(
    result: ObligationResultV1,
    runner: RegisteredRunnerV1,
    artifacts: Mapping[str, OwnedSourceV1],
    name: str,
) -> None:
    witness = result.witness
    if witness.kind is WitnessKindV1.BAD_TRACE_WITNESS:
        if witness.artifact is None or witness.replay_sha256 is not None:
            raise reject(RejectCodeV1.ARTIFACT_UNBOUND, f"{name}: witness shape")
        if witness.artifact.path != runner.witness_artifact_path:
            raise reject(RejectCodeV1.ARTIFACT_UNBOUND, f"{name}: witness path not registered")
        bind_artifact(artifacts, witness.artifact.path, witness.artifact.sha256)
    elif witness.kind is WitnessKindV1.REPLAY_TRANSCRIPT:
        if (
            witness.artifact is not None
            or witness.replay_sha256 != result.observation.replay_sha256
        ):
            raise reject(RejectCodeV1.ARTIFACT_UNBOUND, f"{name}: replay hash")
    elif witness.artifact is not None or witness.replay_sha256 is not None:
        raise reject(RejectCodeV1.ARTIFACT_UNBOUND, f"{name}: witness shape")


def _verify_certificates(
    result: ObligationResultV1,
    predicate: BadPredicateV1,
    registry: RegistryV1,
    artifacts: Mapping[str, OwnedSourceV1],
    name: str,
) -> None:
    seen: set[str] = set()
    registered = {
        row.formal_obligation_id: row
        for row in registry.formal_obligations_for(predicate.bad_predicate_id)
    }
    for certificate in result.formal_certificates:
        if certificate.formal_obligation_id in seen:
            raise reject(RejectCodeV1.RESULT_DUPLICATE, f"{name}: certificate")
        seen.add(certificate.formal_obligation_id)
        obligation = registered.get(certificate.formal_obligation_id)
        if (
            obligation is None
            or obligation.certificate_kind is not certificate.kind
            or obligation.theorem_id != certificate.theorem_id
            or obligation.oracle_id != result.oracle_id
            or obligation.certificate_artifact_path != certificate.artifact.path
        ):
            raise reject(
                RejectCodeV1.FORMAL_OBLIGATION_UNREGISTERED,
                f"{name}: {certificate.formal_obligation_id}",
            )
        bind_artifact(artifacts, certificate.artifact.path, certificate.artifact.sha256)


def _verify_mutants_and_ceiling(
    result: ObligationResultV1, predicate: BadPredicateV1, registry: RegistryV1, name: str
) -> None:
    surfaces = tuple(item.surface for item in result.no_effect_observations)
    if surfaces != tuple(NoEffectSurfaceV1):
        raise reject(RejectCodeV1.NO_EFFECT_OBSERVATIONS_INCOMPLETE, name)
    required = tuple(sorted(registry.mutants_for(predicate.bad_predicate_id)))
    if result.required_mutant_ids != required:
        raise reject(RejectCodeV1.MUTANT_SET_MISMATCH, name)
    if result.killed_mutant_ids != tuple(sorted(result.killed_mutant_ids)) or any(
        mutant not in required for mutant in result.killed_mutant_ids
    ):
        raise reject(RejectCodeV1.MUTANT_UNREGISTERED, name)
    if result.vm_gate_effect != VM_GATE_EFFECT_V1 or result.contributes_to_vm_gates != ():
        raise reject(RejectCodeV1.VM_GATE_CLOSURE_FORBIDDEN, name)
    if result.claim_ceiling != CLAIM_CEILING_V1:
        raise reject(RejectCodeV1.CALLER_SUPPLIED_CEILING, name)


def verify_result(
    result: ObligationResultV1,
    *,
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    subject: ExactSubjectV1,
    artifacts: Mapping[str, OwnedSourceV1],
    replayed_observations: Mapping[str, ExecutionObservationV1],
) -> None:
    """Rebind every coordinate of a result row and recompute its verdict and status."""

    name = f"result {result.obligation_id}"
    row, predicate = _verify_identity(result, inventory, name)
    runner, oracle_kind = _verify_registrations(result, predicate, registry, subject, name)
    replayed = replayed_observations.get(runner.runner_id)
    if replayed is None or replayed != result.observation:
        raise reject(RejectCodeV1.RUNNER_OBSERVATION_MISMATCH, name)
    _verify_witness(result, runner, artifacts, name)
    _verify_certificates(result, predicate, registry, artifacts, name)
    _verify_mutants_and_ceiling(result, predicate, registry, name)
    expected_verdict = derive_oracle_verdict(
        oracle_kind,
        result.observation,
        witness_present=result.witness.kind is WitnessKindV1.BAD_TRACE_WITNESS,
        certificates_present=bool(result.formal_certificates),
    )
    if result.oracle_verdict is not expected_verdict:
        raise reject(RejectCodeV1.CALLER_PROMOTED_STATUS, f"{name}: oracle verdict")
    if result.oracle_report_sha256 != oracle_report_sha256(
        result.oracle_id, result.oracle_verdict, result.observation
    ):
        raise reject(RejectCodeV1.CALLER_PROMOTED_STATUS, f"{name}: oracle report hash")
    if result.computed_status is not compute_result_status(row, result, registry, subject):
        raise reject(RejectCodeV1.CALLER_PROMOTED_STATUS, name)


def expected_result_keys(
    inventory: ObligationInventoryV1, registry: RegistryV1
) -> tuple[tuple[str, str], ...]:
    keys: list[tuple[str, str]] = []
    for row in inventory.rows:
        if row.predicate is None:
            continue
        keys.extend(
            (row.obligation_id, runner.runner_id)
            for runner in registry.runners_for(row.predicate.bad_predicate_id)
        )
    return tuple(sorted(keys))


def verify_results(
    results: Sequence[ObligationResultV1],
    *,
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    subject: ExactSubjectV1,
    artifacts: Mapping[str, OwnedSourceV1],
    replayed_observations: Mapping[str, ExecutionObservationV1],
) -> None:
    observed = tuple((result.obligation_id, result.runner_id) for result in results)
    if len(set(observed)) != len(observed):
        raise reject(RejectCodeV1.RESULT_DUPLICATE, "results")
    if observed != tuple(sorted(observed)):
        raise reject(RejectCodeV1.RESULT_ORDER_INVALID, "results")
    expected = expected_result_keys(inventory, registry)
    unexpected = sorted(set(observed) - set(expected))
    if unexpected:
        raise reject(RejectCodeV1.RESULT_UNEXPECTED, f"{unexpected[0][0]}/{unexpected[0][1]}")
    missing = sorted(set(expected) - set(observed))
    if missing:
        raise reject(RejectCodeV1.RESULT_MISSING, f"{missing[0][0]}/{missing[0][1]}")
    for result in results:
        verify_result(
            result,
            inventory=inventory,
            registry=registry,
            subject=subject,
            artifacts=artifacts,
            replayed_observations=replayed_observations,
        )


def obligation_statuses(
    inventory: ObligationInventoryV1,
    registry: RegistryV1,
    results: Sequence[ObligationResultV1],
) -> dict[str, EvidenceStatusV1]:
    """Join per-result statuses; any bad trace dominates every other status."""

    by_obligation: dict[str, list[EvidenceStatusV1]] = {}
    for result in results:
        by_obligation.setdefault(result.obligation_id, []).append(result.computed_status)
    statuses: dict[str, EvidenceStatusV1] = {}
    for row in inventory.rows:
        if row.predicate is None:
            statuses[row.obligation_id] = EvidenceStatusV1.UNSPECIFIED_SEMANTICS
            continue
        observed = by_obligation.get(row.obligation_id, [])
        if not observed:
            has_runner = bool(registry.runners_for(row.predicate.bad_predicate_id))
            statuses[row.obligation_id] = (
                EvidenceStatusV1.SEARCH_PENDING
                if has_runner
                else EvidenceStatusV1.UNKNOWN_REACHABILITY
            )
        elif EvidenceStatusV1.WITNESSED_REACHABLE in observed:
            statuses[row.obligation_id] = EvidenceStatusV1.WITNESSED_REACHABLE
        else:
            statuses[row.obligation_id] = max(observed, key=lambda status: STATUS_RANK_V1[status])
    return statuses


def build_denominator_status_counts(statuses: Mapping[str, EvidenceStatusV1]) -> dict[str, int]:
    """Exact count vector over the closed status lattice; never a ratio."""

    counts = {status.value: 0 for status in EvidenceStatusV1}
    for status in statuses.values():
        counts[status.value] += 1
    return counts


# --------------------------------------------------------------------------
# Closed parsing of result rows
# --------------------------------------------------------------------------

_OBSERVATION_FIELDS = tuple(ExecutionObservationV1.__dataclass_fields__)
_WITNESS_FIELDS = ("kind", "artifact", "replay_sha256")
_CERTIFICATE_RESULT_FIELDS = (
    "kind",
    "formal_obligation_id",
    "theorem_id",
    "toolchain_manifest_root",
    "artifact",
)


def _parse_artifact(value: object, name: str) -> ArtifactRefV1:
    raw = require_closed_object(value, ("path", "sha256"), name)
    return ArtifactRefV1(
        validate_repo_path(raw["path"], f"{name}.path"),
        require_sha256(raw["sha256"], f"{name}.sha256"),
    )


def _parse_observation(value: object, name: str) -> ExecutionObservationV1:
    raw = require_closed_object(value, _OBSERVATION_FIELDS, name)
    returncode = raw["returncode"]
    return ExecutionObservationV1(
        runner_id=require_token(raw["runner_id"], f"{name}.runner_id"),
        argv_sha256=require_sha256(raw["argv_sha256"], f"{name}.argv_sha256"),
        returncode=None
        if returncode is None
        else require_int(returncode, f"{name}.returncode", low=-255, high=255),
        stdout_sha256=require_sha256(raw["stdout_sha256"], f"{name}.stdout_sha256"),
        stderr_sha256=require_sha256(raw["stderr_sha256"], f"{name}.stderr_sha256"),
        timed_out=require_bool(raw["timed_out"], f"{name}.timed_out"),
        output_limit_exceeded=require_bool(
            raw["output_limit_exceeded"], f"{name}.output_limit_exceeded"
        ),
    )


def _parse_witness(value: object, name: str) -> WitnessV1:
    raw = require_closed_object(value, _WITNESS_FIELDS, name)
    return WitnessV1(
        kind=cast(WitnessKindV1, require_enum(raw["kind"], WitnessKindV1, f"{name}.kind")),
        artifact=None
        if raw["artifact"] is None
        else _parse_artifact(raw["artifact"], f"{name}.artifact"),
        replay_sha256=None
        if raw["replay_sha256"] is None
        else require_sha256(raw["replay_sha256"], f"{name}.replay_sha256"),
    )


def _parse_cells(
    value: object, name: str
) -> tuple[tuple[LifecyclePhaseV1, InvariantFamilyV1], ...]:
    cells: list[tuple[LifecyclePhaseV1, InvariantFamilyV1]] = []
    for index, item in enumerate(require_list(value, name)):
        cell = require_closed_object(
            item, ("lifecycle_phase", "invariant_family"), f"{name}[{index}]"
        )
        cells.append(
            (
                cast(
                    LifecyclePhaseV1,
                    require_enum(
                        cell["lifecycle_phase"],
                        LifecyclePhaseV1,
                        f"{name}[{index}].lifecycle_phase",
                    ),
                ),
                cast(
                    InvariantFamilyV1,
                    require_enum(
                        cell["invariant_family"],
                        InvariantFamilyV1,
                        f"{name}[{index}].invariant_family",
                    ),
                ),
            )
        )
    return tuple(cells)


def _parse_no_effect(value: object, name: str) -> tuple[NoEffectObservationV1, ...]:
    observations: list[NoEffectObservationV1] = []
    for index, item in enumerate(require_list(value, name)):
        entry = require_closed_object(item, ("surface", "outcome"), f"{name}[{index}]")
        observations.append(
            NoEffectObservationV1(
                cast(
                    NoEffectSurfaceV1,
                    require_enum(entry["surface"], NoEffectSurfaceV1, f"{name}[{index}].surface"),
                ),
                cast(
                    NoEffectOutcomeV1,
                    require_enum(entry["outcome"], NoEffectOutcomeV1, f"{name}[{index}].outcome"),
                ),
            )
        )
    return tuple(observations)


def _parse_certificates(value: object, name: str) -> tuple[FormalCertificateV1, ...]:
    certificates: list[FormalCertificateV1] = []
    for index, item in enumerate(require_list(value, name)):
        cert_name = f"{name}[{index}]"
        cert = require_closed_object(item, _CERTIFICATE_RESULT_FIELDS, cert_name)
        certificates.append(
            FormalCertificateV1(
                kind=cast(
                    CertificateKindV1,
                    require_enum(cert["kind"], CertificateKindV1, f"{cert_name}.kind"),
                ),
                formal_obligation_id=require_token(
                    cert["formal_obligation_id"], f"{cert_name}.formal_obligation_id"
                ),
                theorem_id=require_token(cert["theorem_id"], f"{cert_name}.theorem_id"),
                toolchain_manifest_root=require_root(
                    cert["toolchain_manifest_root"], f"{cert_name}.toolchain_manifest_root"
                ),
                artifact=_parse_artifact(cert["artifact"], f"{cert_name}.artifact"),
            )
        )
    return tuple(certificates)


def parse_result(value: object, name: str) -> ObligationResultV1:
    raw = require_closed_object(value, RESULT_FIELDS_V1, name)
    obligation_id = require_string(raw["obligation_id"], f"{name}.obligation_id", max_chars=70)
    if (
        not obligation_id.startswith("WEDC1-")
        or len(obligation_id) != 70
        or any(char not in "0123456789abcdef" for char in obligation_id[6:])
    ):
        raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}.obligation_id")
    return ObligationResultV1(
        obligation_id=obligation_id,
        key=parse_obligation_key(raw["key"], f"{name}.key"),
        predicate_root=require_root(raw["predicate_root"], f"{name}.predicate_root"),
        schema_root=require_root(raw["schema_root"], f"{name}.schema_root"),
        bounds_profile_id=require_token(raw["bounds_profile_id"], f"{name}.bounds_profile_id"),
        bounds_root=require_root(raw["bounds_root"], f"{name}.bounds_root"),
        cells=_parse_cells(raw["cells"], f"{name}.cells"),
        runner_id=require_token(raw["runner_id"], f"{name}.runner_id"),
        oracle_id=require_token(raw["oracle_id"], f"{name}.oracle_id"),
        argv_sha256=require_sha256(raw["argv_sha256"], f"{name}.argv_sha256"),
        source_pins_root=require_root(raw["source_pins_root"], f"{name}.source_pins_root"),
        subject_root=require_root(raw["subject_root"], f"{name}.subject_root"),
        execution_premise=cast(
            ExecutionPremiseV1,
            require_enum(raw["execution_premise"], ExecutionPremiseV1, f"{name}.execution_premise"),
        ),
        observation=_parse_observation(raw["observation"], f"{name}.observation"),
        oracle_verdict=cast(
            OracleVerdictV1,
            require_enum(raw["oracle_verdict"], OracleVerdictV1, f"{name}.oracle_verdict"),
        ),
        oracle_report_sha256=require_sha256(
            raw["oracle_report_sha256"], f"{name}.oracle_report_sha256"
        ),
        witness=_parse_witness(raw["witness"], f"{name}.witness"),
        no_effect_observations=_parse_no_effect(
            raw["no_effect_observations"], f"{name}.no_effect_observations"
        ),
        required_mutant_ids=require_token_list(
            raw["required_mutant_ids"], f"{name}.required_mutant_ids", unique=True
        ),
        killed_mutant_ids=require_token_list(
            raw["killed_mutant_ids"], f"{name}.killed_mutant_ids", unique=True
        ),
        formal_certificates=_parse_certificates(
            raw["formal_certificates"], f"{name}.formal_certificates"
        ),
        vm_gate_effect=require_token(raw["vm_gate_effect"], f"{name}.vm_gate_effect"),
        contributes_to_vm_gates=require_token_list(
            raw["contributes_to_vm_gates"], f"{name}.contributes_to_vm_gates", unique=True
        ),
        computed_status=cast(
            EvidenceStatusV1,
            require_enum(raw["computed_status"], EvidenceStatusV1, f"{name}.computed_status"),
        ),
        claim_ceiling=require_token(raw["claim_ceiling"], f"{name}.claim_ceiling"),
    )
