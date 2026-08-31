"""Compare observations against the manifest and assemble the inventory report.

Field names deliberately say ``static_source`` rather than ``deployed``.  The
scan reaches statically resolvable edges from decoded launchers; it does not
establish runtime reachability or complete deployment coverage.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from tools.m6_value_sinks.deployment import DeploymentClosureV2, derive_python_deployment_closure
from tools.m6_value_sinks.launchers import ClosureFindingV2
from tools.m6_value_sinks.manifest import (
    SCHEMA_V2,
    ClosureGapV2,
    ValueSinkSpecV2,
    load_closure_gaps,
    load_value_sink_manifest,
)
from tools.m6_value_sinks.operations import combine_fingerprints
from tools.m6_value_sinks.scanner import ValueSinkObservationV2, scan_module

MANIFEST_NAME = "m6_value_sink_manifest_v2.json"

NONCLAIMS: tuple[str, ...] = (
    "this is a static-source inventory aid; it is never proof of sole-publisher closure",
    "the scan follows statically resolvable Python import and dispatch edges from decoded launchers only",
    "unresolved dynamic import, subprocess, shell, plugin, native, and generated dispatch are reported as closure gaps, not followed",
    "Rust, Tau, shell bodies, generated code, native extensions, and container wiring beyond entrypoint dispatch require separate cross-language inventories",
    "an observed operation may be unreachable at runtime, and an unobserved path may still write through an unmodelled mechanism",
    "classification and consumer tracing record research judgement; the manifest carries no release-backed authority",
    "a passing result does not establish complete mediation, durability, finality, or safe value movement",
    "VM-01 remains open; no gate here contributes production authority",
)


@dataclass(frozen=True, slots=True)
class SinkComparisonV2:
    findings: tuple[ClosureFindingV2, ...]
    observed_occurrences: int


def _observation_groups(
    observations: tuple[ValueSinkObservationV2, ...],
) -> dict[tuple[str, str, str], list[ValueSinkObservationV2]]:
    groups: dict[tuple[str, str, str], list[ValueSinkObservationV2]] = {}
    for observation in observations:
        groups.setdefault(observation.identity(), []).append(observation)
    return groups


def compare_inventory(
    specs: tuple[ValueSinkSpecV2, ...],
    observations: tuple[ValueSinkObservationV2, ...],
    scanned_modules: frozenset[str] = frozenset(),
) -> tuple[ClosureFindingV2, ...]:
    """Require one exact classification per observed durable-write identity."""

    findings: list[ClosureFindingV2] = []
    groups = _observation_groups(observations)
    specs_by_identity = {spec.identity(): spec for spec in specs}
    for identity, group in sorted(groups.items()):
        spec = specs_by_identity.get(identity)
        count = len(group)
        evidence = f"{identity[1]}:{identity[2]}:{count}"
        if spec is None:
            findings.append(ClosureFindingV2(identity[0], "unclassified_value_sink", evidence))
            continue
        if spec.occurrence_count != count:
            findings.append(
                ClosureFindingV2(
                    identity[0],
                    "value_sink_occurrence_mismatch",
                    f"{evidence}:expected={spec.occurrence_count}",
                )
            )
        fingerprint = combine_fingerprints(tuple(item.fingerprint for item in group))
        if spec.identity_fingerprint != fingerprint:
            findings.append(
                ClosureFindingV2(
                    identity[0],
                    "operation_fingerprint_mismatch",
                    f"{spec.sink_id}:observed={fingerprint}",
                )
            )
        if spec.deployed_reachable != (identity[0] in scanned_modules):
            findings.append(
                ClosureFindingV2(
                    identity[0],
                    "reachability_claim_mismatch",
                    f"{spec.sink_id}:declared={spec.deployed_reachable}",
                )
            )
    for identity, spec in sorted(specs_by_identity.items()):
        if identity not in groups:
            findings.append(
                ClosureFindingV2(
                    spec.path, "classified_value_sink_missing", f"{spec.symbol}:{spec.sink_kind}"
                )
            )
    return tuple(sorted(findings))


def reconcile_closure_gaps(
    observed: tuple[tuple[str, str], ...], declared: tuple[ClosureGapV2, ...]
) -> tuple[ClosureFindingV2, ...]:
    """Require the declared incompleteness set to equal the observed one."""

    declared_identities = {gap.identity() for gap in declared}
    observed_identities = set(observed)
    findings = [
        ClosureFindingV2(path, "undeclared_closure_gap", mechanism)
        for path, mechanism in sorted(observed_identities - declared_identities)
    ]
    findings.extend(
        ClosureFindingV2(path, "stale_closure_gap", mechanism)
        for path, mechanism in sorted(declared_identities - observed_identities)
    )
    return tuple(sorted(findings))


def scan_closure(root: Path, closure: DeploymentClosureV2) -> tuple[ValueSinkObservationV2, ...]:
    """Observe operations across the statically scanned module set."""

    import ast

    observations: list[ValueSinkObservationV2] = []
    for relative in closure.modules:
        path = root / relative
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except (OSError, UnicodeError, SyntaxError, ValueError) as exc:
            raise ValueError(f"cannot scan {relative}: {exc}") from exc
        observations.extend(scan_module(relative, tree))
    return tuple(sorted(observations))


def _load_manifest_parts(
    manifest_path: Path,
) -> tuple[tuple[ValueSinkSpecV2, ...], tuple[ClosureGapV2, ...], list[ClosureFindingV2]]:
    findings: list[ClosureFindingV2] = []
    relative_name = f"tools/{MANIFEST_NAME}"
    try:
        specs = load_value_sink_manifest(manifest_path)
    except ValueError as exc:
        specs = ()
        findings.append(ClosureFindingV2(relative_name, "manifest_invalid", str(exc)))
    try:
        gaps = load_closure_gaps(manifest_path)
    except ValueError as exc:
        gaps = ()
        findings.append(ClosureFindingV2(relative_name, "closure_gaps_invalid", str(exc)))
    return specs, gaps, findings


def build_report(root: Path) -> dict[str, object]:
    """Assemble the fail-closed inventory report for one repository root."""

    root = root.resolve()
    specs, declared_gaps, findings = _load_manifest_parts(root / "tools" / MANIFEST_NAME)
    closure = derive_python_deployment_closure(root)
    findings.extend(closure.findings)
    findings.extend(reconcile_closure_gaps(closure.observed_gaps, declared_gaps))
    try:
        observations = scan_closure(root, closure)
    except ValueError as exc:
        observations = ()
        findings.append(ClosureFindingV2("bin", "sink_scan_failed", str(exc)))
    findings.extend(compare_inventory(specs, observations, frozenset(closure.modules)))
    findings.sort()
    unmediated = sorted(
        spec.sink_id for spec in specs if spec.mediation_status == "UNMEDIATED_DEPLOYED_WRITER"
    )
    release_gaps = sorted(
        spec.sink_id
        for spec in specs
        if spec.mediation_status != "NON_VALUE_EFFECT" and spec.release_binding is None
    )
    return {
        "classified_identity_count": len(specs),
        "declared_closure_gaps": [gap.to_dict() for gap in declared_gaps],
        "decoded_launchers": [entrypoint.to_dict() for entrypoint in closure.entrypoints],
        "findings": [finding.to_dict() for finding in findings],
        "nonclaims": list(NONCLAIMS),
        "observed_occurrence_count": len(observations),
        "ok": not findings,
        "production_authority": False,
        "release_gaps": release_gaps,
        "release_ready": (
            bool(specs)
            and not findings
            and not release_gaps
            and not unmediated
            and not declared_gaps
        ),
        "schema": SCHEMA_V2,
        "sinks": [spec.to_dict() for spec in specs],
        "static_reachable_unscanned_modules": list(closure.unscanned_modules),
        "static_scanned_module_count": len(closure.modules),
        "static_scanned_module_digests": [
            {"path": path, "sha256": digest} for path, digest in closure.module_digests
        ],
        "unmediated_static_writers": unmediated,
        "vm01_status": "OPEN",
    }
