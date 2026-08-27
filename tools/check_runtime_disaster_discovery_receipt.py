#!/usr/bin/env python3
"""Independent deterministic verifier for WholeEconomyDisasterCoverageV1 packets.

The verifier never trusts a packet's counts, floors, roots, statuses, or
flags.  It captures the subject commit and tree once, reads the committed
registry and every pinned source exactly once against that captured tree
object, rechecks the commit/tree after the reads, re-derives the applicability
grid and the source universes, recomputes the exact subject, rebinds every
result row to registered predicates, runners, oracles, bounds, mutants, formal
obligations, and committed artifacts, recomputes each evidence status, and
finally requires byte-exact equality of the canonical core and its
domain-separated receipt root.

Legacy stateful-bridge receipts are historical telemetry and are rejected with
``LEGACY_BRIDGE_RECEIPT_REJECTED``.  Exit-zero or test-looking output can never
verify above NOT_WITNESSED_IN_TESTS.

JSON contract: prints one report object; exit 0 only when ``ok`` is true.
A green result establishes denominator and evidence-association integrity for
the exact subject and nothing more.
"""

from __future__ import annotations

import argparse
import errno
import json
import os
import sys
from pathlib import Path
from typing import Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.runtime_disaster_discovery import (  # noqa: E402
    MAX_PACKET_BYTES_V1,
    RECEIPT_CHECK_SCHEMA_V1,
    REGISTRY_PATH_V1,
    REQUIRED_SOURCE_PATHS_V1,
    BoundSourceV1,
    DiscoveryReject,
    ExecutionObservationV1,
    HeadBindingV1,
    ObligationInventoryV1,
    PacketCoreV1,
    PacketV1,
    PathKindV1,
    RegistryV1,
    RejectCodeV1,
    SourceRoleV1,
    bind_sources,
    compute_subject,
    derive_inventory,
    execution_premise,
    expected_result_keys,
    owned_source_matches_head_v1,
    parse_packet,
    parse_registry,
    verify_packet,
)
from tools.runtime_disaster_discovery_ports_v1 import (  # noqa: E402
    OneReadCacheV1,
    ShellPortsV1,
    build_runner_execution_request_v1,
    capture_head,
    default_ports,
    read_descriptor_bounded,
    require_same_head,
)


def read_receipt_bounded(path: Path) -> bytes:
    """Open the operator-supplied receipt without following symlinks and cap it before reading."""

    try:
        descriptor = os.open(str(path), os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise DiscoveryReject(RejectCodeV1.PATH_SYMLINK, "receipt") from exc
        raise DiscoveryReject(
            RejectCodeV1.SOURCE_UNREADABLE, f"receipt: {type(exc).__name__}"
        ) from exc
    try:
        read = read_descriptor_bounded(descriptor, MAX_PACKET_BYTES_V1)
    except OSError as exc:
        raise DiscoveryReject(
            RejectCodeV1.SOURCE_UNREADABLE, f"receipt: {type(exc).__name__}"
        ) from exc
    finally:
        os.close(descriptor)
    if read.kind is PathKindV1.OVERSIZE:
        raise DiscoveryReject(RejectCodeV1.JSON_TOO_LARGE, "receipt")
    if read.kind is not PathKindV1.REGULAR or read.data is None:
        raise DiscoveryReject(RejectCodeV1.PATH_NOT_REGULAR_FILE, f"receipt: {read.kind.value}")
    return read.data


def _referenced_artifact_paths(packet: PacketV1) -> set[str]:
    paths: set[str] = set()
    for result in packet.core.results:
        if result.witness.artifact is not None:
            paths.add(result.witness.artifact.path)
        for certificate in result.formal_certificates:
            paths.add(certificate.artifact.path)
    return paths


def _report(packet: PacketV1, verified: PacketCoreV1) -> dict[str, object]:
    return {
        "schema": RECEIPT_CHECK_SCHEMA_V1,
        "ok": True,
        "reject_code": None,
        "detail": "",
        "receipt_root": packet.receipt_root,
        "subject_commit": verified.subject.commit,
        "subject_tree": verified.subject.tree,
        "subject_root": verified.subject.subject_root,
        "execution_premise": verified.execution_premise.value,
        "denominator_state": verified.denominator.state.value,
        "applicability_cells": verified.denominator.applicability_cells,
        "classification_counts": dict(verified.denominator.classification_counts),
        "obligation_rows": verified.denominator.obligation_rows,
        "evidence_status_counts": dict(verified.denominator.evidence_status_counts),
        "inventory_entry_counts": dict(verified.denominator.inventory_entry_counts),
        "result_count": len(verified.results),
        "flags": verified.flags.to_canonical(),
        "claim_ceiling": verified.claim_ceiling,
        "coverage_ratio": verified.denominator.coverage_ratio,
        "production_authority": "NONE",
        "findings": [],
    }


def _replay_runner_observations(
    packet: PacketV1,
    ports: ShellPortsV1,
    registry: RegistryV1,
    inventory: ObligationInventoryV1,
    bound: Mapping[str, BoundSourceV1],
    source_tree: dict[str, bytes],
) -> dict[str, ExecutionObservationV1]:
    """Re-execute every referenced registered runner from verifier-owned bytes."""

    expected = set(expected_result_keys(inventory, registry))
    observed = {(result.obligation_id, result.runner_id) for result in packet.core.results}
    unexpected = sorted(observed - expected)
    if unexpected:
        raise DiscoveryReject(
            RejectCodeV1.RESULT_UNEXPECTED,
            f"{unexpected[0][0]}/{unexpected[0][1]}",
        )
    replayed: dict[str, ExecutionObservationV1] = {}
    for runner_id in sorted({result.runner_id for result in packet.core.results}):
        runner = registry.runner(runner_id)
        if runner is None:
            raise DiscoveryReject(RejectCodeV1.RUNNER_UNREGISTERED, runner_id)
        runner_source = bound.get(runner.argv[1])
        if (
            runner_source is None
            or runner_source.pin.role is not SourceRoleV1.CHECKER_SOURCE
            or runner_source.head_binding is not HeadBindingV1.HEAD_BLOB_MATCH
        ):
            raise DiscoveryReject(
                RejectCodeV1.RUNNER_SOURCE_UNBOUND,
                f"runner {runner.runner_id}: {runner.argv[1]}",
            )
        replayed[runner_id] = ports.execute(build_runner_execution_request_v1(runner, source_tree))
    return replayed


def verify_receipt_bytes(receipt: bytes, ports: ShellPortsV1) -> dict[str, object]:
    """Verify one packet against independently re-read sources; raise on any drift."""

    if len(receipt) > MAX_PACKET_BYTES_V1:
        raise DiscoveryReject(RejectCodeV1.JSON_TOO_LARGE, "receipt")
    packet = parse_packet(receipt)
    head = capture_head(ports)
    cache = OneReadCacheV1(ports, head.tree)
    registry_owned = cache.get(REGISTRY_PATH_V1)
    if registry_owned.data is None or registry_owned.kind is not PathKindV1.REGULAR:
        raise DiscoveryReject(RejectCodeV1.SOURCE_UNREADABLE, REGISTRY_PATH_V1)
    registry = parse_registry(registry_owned.data)
    sources = {path: cache.get(path) for path in REQUIRED_SOURCE_PATHS_V1}
    artifact_paths = _referenced_artifact_paths(packet) | {
        decision.certificate.artifact_path
        for decision in registry.applicability_decisions
        if decision.certificate is not None
    }
    artifacts = {path: cache.get(path) for path in sorted(artifact_paths)}
    ports.race_boundary("after_read")
    require_same_head(ports, head, "after_read")
    bound: Mapping[str, BoundSourceV1] = {
        source.pin.path: source for source in bind_sources(registry.source_pins, sources)
    }
    inventory = derive_inventory(
        registry, bound, subject_commit=head.commit, subject_tree=head.tree, artifacts=artifacts
    )
    subject = compute_subject(
        commit=head.commit,
        tree=head.tree,
        registry=registry,
        bound=bound,
        m6_manifest_root=inventory.manifest.manifest_root,
    )
    expected_premise = execution_premise(
        head.worktree_clean,
        bound,
        registry_head_bound=owned_source_matches_head_v1(registry_owned),
    )
    registry_data = registry_owned.data
    if registry_data is None:
        raise DiscoveryReject(RejectCodeV1.SOURCE_UNREADABLE, REGISTRY_PATH_V1)
    source_tree = {path: source.data for path, source in bound.items()}
    source_tree[REGISTRY_PATH_V1] = registry_data
    replayed = _replay_runner_observations(
        packet,
        ports,
        registry,
        inventory,
        bound,
        source_tree,
    )
    ports.race_boundary("after_execute")
    require_same_head(ports, head, "after_execute")
    core = verify_packet(
        packet,
        subject=subject,
        bound=bound,
        inventory=inventory,
        registry=registry,
        artifacts=artifacts,
        expected_premise=expected_premise,
        replayed_observations=replayed,
    )
    return _report(packet, core)


def reject_report(exc: DiscoveryReject) -> dict[str, object]:
    return {
        "schema": RECEIPT_CHECK_SCHEMA_V1,
        "ok": False,
        "reject_code": exc.code.value,
        "detail": exc.detail,
        "production_authority": "NONE",
        "findings": [f"{exc.code.value}: {exc.detail}"],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--receipt", type=Path, required=True, help="packet JSON produced by the runner shell"
    )
    args = parser.parse_args(argv)
    try:
        report = verify_receipt_bytes(read_receipt_bounded(args.receipt), default_ports(REPO_ROOT))
    except DiscoveryReject as exc:
        report = reject_report(exc)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
