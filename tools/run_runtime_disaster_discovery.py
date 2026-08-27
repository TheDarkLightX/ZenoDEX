#!/usr/bin/env python3
"""Fixed-registry imperative shell for WholeEconomyDisasterCoverageV1.

The shell captures the subject commit and tree once, reads the committed
registry and every pinned path exactly once against that captured tree,
rechecks the commit/tree after the reads, executes only argv vectors the
registry declares, rechecks again after execution, and renders one discovery
packet.  Packets, receipts, and command-line inputs never supply argv, command
strings, repository paths, or execution authority.

JSON contract: stdout carries either the packet (``--json``) or a compact
summary; ``--out`` writes the packet file.  Exit 0 only when the packet was
built with integrity; a typed reject prints ``{"ok": false, "reject_code":
...}`` and exits 1 without writing anything.  ``--render-source-pins`` is the
recorded, read-only regeneration command for the registry's source pins.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.runtime_disaster_discovery import (  # noqa: E402
    REGISTRY_PATH_V1,
    REQUIRED_SOURCE_PATHS_V1,
    REQUIRED_SOURCE_PINS_V1,
    UNOBSERVED_NO_EFFECT_V1,
    ArtifactRefV1,
    BoundSourceV1,
    DiscoveryReject,
    ExactSubjectV1,
    ExecutionPremiseV1,
    FormalCertificateV1,
    HeadBindingV1,
    ObligationInventoryV1,
    ObligationResultV1,
    OwnedSourceV1,
    PacketV1,
    PathKindV1,
    RegistryV1,
    RejectCodeV1,
    SourceRoleV1,
    bind_sources,
    build_packet_core,
    build_result,
    compute_subject,
    derive_inventory,
    execution_premise,
    git_blob_oid,
    owned_source_matches_head_v1,
    parse_registry,
    sha256_hex,
)
from tools.runtime_disaster_discovery_ports_v1 import (  # noqa: E402
    OneReadCacheV1,
    ShellPortsV1,
    build_runner_execution_request_v1,
    capture_head,
    default_ports,
    require_same_head,
)


def _artifact_ref(cache: OneReadCacheV1, path: str | None) -> ArtifactRefV1 | None:
    if path is None:
        return None
    owned = cache.get(path)
    if owned.kind is not PathKindV1.REGULAR or owned.symlink_in_ancestry or owned.data is None:
        return None
    return ArtifactRefV1(path, sha256_hex(owned.data))


def _certificates(
    cache: OneReadCacheV1,
    registry: RegistryV1,
    bad_predicate_id: str,
    oracle_id: str,
    toolchain_manifest_root: str,
) -> tuple[FormalCertificateV1, ...]:
    certificates: list[FormalCertificateV1] = []
    for obligation in registry.formal_obligations_for(bad_predicate_id):
        if obligation.oracle_id != oracle_id:
            continue
        artifact = _artifact_ref(cache, obligation.certificate_artifact_path)
        if artifact is None:
            continue
        certificates.append(
            FormalCertificateV1(
                kind=obligation.certificate_kind,
                formal_obligation_id=obligation.formal_obligation_id,
                theorem_id=obligation.theorem_id,
                toolchain_manifest_root=toolchain_manifest_root,
                artifact=artifact,
            )
        )
    return tuple(certificates)


def _execute_results(
    ports: ShellPortsV1,
    cache: OneReadCacheV1,
    registry: RegistryV1,
    inventory: ObligationInventoryV1,
    subject: ExactSubjectV1,
    premise: ExecutionPremiseV1,
    bound: Mapping[str, BoundSourceV1],
    source_tree: dict[str, bytes],
) -> tuple[ObligationResultV1, ...]:
    results: list[ObligationResultV1] = []
    for row in inventory.rows:
        if row.predicate is None:
            continue
        for runner in registry.runners_for(row.predicate.bad_predicate_id):
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
            observation = ports.execute(build_runner_execution_request_v1(runner, source_tree))
            results.append(
                build_result(
                    row=row,
                    runner=runner,
                    registry=registry,
                    subject=subject,
                    premise=premise,
                    observation=observation,
                    witness_artifact=_artifact_ref(cache, runner.witness_artifact_path),
                    certificates=_certificates(
                        cache,
                        registry,
                        row.predicate.bad_predicate_id,
                        runner.oracle_id,
                        subject.toolchain_manifest_root,
                    ),
                    no_effect_observations=UNOBSERVED_NO_EFFECT_V1,
                    killed_mutant_ids=(),
                )
            )
    return tuple(results)


def _read_registry(cache: OneReadCacheV1) -> tuple[RegistryV1, OwnedSourceV1]:
    owned = cache.get(REGISTRY_PATH_V1)
    if owned.data is None or owned.kind is not PathKindV1.REGULAR:
        raise DiscoveryReject(RejectCodeV1.SOURCE_UNREADABLE, REGISTRY_PATH_V1)
    return parse_registry(owned.data), owned


def run_discovery(ports: ShellPortsV1) -> PacketV1:
    """Capture, read once, bind, derive, execute registered runners, recheck, render."""

    started = time.monotonic()
    ports.race_boundary("before_capture")
    head = capture_head(ports)
    cache = OneReadCacheV1(ports, head.tree)
    ports.race_boundary("before_read")
    registry, registry_owned = _read_registry(cache)
    owned = {path: cache.get(path) for path in REQUIRED_SOURCE_PATHS_V1}
    artifact_paths = sorted(
        {
            decision.certificate.artifact_path
            for decision in registry.applicability_decisions
            if decision.certificate is not None
        }
    )
    artifacts = {path: cache.get(path) for path in artifact_paths}
    ports.race_boundary("after_read")
    require_same_head(ports, head, "after_read")
    bound: Mapping[str, BoundSourceV1] = {
        source.pin.path: source for source in bind_sources(registry.source_pins, owned)
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
    premise = execution_premise(
        head.worktree_clean,
        bound,
        registry_head_bound=owned_source_matches_head_v1(registry_owned),
    )
    registry_data = registry_owned.data
    if registry_data is None:
        raise DiscoveryReject(RejectCodeV1.SOURCE_UNREADABLE, REGISTRY_PATH_V1)
    source_tree = {path: source.data for path, source in bound.items()}
    source_tree[REGISTRY_PATH_V1] = registry_data
    results = _execute_results(
        ports,
        cache,
        registry,
        inventory,
        subject,
        premise,
        bound,
        source_tree,
    )
    ports.race_boundary("after_execute")
    require_same_head(ports, head, "after_execute")
    core = build_packet_core(
        subject=subject,
        premise=premise,
        bound=bound,
        inventory=inventory,
        registry=registry,
        results=results,
    )
    telemetry: dict[str, object] = {
        "generated_at": ports.now_utc_iso(),
        "duration_ms": int((time.monotonic() - started) * 1000),
        "python_version": ports.python_version,
        "stdout_previews": [],
    }
    return PacketV1(core=core, receipt_root=core.receipt_root, telemetry=telemetry)


def render_source_pins(ports: ShellPortsV1) -> list[dict[str, object]]:
    """Recorded read-only regeneration command for the registry's source pins."""

    head = capture_head(ports)
    cache = OneReadCacheV1(ports, head.tree)
    pins: list[dict[str, object]] = []
    for path, role in REQUIRED_SOURCE_PINS_V1:
        owned = cache.get(path)
        if owned.data is None:
            raise DiscoveryReject(RejectCodeV1.SOURCE_UNREADABLE, path)
        mode = owned.head_entry.git_mode if owned.head_entry is not None else "100644"
        pins.append(
            {
                "path": path,
                "role": role.value,
                "git_mode": mode,
                "blob_oid": git_blob_oid(owned.data),
                "sha256": sha256_hex(owned.data),
                "byte_size": len(owned.data),
            }
        )
    require_same_head(ports, head, "after_render")
    return pins


def summarize_packet(packet: PacketV1) -> dict[str, object]:
    core = packet.core
    return {
        "schema": "zenodex/whole-economy-disaster-discovery-summary/v1",
        "ok": True,
        "receipt_root": packet.receipt_root,
        "subject_commit": core.subject.commit,
        "subject_tree": core.subject.tree,
        "execution_premise": core.execution_premise.value,
        "denominator_state": core.denominator.state.value,
        "applicability_cells": core.denominator.applicability_cells,
        "classification_counts": dict(core.denominator.classification_counts),
        "obligation_rows": core.denominator.obligation_rows,
        "inventory_entry_counts": dict(core.denominator.inventory_entry_counts),
        "result_count": len(core.results),
        "flags": core.flags.to_canonical(),
        "claim_ceiling": core.claim_ceiling,
        "coverage_ratio": core.denominator.coverage_ratio,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="print the full packet instead of the summary"
    )
    parser.add_argument("--out", type=Path, help="write the packet JSON to this path")
    parser.add_argument(
        "--render-source-pins",
        action="store_true",
        help="print current source pins for manual registry regeneration (read-only)",
    )
    args = parser.parse_args(argv)
    ports = default_ports(REPO_ROOT)
    try:
        if args.render_source_pins:
            print(json.dumps(render_source_pins(ports), indent=2, sort_keys=True))
            return 0
        packet = run_discovery(ports)
    except DiscoveryReject as exc:
        print(
            json.dumps(
                {"ok": False, "reject_code": exc.code.value, "detail": exc.detail}, sort_keys=True
            )
        )
        return 1
    rendered = json.dumps(packet.to_canonical(), indent=2, sort_keys=True)
    if args.out is not None:
        args.out.write_text(rendered + "\n", encoding="utf-8")
    print(rendered if args.json else json.dumps(summarize_packet(packet), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
